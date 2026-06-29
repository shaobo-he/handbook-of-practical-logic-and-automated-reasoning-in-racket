#lang racket/base

;; cooper --- Cooper's algorithm for Presburger arithmetic.
;;
;; Numerals are nullary function terms whose symbol is the number's text,
;; e.g. (fn |3|). Racket's exact integers provide the arbitrary-precision arithmetic.
;; Linear terms are kept canonical: c1*x1 + ... + cn*xn + k, encoded as
;; (fn + (fn * c x) rest) ending in the constant k.

(require racket/match)
(require (only-in racket/list range))
(require (only-in "../core/lib.rkt" earlier union can))
(require (only-in "../core/formulas.rkt" list-disj onatoms))
(require (only-in "../fol/skolem.rkt" simplify))
(require (only-in "qelim.rkt" lift-qelim cnnf))

(provide (all-defined-out))

;; ===== numerals =====
(define (mk-numeral n)
  `(fn ,(string->symbol (number->string n))))
(define (dest-numeral t)
  (match t
    [`(fn ,ns) (or (string->number (symbol->string ns)) (error 'dest-numeral "dest_numeral"))]
    [_ (error 'dest-numeral "dest_numeral")]))
(define (is-numeral t)
  (can dest-numeral t))
(define (numeral1 fn n)
  (mk-numeral (fn (dest-numeral n))))
(define (numeral2 fn m n)
  (mk-numeral (fn (dest-numeral m) (dest-numeral n))))

(define zero (mk-numeral 0))
(define one (mk-numeral 1))

;; ===== canonical linear-term arithmetic =====
;; A canonical linear term is c1*x1 + ... + cn*xn + k with the variables in
;; `vars` order and every coefficient ci a nonzero numeral. linear-cmul,
;; linear-add, etc. all preserve this normal form, which is what lets the
;; quantifier-elimination steps below pattern-match on (fn * coeff x) directly.
(define (linear-cmul n tm)
  (if (= n 0)
      zero
      (match tm
        [`(fn + (fn * ,c ,x) ,r) `(fn + (fn * ,(numeral1 (λ (z) (* n z)) c) ,x) ,(linear-cmul n r))]
        [k (numeral1 (λ (z) (* n z)) k)])))

(define (linear-add vars tm1 tm2)
  (match* (tm1 tm2)
    [(`(fn + (fn * ,c1 (var ,x1)) ,r1) `(fn + (fn * ,c2 (var ,x2)) ,r2))
     (cond
       [(equal? x1 x2)
        (define c (numeral2 + c1 c2))
        (if (equal? c zero)
            (linear-add vars r1 r2)
            `(fn + (fn * ,c (var ,x1)) ,(linear-add vars r1 r2)))]
       [(earlier vars x1 x2) `(fn + (fn * ,c1 (var ,x1)) ,(linear-add vars r1 tm2))]
       [else `(fn + (fn * ,c2 (var ,x2)) ,(linear-add vars tm1 r2))])]
    [(`(fn + (fn * ,c1 (var ,x1)) ,r1) k2) `(fn + (fn * ,c1 (var ,x1)) ,(linear-add vars r1 k2))]
    [(k1 `(fn + (fn * ,c2 (var ,x2)) ,r2)) `(fn + (fn * ,c2 (var ,x2)) ,(linear-add vars k1 r2))]
    [(_ _) (numeral2 + tm1 tm2)]))

(define (linear-neg tm)
  (linear-cmul -1 tm))
(define (linear-sub vars tm1 tm2)
  (linear-add vars tm1 (linear-neg tm2)))
(define (linear-mul tm1 tm2)
  (cond
    [(is-numeral tm1) (linear-cmul (dest-numeral tm1) tm2)]
    [(is-numeral tm2) (linear-cmul (dest-numeral tm2) tm1)]
    [else (error 'linear-mul "nonlinearity")]))

(define (lint vars tm)
  (match tm
    [`(var ,_) `(fn + (fn * ,one ,tm) ,zero)]
    [`(fn - ,t) (linear-neg (lint vars t))]
    [`(fn + ,s ,t) (linear-add vars (lint vars s) (lint vars t))]
    [`(fn - ,s ,t) (linear-sub vars (lint vars s) (lint vars t))]
    [`(fn * ,s ,t) (linear-mul (lint vars s) (lint vars t))]
    [_
     (if (is-numeral tm)
         tm
         (error 'lint "unknown term"))]))

;; ===== linearize atoms; drop non-strict inequalities =====
(define (mkatom vars p t)
  `(atom (rel ,p ,zero ,(lint vars t))))

(define (linform vars fm)
  (match fm
    [`(atom (rel divides ,c ,t)) `(atom (rel divides ,(numeral1 abs c) ,(lint vars t)))]
    [`(atom (rel = ,s ,t)) (mkatom vars '= `(fn - ,t ,s))]
    [`(atom (rel < ,s ,t)) (mkatom vars '< `(fn - ,t ,s))]
    [`(atom (rel > ,s ,t)) (mkatom vars '< `(fn - ,s ,t))]
    [`(atom (rel <= ,s ,t)) (mkatom vars '< `(fn - (fn + ,t ,one) ,s))]
    [`(atom (rel >= ,s ,t)) (mkatom vars '< `(fn - (fn + ,s ,one) ,t))]
    [_ fm]))

(define (posineq fm)
  (match fm
    [`(not (atom (rel < (fn |0|) ,t))) `(atom (rel < ,zero ,(linear-sub '() one t)))]
    [_ fm]))

;; ===== make the coefficient of x equal to 1 =====
(define (formlcm x fm)
  (match fm
    [`(atom (rel ,p ,_ (fn + (fn * ,c ,y) ,z)))
     #:when (equal? y x)
     (abs (dest-numeral c))]
    [`(not ,p) (formlcm x p)]
    [`(and ,p ,q) (lcm (formlcm x p) (formlcm x q))]
    [`(or ,p ,q) (lcm (formlcm x p) (formlcm x q))]
    [_ 1]))

(define (adjustcoeff x l fm)
  (match fm
    [`(atom (rel ,p ,d (fn + (fn * ,c ,y) ,z)))
     #:when (equal? y x)
     (define m (quotient l (dest-numeral c)))
     (define n
       (if (equal? p '<)
           (abs m)
           m))
     (define xtm `(fn * ,(mk-numeral (quotient m n)) ,x))
     `(atom (rel ,p ,(linear-cmul (abs m) d) (fn + ,xtm ,(linear-cmul n z))))]
    [`(not ,p) `(not ,(adjustcoeff x l p))]
    [`(and ,p ,q) `(and ,(adjustcoeff x l p) ,(adjustcoeff x l q))]
    [`(or ,p ,q) `(or ,(adjustcoeff x l p) ,(adjustcoeff x l q))]
    [_ fm]))

(define (unitycoeff x fm)
  (define l (formlcm x fm))
  (define fm* (adjustcoeff x l fm))
  (if (= l 1)
      fm*
      (let ([xp `(fn + (fn * ,one ,x) ,zero)])
        `(and (atom (rel divides ,(mk-numeral l) ,xp)) ,(adjustcoeff x l fm)))))

;; ===== minus-infinity formula and divisor LCM =====
;; minusinf replaces each atom by its truth value as x -> -infinity (the unity
;; coefficient of x is +/-1 here). An equality 0 = x + a is eventually false, and
;; 0 < x + a is eventually false while 0 < -x + a is eventually true; divisibility
;; atoms are periodic so they are left unchanged.
(define (minusinf x fm)
  (match fm
    [`(atom (rel = (fn |0|) (fn + (fn * (fn |1|) ,y) ,a)))
     #:when (equal? y x)
     #f]
    [`(atom (rel < (fn |0|) (fn + (fn * ,pm1 ,y) ,a)))
     #:when (equal? y x)
     (if (equal? pm1 one) #f #t)]
    [`(not ,p) `(not ,(minusinf x p))]
    [`(and ,p ,q) `(and ,(minusinf x p) ,(minusinf x q))]
    [`(or ,p ,q) `(or ,(minusinf x p) ,(minusinf x q))]
    [_ fm]))

(define (divlcm x fm)
  (match fm
    [`(atom (rel divides ,d (fn + (fn * ,c ,y) ,a)))
     #:when (equal? y x)
     (dest-numeral d)]
    [`(not ,p) (divlcm x p)]
    [`(and ,p ,q) (lcm (divlcm x p) (divlcm x q))]
    [`(or ,p ,q) (lcm (divlcm x p) (divlcm x q))]
    [_ 1]))

;; ===== B-set and linear replacement =====
;; The B-set collects the witness points just below which an atom can change
;; truth value (extracted from x = a, ~(x = a) and 0 < x + a literals). Cooper's
;; theorem says a solution, if any, is found either at -infinity or at b + j for
;; some b in the B-set and small offset j.
(define (bset x fm)
  (match fm
    [`(not (atom (rel = (fn |0|) (fn + (fn * (fn |1|) ,y) ,a))))
     #:when (equal? y x)
     (list (linear-neg a))]
    [`(atom (rel = (fn |0|) (fn + (fn * (fn |1|) ,y) ,a)))
     #:when (equal? y x)
     (list (linear-neg (linear-add '() a one)))]
    [`(atom (rel < (fn |0|) (fn + (fn * (fn |1|) ,y) ,a)))
     #:when (equal? y x)
     (list (linear-neg a))]
    [`(not ,p) (bset x p)]
    [`(and ,p ,q) (union (bset x p) (bset x q))]
    [`(or ,p ,q) (union (bset x p) (bset x q))]
    [_ '()]))

(define (linrep vars x t fm)
  (match fm
    [`(atom (rel ,p ,d (fn + (fn * ,c ,y) ,a)))
     #:when (equal? y x)
     (define ct (linear-cmul (dest-numeral c) t))
     `(atom (rel ,p ,d ,(linear-add vars ct a)))]
    [`(not ,p) `(not ,(linrep vars x t p))]
    [`(and ,p ,q) `(and ,(linrep vars x t p) ,(linrep vars x t q))]
    [`(or ,p ,q) `(or ,(linrep vars x t p) ,(linrep vars x t q))]
    [_ fm]))

;; ===== core elimination =====
;; (exists x . p) becomes a finite disjunction. p-inf is the formula valid as
;; x -> -infinity; bs is the B-set of candidate witnesses; js ranges over one
;; full period 1..lcm-of-divisors. stage j ORs the -infinity branch (shifted by j)
;; with the b+j branch for each b in bs, and the answer is the OR over all j.
(define (cooper vars fm)
  (match fm
    [`(exists ,x0 ,p0)
     (define x `(var ,x0))
     (define p (unitycoeff x p0))
     (define p-inf (simplify (minusinf x p)))
     (define bs (bset x p))
     (define js (range 1 (add1 (divlcm x p))))
     (define (p-element j b)
       (linrep vars x (linear-add vars b (mk-numeral j)) p))
     (define (stage j)
       (list-disj (cons (linrep vars x (mk-numeral j) p-inf) (map (λ (b) (p-element j b)) bs))))
     (list-disj (map stage js))]
    [_ (error 'cooper "not an existential formula")]))

;; ===== evaluate constant atoms =====
(define operations
  (list (cons '= =)
        (cons '< <)
        (cons '> >)
        (cons '<= <=)
        (cons '>= >=)
        (cons 'divides (λ (x y) (= (modulo y x) 0)))))

(define (evalc fm)
  (onatoms (λ (at)
             (with-handlers ([exn:fail? (λ (e) `(atom ,at))])
               (match at
                 [`(rel ,p ,s ,t)
                  (define op (cdr (assoc p operations)))
                  (if (op (dest-numeral s) (dest-numeral t)) #t #f)])))
           fm))

;; ===== overall procedures =====
(define integer-qelim
  (λ (fm)
    (simplify (evalc ((lift-qelim linform
                                  (λ (g) ((cnnf posineq) (evalc g)))
                                  (λ (vars) (λ (f) (cooper vars f))))
                      fm)))))

(define (relativize r fm)
  (match fm
    [`(not ,p) `(not ,(relativize r p))]
    [`(and ,p ,q) `(and ,(relativize r p) ,(relativize r q))]
    [`(or ,p ,q) `(or ,(relativize r p) ,(relativize r q))]
    [`(imp ,p ,q) `(imp ,(relativize r p) ,(relativize r q))]
    [`(iff ,p ,q) `(iff ,(relativize r p) ,(relativize r q))]
    [`(forall ,x ,p) `(forall ,x (imp ,(r x) ,(relativize r p)))]
    [`(exists ,x ,p) `(exists ,x (and ,(r x) ,(relativize r p)))]
    [_ fm]))

(define (natural-qelim fm)
  (integer-qelim (relativize (λ (x) `(atom (rel <= ,zero (var ,x)))) fm)))
