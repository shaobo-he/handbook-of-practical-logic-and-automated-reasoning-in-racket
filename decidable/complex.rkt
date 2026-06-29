#lang racket/base

;; complex --- quantifier elimination for algebraically closed fields
;; (Tarski-style, via pseudo-division and sign management).
;;
;; Canonical polynomials are nested in the head variable:
;;   (fn + c (fn * (var x) p))   meaning  c + x*p
;; with c, p polynomials in the later variables, bottoming out at numerals.

(require racket/match)
(require (only-in racket/list partition last))
(require (only-in "../core/lib.rkt" earlier funpow subtract can non))
(require (only-in "../core/formulas.rkt" conjuncts list-conj mk-or end-itlist))
(require (only-in "../prop/prop.rkt" dnf negate negative))
(require (only-in "../fol/skolem.rkt" simplify))
(require (only-in "qelim.rkt" lift-qelim cnnf))
(require (only-in "cooper.rkt" zero one mk-numeral dest-numeral is-numeral numeral1 numeral2 evalc))
(require (only-in "../equality/equal.rkt" mk-eq lhs))

(provide (all-defined-out))

;; ===== canonical polynomial arithmetic =====
(define (poly-add vars pol1 pol2)
  (match* (pol1 pol2)
    [(`(fn + ,c (fn * (var ,x) ,p)) `(fn + ,d (fn * (var ,y) ,q)))
     (cond
       [(earlier vars x y) (poly-ladd vars pol2 pol1)]
       [(earlier vars y x) (poly-ladd vars pol1 pol2)]
       [else
        (define e (poly-add vars c d))
        (define r (poly-add vars p q))
        (if (equal? r zero)
            e
            `(fn + ,e (fn * (var ,x) ,r)))])]
    [(_ `(fn + ,_ ,_)) (poly-ladd vars pol1 pol2)]
    [(`(fn + ,_ ,_) _) (poly-ladd vars pol2 pol1)]
    [(_ _) (numeral2 + pol1 pol2)]))

(define (poly-ladd vars pol1 pol2)
  (match pol2
    [`(fn + ,d (fn * (var ,y) ,q)) `(fn + ,(poly-add vars pol1 d) (fn * (var ,y) ,q))]))

(define (poly-neg p)
  (match p
    [`(fn + ,c (fn * (var ,x) ,pp)) `(fn + ,(poly-neg c) (fn * (var ,x) ,(poly-neg pp)))]
    [n (numeral1 - n)]))

(define (poly-sub vars p q)
  (poly-add vars p (poly-neg q)))

(define (poly-mul vars pol1 pol2)
  (match* (pol1 pol2)
    [(`(fn + ,c (fn * (var ,x) ,p)) `(fn + ,d (fn * (var ,y) ,q)))
     (if (earlier vars x y)
         (poly-lmul vars pol2 pol1)
         (poly-lmul vars pol1 pol2))]
    [(`(fn |0|) _) zero]
    [(_ `(fn |0|)) zero]
    [(_ `(fn + ,_ ,_)) (poly-lmul vars pol1 pol2)]
    [(`(fn + ,_ ,_) _) (poly-lmul vars pol2 pol1)]
    [(_ _) (numeral2 * pol1 pol2)]))

(define (poly-lmul vars pol1 pol2)
  (match pol2
    [`(fn + ,d (fn * (var ,y) ,q))
     (poly-add vars (poly-mul vars pol1 d) `(fn + ,zero (fn * (var ,y) ,(poly-mul vars pol1 q))))]))

(define (poly-pow vars p n)
  (funpow n (λ (z) (poly-mul vars p z)) one))
(define (poly-div vars p q)
  (poly-mul vars p (numeral1 (λ (m) (/ 1 m)) q)))
(define (poly-var x)
  `(fn + ,zero (fn * (var ,x) ,one)))

;; ===== term -> canonical polynomial =====
(define (polynate vars tm)
  (match tm
    [`(var ,x) (poly-var x)]
    [`(fn - ,t) (poly-neg (polynate vars t))]
    [`(fn + ,s ,t) (poly-add vars (polynate vars s) (polynate vars t))]
    [`(fn - ,s ,t) (poly-sub vars (polynate vars s) (polynate vars t))]
    [`(fn * ,s ,t) (poly-mul vars (polynate vars s) (polynate vars t))]
    [`(fn / ,s ,t) (poly-div vars (polynate vars s) (polynate vars t))]
    [`(fn ^ ,p (fn ,n)) (poly-pow vars (polynate vars p) (string->number (symbol->string n)))]
    [_
     (if (is-numeral tm)
         tm
         (error 'polynate "unknown term"))]))

(define (polyatom vars fm)
  (match fm
    [`(atom (rel ,a ,s ,t)) `(atom (rel ,a ,(polynate vars `(fn - ,s ,t)) ,zero))]
    [_ (error 'polyatom "not an atom")]))

;; ===== polynomial utilities =====
(define (coefficients vars p)
  (match p
    [`(fn + ,c (fn * (var ,x) ,q))
     #:when (equal? x (car vars))
     (cons c (coefficients vars q))]
    [_ (list p)]))

(define (degree vars p)
  (- (length (coefficients vars p)) 1))
(define (is-constant vars p)
  (= (degree vars p) 0))
(define (head vars p)
  (last (coefficients vars p)))

(define (behead vars p)
  (match p
    [`(fn + ,c (fn * (var ,x) ,pp))
     #:when (equal? x (car vars))
     (define p* (behead vars pp))
     (if (equal? p* zero)
         c
         `(fn + ,c (fn * (var ,x) ,p*)))]
    [_ zero]))

(define (poly-cmul k p)
  (match p
    [`(fn + ,c (fn * (var ,x) ,q)) `(fn + ,(poly-cmul k c) (fn * (var ,x) ,(poly-cmul k q)))]
    [_ (numeral1 (λ (m) (* k m)) p)]))

(define (headconst p)
  (match p
    [`(fn + ,c (fn * (var ,x) ,q)) (headconst q)]
    [`(fn ,n) (dest-numeral p)]))

(define (monic p)
  (define h (headconst p))
  (if (= h 0)
      (values p #f)
      (values (poly-cmul (/ 1 h) p) (< h 0))))

;; ===== pseudo-division =====
;; Pseudo-divide s by p in the head variable, returning (k r) such that
;; a^k * s = q*p + r with deg(r) < deg(p), where a is p's leading coefficient.
;; Multiplying by a^k sidesteps dividing by a coefficient whose sign/vanishing is
;; not yet known -- exactly what the sign-based QE below needs.
(define (pdivide vars s p)
  (define (shift1 x pp)
    `(fn + ,zero (fn * (var ,x) ,pp)))
  (define (pdivide-aux a n pp k s)
    (if (equal? s zero)
        (values k s)
        (let ([b (head vars s)]
              [m (degree vars s)])
          (if (< m n)
              (values k s)
              (let ([p* (funpow (- m n) (λ (z) (shift1 (car vars) z)) pp)])
                (if (equal? a b)
                    (pdivide-aux a n pp k (poly-sub vars s p*))
                    (pdivide-aux a
                                 n
                                 pp
                                 (+ k 1)
                                 (poly-sub vars (poly-mul vars a s) (poly-mul vars b p*)))))))))
  (pdivide-aux (head vars p) (degree vars p) p 0 s))

;; ===== signs =====
(define (swap swf s)
  (if (not swf)
      s
      (case s
        [(positive) 'negative]
        [(negative) 'positive]
        [else s])))

(define (findsign sgns p)
  (define-values (p* swf) (monic p))
  (define s (assoc p* sgns))
  (if s
      (swap swf (cdr s))
      (error 'findsign "findsign")))

(define (assertsign sgns ps)
  (define p (car ps))
  (define s (cdr ps))
  (if (equal? p zero)
      (if (eq? s 'zero)
          sgns
          (error 'assertsign "assertsign"))
      (let ()
        (define-values (p* swf) (monic p))
        (define s* (swap swf s))
        (define existing (assoc p* sgns))
        (define s0
          (if existing
              (cdr existing)
              s*))
        (if (or (eq? s* s0) (and (eq? s0 'nonzero) (or (eq? s* 'positive) (eq? s* 'negative))))
            (cons (cons p* s*) (subtract sgns (list (cons p* s0))))
            (error 'assertsign "assertsign")))))

;; If the sign database already pins down whether pol is zero, take that branch
;; directly; otherwise split the formula into a pol = 0 case and a pol /= 0 case,
;; extending sgns accordingly in each, so later steps never guess a sign.
(define (split-zero sgns pol cont-z cont-n)
  (define z
    (with-handlers ([exn:fail? (λ (e) #f)])
      (findsign sgns pol)))
  (if z
      ((if (eq? z 'zero) cont-z cont-n) sgns)
      (let ([eq (mk-eq pol zero)])
        `(or (and ,eq ,(cont-z (assertsign sgns (cons pol 'zero))))
             (and (not ,eq) ,(cont-n (assertsign sgns (cons pol 'nonzero))))))))

(define (poly-nonzero vars sgns pol)
  (define cs (coefficients vars pol))
  (define-values (dcs ucs) (partition (λ (p) (can (λ (x) (findsign sgns x)) p)) cs))
  (cond
    [(ormap (λ (p) (not (eq? (findsign sgns p) 'zero))) dcs) #t]
    [(null? ucs) #f]
    [else (end-itlist mk-or (map (λ (p) `(not ,(mk-eq p zero))) ucs))]))

(define (poly-nondiv vars sgns p s)
  (define-values (k r) (pdivide vars s p))
  (poly-nonzero vars sgns r))

;; ===== core elimination: exists x. (all eqs=0) /\ (all neqs<>0) =====
;; Recursively eliminate x from a system of equations (eqs, all = 0) and
;; disequations (neqs, all /= 0). Constant equations are resolved first against
;; the sign database sgns; otherwise the lowest-degree equation p is used to
;; reduce the rest by pseudo-division, branching on the sign of p's head
;; coefficient. The sign database keeps every such branch consistent.
(define (cqelim vars eqs-neqs sgns)
  (define eqs (car eqs-neqs))
  (define neqs (cdr eqs-neqs))
  (define c (findf (λ (p) (is-constant vars p)) eqs))
  (if c
      (let ([sgns* (with-handlers ([exn:fail? (λ (e) 'fail)])
                     (assertsign sgns (cons c 'zero)))])
        (if (eq? sgns* 'fail)
            #f
            `(and ,(mk-eq c zero) ,(cqelim vars (cons (subtract eqs (list c)) neqs) sgns*))))
      (if (null? eqs)
          (list-conj (map (λ (q) (poly-nonzero vars sgns q)) neqs))
          (let ()
            (define n (end-itlist min (map (λ (p) (degree vars p)) eqs)))
            (define p (findf (λ (p) (= (degree vars p) n)) eqs))
            (define oeqs (subtract eqs (list p)))
            (split-zero
             sgns
             (head vars p)
             (λ (s) (cqelim vars (cons (cons (behead vars p) oeqs) neqs) s))
             (λ (sgns*)
               (define (cfn s)
                 (let-values ([(k r) (pdivide vars s p)])
                   r))
               (cond
                 [(not (null? oeqs)) (cqelim vars (cons (cons p (map cfn oeqs)) neqs) sgns*)]
                 [(null? neqs) #t]
                 [else
                  (define q (end-itlist (λ (a b) (poly-mul vars a b)) neqs))
                  (poly-nondiv vars sgns* p (poly-pow vars q (degree vars p)))])))))))

;; ===== full QE =====
;; Seed sign database: 1 is positive and 0 is zero. assertsign extends it with
;; new sign facts as elimination discovers them.
(define init-sgns (list (cons one 'positive) (cons zero 'zero)))

(define (basic-complex-qelim vars fm)
  (match fm
    [`(exists ,x ,p)
     (define-values (eqs neqs) (partition (non negative) (conjuncts p)))
     (cqelim (cons x vars) (cons (map lhs eqs) (map (λ (e) (lhs (negate e))) neqs)) init-sgns)]))

(define complex-qelim
  (λ (fm)
    (simplify (evalc ((lift-qelim polyatom
                                  (λ (g) (dnf ((cnnf (λ (x) x)) (evalc g))))
                                  (λ (vars) (λ (f) (basic-complex-qelim vars f))))
                      fm)))))
