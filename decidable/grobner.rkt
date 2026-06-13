#lang racket/base

;; grobner.fs --- Grobner basis algorithm and a universal decision procedure
;; for algebraically closed fields (with the Rabinowitsch trick).
;;
;; Polynomials here are lists of monomials (coeff . exponent-list), one
;; exponent per variable in `vars`, ordered by a total-degree/lex order.

(require racket/match)
(require (only-in racket/list partition range))
(require (only-in "../core/lib.rkt" funpow union tryfind distinctpairs))
(require (only-in "../core/formulas.rkt" end-itlist))
(require (only-in "../prop/prop.rkt" positive negate simpdnf))
(require (only-in "../fol/fol.rkt" fv variant))
(require (only-in "../fol/skolem.rkt" specialize prenex nnf simplify))
(require (only-in "cooper.rkt" dest-numeral mk-numeral))
(require (only-in "../equality/order.rkt" lexord))

(provide (all-defined-out))

(define grobner-verbose (make-parameter #f))

;; ===== monomial operations =====
(define (mmul cm1 cm2)
  (cons (* (car cm1) (car cm2)) (map + (cdr cm1) (cdr cm2))))

(define (mdiv cm1 cm2)
  (define (index-sub n1 n2)
    (if (< n1 n2)
        (error 'mdiv "mdiv")
        (- n1 n2)))
  (cons (/ (car cm1) (car cm2)) (map index-sub (cdr cm1) (cdr cm2))))

(define (mlcm cm1 cm2)
  (cons 1 (map max (cdr cm1) (cdr cm2))))

(define (morder-lt m1 m2)
  (define n1 (foldr + 0 m1))
  (define n2 (foldr + 0 m2))
  (or (< n1 n2) (and (= n1 n2) (lexord (λ (a b) (> a b)) m1 m2))))

;; ===== polynomial arithmetic =====
(define (mpoly-mmul cm pol)
  (map (λ (m) (mmul cm m)) pol))
(define (mpoly-neg pol)
  (map (λ (cm) (cons (- (car cm)) (cdr cm))) pol))
(define (mpoly-const vars c)
  (if (= c 0)
      '()
      (list (cons c (map (λ (_) 0) vars)))))
(define (mpoly-var vars x)
  (list (cons 1 (map (λ (y) (if (equal? y x) 1 0)) vars))))

(define (mpoly-add l1 l2)
  (match* (l1 l2)
    [('() x) x]
    [(x '()) x]
    [((cons (cons c1 m1) o1) (cons (cons c2 m2) o2))
     (cond
       [(equal? m1 m2)
        (define c (+ c1 c2))
        (define rest (mpoly-add o1 o2))
        (if (= c 0)
            rest
            (cons (cons c m1) rest))]
       [(morder-lt m2 m1) (cons (cons c1 m1) (mpoly-add o1 l2))]
       [else (cons (cons c2 m2) (mpoly-add l1 o2))])]))

(define (mpoly-sub l1 l2)
  (mpoly-add l1 (mpoly-neg l2)))

(define (mpoly-mul l1 l2)
  (match l1
    ['() '()]
    [(cons h1 t1) (mpoly-add (mpoly-mmul h1 l2) (mpoly-mul t1 l2))]))

(define (mpoly-pow vars l n)
  (funpow n (λ (z) (mpoly-mul l z)) (mpoly-const vars 1)))

(define (mpoly-inv p)
  (match p
    [(list (cons c m))
     #:when (andmap (λ (i) (= i 0)) m)
     (list (cons (/ 1 c) m))]
    [_ (error 'mpoly-inv "non-constant polynomial")]))

(define (mpoly-div p q)
  (mpoly-mul p (mpoly-inv q)))

;; ===== term -> canonical polynomial =====
(define (mpolynate vars tm)
  (match tm
    [`(var ,x) (mpoly-var vars x)]
    [`(fn - ,t) (mpoly-neg (mpolynate vars t))]
    [`(fn + ,s ,t) (mpoly-add (mpolynate vars s) (mpolynate vars t))]
    [`(fn - ,s ,t) (mpoly-sub (mpolynate vars s) (mpolynate vars t))]
    [`(fn * ,s ,t) (mpoly-mul (mpolynate vars s) (mpolynate vars t))]
    [`(fn / ,s ,t) (mpoly-div (mpolynate vars s) (mpolynate vars t))]
    [`(fn ^ ,t (fn ,n)) (mpoly-pow vars (mpolynate vars t) (string->number (symbol->string n)))]
    [_ (mpoly-const vars (dest-numeral tm))]))

(define (mpolyatom vars fm)
  (match fm
    [`(atom (rel = ,s ,t)) (mpolynate vars `(fn - ,s ,t))]
    [_ (error 'mpolyatom "not an equation")]))

;; ===== reduction =====
(define (reduce1 cm pol)
  (match pol
    ['() (error 'reduce1 "reduce1")]
    [(cons hm cms)
     (define cm* (mdiv cm hm))
     (mpoly-mmul (cons (- (car cm*)) (cdr cm*)) cms)]))

(define (reduceb cm pols)
  (tryfind (λ (p) (reduce1 cm p)) pols))

(define (reduce pols pol)
  (match pol
    ['() '()]
    [(cons cm ptl)
     (with-handlers ([exn:fail? (λ (e) (cons cm (reduce pols ptl)))])
       (reduce pols (mpoly-add (reduceb cm pols) ptl)))]))

;; ===== S-polynomial and Grobner basis =====
(define (spoly pol1 pol2)
  (match* (pol1 pol2)
    [('() _) '()]
    [(_ '()) '()]
    [((cons m1 ptl1) (cons m2 ptl2))
     (define m (mlcm m1 m2))
     (mpoly-sub (mpoly-mmul (mdiv m m1) ptl1) (mpoly-mmul (mdiv m m2) ptl2))]))

(define (grobner basis pairs)
  (when (grobner-verbose)
    (printf "~a basis elements and ~a pairs\n" (length basis) (length pairs)))
  (match pairs
    ['() basis]
    [(cons p1p2 opairs)
     (define sp (reduce basis (spoly (car p1p2) (cdr p1p2))))
     (cond
       [(null? sp) (grobner basis opairs)]
       [(andmap (λ (cm) (andmap (λ (e) (= e 0)) (cdr cm))) sp) (list sp)]
       [else (grobner (cons sp basis) (append opairs (map (λ (p) (cons p sp)) basis)))])]))

(define (groebner basis)
  (grobner basis (distinctpairs basis)))

;; ===== Rabinowitsch trick: p =/= 0  becomes  1 - v*p = 0 =====
(define (rabinowitsch vars v p)
  (mpoly-sub (mpoly-const vars 1) (mpoly-mul (mpoly-var vars v) p)))

(define (grobner-trivial fms)
  (define vars0 (foldr (λ (f acc) (union (fv f) acc)) '() fms))
  (define-values (eqs neqs) (partition positive fms))
  (define rvs
    (map (λ (n) (variant (string->symbol (string-append "_" (number->string n))) vars0))
         (range 1 (add1 (length neqs)))))
  (define vars (append vars0 rvs))
  (define poleqs (map (λ (e) (mpolyatom vars e)) eqs))
  (define polneqs (map (λ (e) (mpolyatom vars (negate e))) neqs))
  (define pols (append poleqs (map (λ (rv pn) (rabinowitsch vars rv pn)) rvs polneqs)))
  (null? (reduce (groebner pols) (mpoly-const vars 1))))

(define (grobner-decide fm)
  (define fm1 (specialize (prenex (nnf (simplify fm)))))
  (andmap grobner-trivial (simpdnf (nnf `(not ,fm1)))))

;; ===== mapping polynomials back to terms (for display) =====
(define (term-of-varpow vars xk)
  (if (= (cdr xk) 1)
      `(var ,(car xk))
      `(fn ^ (var ,(car xk)) ,(mk-numeral (cdr xk)))))

(define (term-of-varpows vars lis)
  (define tms (filter (λ (ab) (not (= (cdr ab) 0))) (map cons vars lis)))
  (end-itlist (λ (s t) `(fn * ,s ,t)) (map (λ (xk) (term-of-varpow vars xk)) tms)))

(define (term-of-monomial vars cm)
  (cond
    [(andmap (λ (x) (= x 0)) (cdr cm)) (mk-numeral (car cm))]
    [(= (car cm) 1) (term-of-varpows vars (cdr cm))]
    [else `(fn * ,(mk-numeral (car cm)) ,(term-of-varpows vars (cdr cm)))]))

(define (term-of-poly vars pol)
  (end-itlist (λ (s t) `(fn + ,s ,t)) (map (λ (cm) (term-of-monomial vars cm)) pol)))

(define (grobner-basis vars pols)
  (map (λ (p) (term-of-poly vars p)) (groebner (map (λ (p) (mpolyatom vars p)) pols))))
