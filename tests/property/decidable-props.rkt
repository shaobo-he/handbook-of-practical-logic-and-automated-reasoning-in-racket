#lang racket/base

;; Property tests for decidable theories: the complex/grobner/real polynomial
;; rings satisfy ring and derivative laws, Cooper linearization matches native
;; arithmetic, QE decides ground (in)equalities, DLO QE removes all quantifiers,
;; and grobner-decide confirms field congruences.

(require rackunit
         rackcheck
         racket/match
         "common.rkt")
(require (only-in "../../decidable/cooper.rkt" integer-qelim lint dest-numeral))
(require (only-in "../../decidable/qelim.rkt" quelim-dlo))
(require (only-in "../../decidable/complex.rkt" complex-qelim polynate poly-add poly-neg poly-mul))
(require (only-in "../../decidable/real.rkt" real-qelim poly-diff))
(require (only-in "../../decidable/grobner.rkt"
                  grobner-decide
                  mpolynate
                  mpoly-add
                  mpoly-neg
                  mpoly-mul))

(define (cnum k)
  `(fn ,(string->symbol (number->string k))))

;; polynomial terms over {x,y} with +,-,*,^ (numeral exponent)
(define (poly-term-gen n)
  (if (<= n 0)
      (gen:choice (gen:one-of '((var x) (var y))) (gen:map (gen:integer-in 0 4) cnum))
      (gen:frequency (list (cons 1 (gen:one-of '((var x) (var y))))
                           (cons 1 (gen:map (gen:integer-in 0 4) cnum))
                           (cons 3
                                 (gen:bind (gen:one-of '(+ - *))
                                           (λ (op)
                                             (gen:map (gen:tuple (poly-term-gen (sub1 n))
                                                                 (poly-term-gen (sub1 n)))
                                                      (λ (ab) `(fn ,op ,(car ab) ,(cadr ab)))))))
                           (cons 1
                                 (gen:map (gen:tuple (poly-term-gen (sub1 n)) (gen:integer-in 0 3))
                                          (λ (te) `(fn ^ ,(car te) ,(cnum (cadr te))))))))))
(define pv '(x y))
(define zero-poly (polynate pv '(fn |0|)))
(define zero-mpoly (mpolynate pv '(fn |0|)))

;; complex.rkt nested polynomial ring laws (canonical form => structural equality)
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
                          (equal? (poly-add pv (polynate pv t1) (polynate pv t2))
                                  (poly-add pv (polynate pv t2) (polynate pv t1)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)] [t3 (poly-term-gen 2)])
                          (define p (polynate pv t1))
                          (define q (polynate pv t2))
                          (define r (polynate pv t3))
                          (equal? (poly-mul pv p (poly-add pv q r))
                                  (poly-add pv (poly-mul pv p q) (poly-mul pv p r)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)])
                          (equal? (poly-add pv (polynate pv t1) (poly-neg (polynate pv t1)))
                                  zero-poly)))
;; grobner.rkt monomial-list ring laws
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
                          (equal? (mpoly-add (mpolynate pv t1) (mpolynate pv t2))
                                  (mpoly-add (mpolynate pv t2) (mpolynate pv t1)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)] [t3 (poly-term-gen 2)])
                          (define p (mpolynate pv t1))
                          (define q (mpolynate pv t2))
                          (define r (mpolynate pv t3))
                          (equal? (mpoly-mul p (mpoly-add q r))
                                  (mpoly-add (mpoly-mul p q) (mpoly-mul p r)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)])
                          (equal? (mpoly-add (mpolynate pv t1) (mpoly-neg (mpolynate pv t1)))
                                  zero-mpoly)))
;; real.rkt formal differentiation: linearity and the product rule
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
                          (define p (polynate pv t1))
                          (define q (polynate pv t2))
                          (equal? (poly-diff pv (poly-add pv p q))
                                  (poly-add pv (poly-diff pv p) (poly-diff pv q)))))
(check-property
 poly
 (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
           (define p (polynate pv t1))
           (define q (polynate pv t2))
           (equal? (poly-diff pv (poly-mul pv p q))
                   (poly-add pv (poly-mul pv (poly-diff pv p) q) (poly-mul pv p (poly-diff pv q))))))

;; cooper linearization of a ground term equals its native value
(define (cterm-gen n)
  (if (<= n 0)
      (gen:map (gen:integer-in 0 4) cnum)
      (gen:bind (gen:one-of '(+ - *))
                (λ (op)
                  (gen:map (gen:tuple (cterm-gen (sub1 n)) (cterm-gen (sub1 n)))
                           (λ (ab) `(fn ,op ,(car ab) ,(cadr ab))))))))
(define (cterm-value t)
  (match t
    [`(fn + ,a ,b) (+ (cterm-value a) (cterm-value b))]
    [`(fn - ,a ,b) (- (cterm-value a) (cterm-value b))]
    [`(fn * ,a ,b) (* (cterm-value a) (cterm-value b))]
    [`(fn ,k) (string->number (symbol->string k))]))
(check-property big (property ([t (cterm-gen 2)]) (= (dest-numeral (lint '() t)) (cterm-value t))))

;; QE procedures decide ground (in)equalities correctly
(define (rel-true? op av bv)
  (case op
    [(=) (= av bv)]
    [(<) (< av bv)]
    [(<=) (<= av bv)]
    [(>) (> av bv)]
    [(>=) (>= av bv)]))
(check-property mid
                (property ([op (gen:one-of '(= < <= > >=))] [a (cterm-gen 2)] [b (cterm-gen 2)])
                          (eq? (integer-qelim `(atom (rel ,op ,a ,b)))
                               (rel-true? op (cterm-value a) (cterm-value b)))))
(check-property mid
                (property ([op (gen:one-of '(= < <= > >=))] [a (cterm-gen 2)] [b (cterm-gen 2)])
                          (eq? (real-qelim `(atom (rel ,op ,a ,b)))
                               (rel-true? op (cterm-value a) (cterm-value b)))))
(check-property mid
                (property ([a (cterm-gen 2)] [b (cterm-gen 2)])
                          (eq? (complex-qelim `(atom (rel = ,a ,b)))
                               (= (cterm-value a) (cterm-value b)))))

;; DLO quantifier elimination removes all quantifiers
(define (qfree? fm)
  (match fm
    [`(,(or 'forall 'exists) ,_ ,_) #f]
    [`(not ,p) (qfree? p)]
    [`(,(or 'and 'or 'imp 'iff) ,p ,q) (and (qfree? p) (qfree? q))]
    [_ #t]))
(define (dlo-gen n)
  (define as
    '((atom (rel < (var x) (var y))) (atom (rel < (var y) (var x))) (atom (rel = (var x) (var y)))))
  (if (<= n 0)
      (gen:one-of as)
      (gen:frequency (list (cons 1 (gen:one-of as))
                           (cons 2 (gen:map (dlo-gen (sub1 n)) (λ (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or imp) dlo-gen n))
                           (cons 2 (quant-gen '(forall exists) '(x y z) dlo-gen n))))))
(check-property mid (property ([fm (dlo-gen 3)]) (qfree? (quelim-dlo fm))))

;; grobner-decide confirms congruence over a field: x=y => p(x)=p(y)
(define (x->y t)
  (match t
    [`(var x) '(var y)]
    [`(fn ,f . ,as) `(fn ,f ,@(map x->y as))]
    [_ t]))
(check-property low
                (property ([t (poly-term-gen 2)])
                          (grobner-decide `(imp (atom (rel = (var x) (var y)))
                                                (atom (rel = ,t ,(x->y t)))))))
