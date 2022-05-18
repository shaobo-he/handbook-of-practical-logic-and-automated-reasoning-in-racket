#lang racket/base

(require rackunit)
(require racket/match)
(require (only-in racket/list range))
(require (only-in math/number-theory prime?))
(require "fol-untyped.rkt")


;; domain, func, pred for Boolean and modulo n
(define b-domain '(#t #f))

(define (b-func f args)
  (match f
    ['|0| #f]
    ['|1| #t]
    ['+ (not (apply equal? args))]
    ['* (apply (λ (x y) (and x y)) args)]))

(define (b-pred p args)
  (match p
    ['= (apply equal? args)]))

(define (m-domain n)
  (range n))

(define (m-func n)
  (λ (f args)
    (match f
      ['|0| 0]
      ['|1| (modulo 1 n)]
      ['+ (apply (λ (x y) (modulo (+ x y) n)) args)]
      ['* (apply (λ (x y) (modulo (* x y) n)) args)])))

(define (m-pred n)
  (λ (p args)
    (match p
      ['= (apply equal? args)])))

;; simple term and formula
(define *11 '(fn * (fn |1|) (fn |1|)))
(define *11=0 `(atom (rel = (fn |0|) ,*11)))

(check-true (termval b-func #f *11))
(check-false (holds b-domain b-func b-pred #f *11=0))

;; quantified formulas
(define 0or1 '(forall x (or (atom (rel = (var x) (fn |0|))) (atom (rel = (var x) (fn |1|))))))
(define v (make-immutable-hash))

(check-true (holds b-domain b-func b-pred v 0or1))
(check-true (holds (m-domain 2) (m-func 2) (m-pred 2) v 0or1))
(check-false (holds (m-domain 3) (m-func 3) (m-pred 3) v 0or1))

(define mul-rev '(forall x (imp (not (atom (rel = (var x) (fn |0|)))) (exists y (atom (rel = (fn * (var x) (var y)) (fn |1|)))))))
(check-equal?
 (filter (λ (n) (holds (m-domain n) (m-func n) (m-pred n) v mul-rev)) (range 1 45))
 (cons 1 (filter prime? (range 1 45))))

;; groundness and sentence tests
(check-true (ground/term? *11))
(check-true (ground/formula? *11=0))
(check-true (sentence? 0or1))
(check-true (sentence? mul-rev))

;; generalize
(define xy+z '(exists y (atom (rel < (var x) (fn '+ (var y) (var z))))))
(check-true (sentence? (generalize xy+z)))

;; substitution in terms
(define x≤y '(fn ≤ (var x) (var y)))
(check-equal?
 (tsubst (λ (x) (match x ['x '(fn |1|)])) x≤y)
 '(fn ≤ ((fn |1|) (var y))))

;; substituion in formulas
(check-equal? 'x (variant 'x '(z y)))
(check-equal? 'x^ (variant 'x '(x y)))
(check-equal? 'x^^ (variant 'x '(x x^)))
(define (sfn k)
  (match k
    ['y '(var x)]))
(define qx=y '(forall x (atom (rel = (var x) (var y)))))
(check-equal?
 (subst sfn qx=y)
 '(forall x^ (atom (rel = (var x^) (var x)))))
(define qxx^y
  '(forall
    x
    (forall
     x^
     (imp (atom (rel = (var x) (var y))) (atom (rel = (var x) (var x^)))))))
(check-equal?
 (subst sfn qxx^y)
 '(forall
   x^
   (forall
    x^^
    (imp (atom (rel = (var x^) (var x))) (atom (rel = (var x^) (var x^^)))))))

;; prenex normal form
(define nnf-test
  '(imp
    (forall x (atom (rel P (var x))))
    (iff
     (exists y (atom (rel Q (var y))))
     (exists z (and (atom (rel P (var z))) (atom (rel Q (var z))))))))
(check-equal?
 (nnf nnf-test)
 '(or (exists x (not (atom (rel P (var x)))))
      (or (and
           (exists y (atom (rel Q (var y))))
           (exists z (and (atom (rel P (var z))) (atom (rel Q (var z))))))
          (and
           (forall y (not (atom (rel Q (var y)))))
           (forall z (or (not (atom (rel P (var z)))) (not (atom (rel Q (var z))))))))))
(define prenex-test
  '(imp
    (forall x (or (atom (rel P (var x))) (atom (rel R (var y)))))
    (exists
     y
     (exists
      z
      (or
       (atom (rel Q (var y)))
       (not
        (exists
         z
         (and (atom (rel P (var z))) (atom (rel Q (var z)))))))))))

(check-equal?
 (pnf prenex-test)
 '(exists
   x
   (forall
    z
    (or
     (and (not (atom (rel P (var x)))) (not (atom (rel R (var y)))))
     (or
      (atom (rel Q (var x)))
      (or (not (atom (rel P (var z)))) (not (atom (rel Q (var z))))))))))