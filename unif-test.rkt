#lang racket/base

(require rackunit)
(require "unif.rkt")

;; a successful unification makes both sides of each equation identical
(define (unifies? eqs)
  (andmap (λ (e) (equal? (car e) (cdr e))) (unify-and-apply eqs)))

;; f(x, g(y)) = f(f(z), w)  -->  both become f(f(z), g(y))
(define e1 (list (cons '(fn f (var x) (fn g (var y)))
                       '(fn f (fn f (var z)) (var w)))))
(check-true (unifies? e1))
(check-equal? (unify-and-apply e1)
              (list (cons '(fn f (fn f (var z)) (fn g (var y)))
                          '(fn f (fn f (var z)) (fn g (var y))))))

;; simple variable binding
(check-equal? (unify-and-apply (list (cons '(var x) '(fn |0|))))
              (list (cons '(fn |0|) '(fn |0|))))

;; chained bindings resolve transitively
(check-true (unifies? (list (cons '(var x) '(var y))
                            (cons '(var y) '(fn a (var z))))))

;; occurs check: f(x, g(y)) = f(y, x) is cyclic
(check-exn exn:fail?
           (λ () (unify-and-apply (list (cons '(fn f (var x) (fn g (var y)))
                                              '(fn f (var y) (var x)))))))

;; clashing function symbols / arities are impossible
(check-exn exn:fail?
           (λ () (unify-and-apply (list (cons '(fn f (var x)) '(fn g (var x)))))))
(check-exn exn:fail?
           (λ () (unify-and-apply (list (cons '(fn f (var x)) '(fn f (var x) (var y)))))))
