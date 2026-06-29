#lang racket/base

(require rackunit)
(require "../fol/unif.rkt")
(require (only-in "../core/lib.rkt" undefined update))

;; a successful unification makes both sides of each equation identical
(define (unifies? eqs)
  (andmap (λ (e) (equal? (car e) (cdr e))) (unify-and-apply eqs)))

;; f(x, g(y)) = f(f(z), w)  -->  both become f(f(z), g(y))
(define e1 (list (cons '(fn f (var x) (fn g (var y))) '(fn f (fn f (var z)) (var w)))))
(check-true (unifies? e1))
(check-equal? (unify-and-apply e1)
              (list (cons '(fn f (fn f (var z)) (fn g (var y)))
                          '(fn f (fn f (var z)) (fn g (var y))))))

;; simple variable binding
(check-equal? (unify-and-apply (list (cons '(var x) '(fn |0|)))) (list (cons '(fn |0|) '(fn |0|))))

;; chained bindings resolve transitively
(check-true (unifies? (list (cons '(var x) '(var y)) (cons '(var y) '(fn a (var z))))))

;; occurs check: f(x, g(y)) = f(y, x) is cyclic
(check-exn exn:fail?
           (λ ()
             (unify-and-apply (list (cons '(fn f (var x) (fn g (var y))) '(fn f (var y) (var x)))))))

;; clashing function symbols / arities are impossible
(check-exn exn:fail? (λ () (unify-and-apply (list (cons '(fn f (var x)) '(fn g (var x)))))))
(check-exn exn:fail? (λ () (unify-and-apply (list (cons '(fn f (var x)) '(fn f (var x) (var y)))))))

;; ===== istriv: trivial-binding test plus occurs check =====
;; binding x := x is trivial
(check-true (istriv undefined 'x '(var x)))
;; trivial through the env chain: y is already bound to x, so x := y is trivial
(check-true (istriv (update 'y '(var x) undefined) 'x '(var y)))
;; a ground term contains no variables, so it can never be cyclic -> not trivial
(check-false (istriv undefined 'x '(fn a)))
(check-false (istriv undefined 'x '(fn f (var y))))
;; occurs check: x occurs in f(x), so x := f(x) is cyclic -> raise
(check-exn exn:fail? (λ () (istriv undefined 'x '(fn f (var x)))))
;; transitive cycle x -> y -> f(x) is detected through the env
(check-exn exn:fail? (λ () (istriv (update 'y '(fn f (var x)) undefined) 'x '(var y))))

;; ===== unify: build a (possibly triangular) env from equations =====
;; base case: no equations leaves the env untouched
(check-equal? (unify undefined '()) undefined)
;; a single variable equation adds one binding
(check-equal? (unify undefined (list (cons '(var x) '(fn a)))) (update 'x '(fn a) undefined))
;; chained variable equations resolve transitively after solve
(check-equal? (solve (unify undefined (list (cons '(var x) '(var y)) (cons '(var y) '(fn a)))))
              (hash 'x '(fn a) 'y '(fn a)))
;; an existing binding is honoured: x is already a, so x = b becomes a = b (clash)
(check-exn exn:fail? (λ () (unify (update 'x '(fn a) undefined) (list (cons '(var x) '(fn b))))))

;; ===== solve: normalize a triangular env into an idempotent substitution =====
(check-equal? (solve (update 'x '(var y) (update 'y '(fn a) undefined))) (hash 'x '(fn a) 'y '(fn a)))
;; solve reaches a fixed point: solving an already-solved env changes nothing
(let ([s (fullunify (list (cons '(var x) '(var y)) (cons '(var y) '(fn a))))])
  (check-equal? (solve s) s))

;; ===== unify-var: add a binding unless it is trivial =====
(check-equal? (unify-var undefined 'x '(fn a) '()) (update 'x '(fn a) undefined))
;; a trivial binding x := x adds nothing
(check-equal? (unify-var undefined 'x '(var x) '()) undefined)
