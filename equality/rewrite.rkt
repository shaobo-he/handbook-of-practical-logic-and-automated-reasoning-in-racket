#lang racket/base

;; rewrite.fs --- rewriting terms with a list of equations, at depth and to
;; normal form (top-down, leftmost-outermost).

(require racket/match)
(require (only-in "../core/lib.rkt" undefined))
(require (only-in "../fol/fol.rkt" tsubst))
(require (only-in "../fol/resolution.rkt" term-match))

(provide (all-defined-out))

;; rewrite once at the top with the first applicable equation
(define (rewrite1 eqs t)
  (match eqs
    [(cons `(atom (rel = ,l ,r)) oeqs)
     (with-handlers ([exn:fail? (λ (e) (rewrite1 oeqs t))])
       (tsubst (term-match undefined (list (cons l t))) r))]
    [_ (error 'rewrite1 "rewrite1")]))

;; rewrite to normal form
(define (rewrite eqs tm)
  (with-handlers ([exn:fail? (λ (e)
                               (match tm
                                 [`(var ,x) tm]
                                 [`(fn ,f ,@args)
                                  (define tm* `(fn ,f ,@(map (λ (a) (rewrite eqs a)) args)))
                                  (if (equal? tm* tm)
                                      tm
                                      (rewrite eqs tm*))]))])
    (rewrite eqs (rewrite1 eqs tm))))
