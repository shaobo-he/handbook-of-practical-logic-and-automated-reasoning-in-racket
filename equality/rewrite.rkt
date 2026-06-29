#lang racket/base

;; rewrite --- rewriting terms with a list of equations, at depth and to
;; normal form (top-down, leftmost-outermost).

(require racket/match)
(require (only-in "../core/lib.rkt" undefined))
(require (only-in "../fol/fol.rkt" tsubst))
(require (only-in "../fol/resolution.rkt" term-match))

(provide (all-defined-out))

;; rewrite once at the top with the first applicable equation.
;; term-match raises if l does not match t; the handler then tries the next
;; equation, so the equations are effectively tried in order (first match wins).
(define (rewrite1 eqs t)
  (match eqs
    [`((atom (rel = ,l ,r)) . ,oeqs)
     (with-handlers ([exn:fail? (λ (e) (rewrite1 oeqs t))])
       (tsubst (term-match undefined (list (cons l t))) r))]
    [_ (error 'rewrite1 "rewrite1")]))

;; rewrite to normal form (top-down, leftmost-outermost).
;; First try to rewrite at the top; if rewrite1 fails (no rule applies here), the
;; handler descends into the arguments. The (equal? tm* tm) test detects that the
;; arguments are already in normal form and stops, otherwise we re-try the top of
;; the rewritten term. NB: this still diverges on genuinely non-terminating rule
;; sets (e.g. a=b together with b=a), as termination is the caller's responsibility.
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
