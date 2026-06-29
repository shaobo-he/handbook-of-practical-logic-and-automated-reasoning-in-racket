#lang racket/base

;; unif --- syntactic unification of first-order terms.
;;
;; A unifier `env` is a partial function (hash) from variable name to term.
;; `unify` builds a possibly-triangular env; `solve` normalizes it to an
;; idempotent substitution.

(require racket/match)
(require (only-in "../core/lib.rkt" undefined update defined apply mapf))
(require (only-in "fol.rkt" tsubst))

(provide (all-defined-out))

;; The occurs-check, run before adding a binding x := t:
;;  - returns #t when the binding is trivial (t already resolves to x), so it can
;;    be skipped;
;;  - returns #f when t is a sound, non-cyclic binding;
;;  - raises when t is a compound term that contains x (a cycle like x := f(x)).
;; For a variable y it follows y's existing binding in env (a chain), but only if
;; y is bound: an unbound y cannot create a cycle, so we treat it as non-trivial.
(define (istriv env x t)
  (match t
    [`(var ,y) (or (equal? y x) (and (defined env y) (istriv env x (apply env y))))]
    [`(fn ,f ,@args) (and (ormap (λ (a) (istriv env x a)) args) (error 'unify "cyclic"))]))

;; Process the equation worklist eqs (a list of (s . t) pairs) under env. Equal
;; function applications decompose into pairwise argument equations pushed back
;; onto the worklist (with an arity/symbol clash being a unification failure); an
;; equation with a variable on either side is handed to unify-var. Decomposing
;; before binding keeps the structural work ahead of the variable bindings.
(define (unify env eqs)
  (match eqs
    ['() env]
    [`(((fn ,f ,@fargs) . (fn ,g ,@gargs)) . ,oth)
     (if (and (equal? f g) (= (length fargs) (length gargs)))
         (unify env (append (map cons fargs gargs) oth))
         (error 'unify "impossible unification"))]
    [`(((var ,x) . ,t) . ,oth) (unify-var env x t oth)]
    [`((,t . (var ,x)) . ,oth) (unify-var env x t oth)]))

;; bind x := t. If x is already bound, re-unify its existing value against t
;; instead of overwriting; otherwise add the binding unless it is trivial. The
;; istriv call is the occurs-check that rejects cyclic bindings.
(define (unify-var env x t oth)
  (if (defined env x)
      (unify env (cons (cons (apply env x) t) oth))
      (unify (if (istriv env x t)
                 env
                 (update x t env))
             oth)))

;; normalize a (triangular) env to an idempotent substitution: repeatedly
;; substitute the env into its own range until it stops changing. One pass is
;; not enough because a binding x:=y, y:=t only becomes x:=t after y is resolved.
(define (solve env)
  (define env* (mapf (λ (t) (tsubst env t)) env))
  (if (equal? env* env)
      env
      (solve env*)))

(define (fullunify eqs)
  (solve (unify undefined eqs)))

;; solve and apply, returning each equation with both sides instantiated
(define (unify-and-apply eqs)
  (define i (fullunify eqs))
  (map (λ (e) (cons (tsubst i (car e)) (tsubst i (cdr e)))) eqs))
