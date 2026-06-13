#lang racket/base

;; unif.fs --- syntactic unification of first-order terms.
;;
;; A unifier `env` is a partial function (hash) from variable name to term.
;; `unify` builds a possibly-triangular env; `solve` normalizes it to an
;; idempotent substitution.

(require racket/match)
(require (only-in "lib.rkt" undefined update defined apply mapf))
(require (only-in "fol.rkt" tsubst))

(provide (all-defined-out))

;; #t if binding x := t would be trivial (t is x); raises on a cyclic binding
(define (istriv env x t)
  (match t
    [`(var ,y)
     (or (equal? y x)
         (and (defined env y) (istriv env x (apply env y))))]
    [`(fn ,f ,@args)
     (and (ormap (λ (a) (istriv env x a)) args)
          (error 'unify "cyclic"))]))

;; eqs is a list of (s . t) pairs to be unified under env
(define (unify env eqs)
  (match eqs
    ['() env]
    [(cons (cons `(fn ,f ,@fargs) `(fn ,g ,@gargs)) oth)
     (if (and (equal? f g) (= (length fargs) (length gargs)))
         (unify env (append (map cons fargs gargs) oth))
         (error 'unify "impossible unification"))]
    [(cons (cons `(var ,x) t) oth) (unify-var env x t oth)]
    [(cons (cons t `(var ,x)) oth) (unify-var env x t oth)]))

(define (unify-var env x t oth)
  (if (defined env x)
      (unify env (cons (cons (apply env x) t) oth))
      (unify (if (istriv env x t) env (update x t env)) oth)))

;; normalize a (triangular) env to an idempotent substitution
(define (solve env)
  (define env* (mapf (λ (t) (tsubst env t)) env))
  (if (equal? env* env) env (solve env*)))

(define (fullunify eqs) (solve (unify undefined eqs)))

;; solve and apply, returning each equation with both sides instantiated
(define (unify-and-apply eqs)
  (define i (fullunify eqs))
  (map (λ (e) (cons (tsubst i (car e)) (tsubst i (cdr e)))) eqs))
