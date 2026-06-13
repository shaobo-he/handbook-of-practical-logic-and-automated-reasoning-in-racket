#lang racket/base

(require rackunit)
(require "prop.rkt")

;; ===== evaluation =====
(define (v->fn alist) (λ (x) (cdr (assoc x alist))))
(check-true (eval '(and (atom p) (atom q)) (v->fn '((p . #t) (q . #t)))))
(check-false (eval '(and (atom p) (atom q)) (v->fn '((p . #t) (q . #f)))))
(check-true (eval '(imp (atom p) (atom q)) (v->fn '((p . #f) (q . #f)))))

;; ===== atoms =====
(check-equal? (sort (atoms '(imp (atom p) (or (atom q) (atom p)))) symbol<?) '(p q))

;; ===== tautology / satisfiability =====
(check-true (tautology '(or (atom p) (not (atom p)))))
(check-false (tautology '(or (atom p) (atom q))))
;; hypothetical syllogism
(check-true (tautology '(imp (and (imp (atom p) (atom q)) (imp (atom q) (atom r)))
                             (imp (atom p) (atom r)))))
;; De Morgan
(check-true (tautology '(iff (not (and (atom p) (atom q))) (or (not (atom p)) (not (atom q))))))
(check-false (satisfiable '(and (atom p) (not (atom p)))))
(check-true (unsatisfiable '(and (atom p) (not (atom p)))))
(check-true (satisfiable '(or (atom p) (atom q))))

;; ===== simplification =====
(check-equal? (psimplify '(imp (imp #t (iff (atom x) #f)) (not (or (atom y) (and #f (atom z))))))
              '(imp (not (atom x)) (not (atom y))))
(check-equal? (psimplify '(or (imp (imp (atom x) (atom y)) #t) (not #f))) #t)

;; ===== duality =====
(check-equal? (dual '(and (atom p) (or (atom q) #f))) '(or (atom p) (and (atom q) #t)))

;; ===== NNF preserves meaning and removes ==>, <=> =====
(define f1 '(imp (atom p) (iff (atom q) (atom r))))
(check-true (tautology `(iff ,f1 ,(nnf f1))))

;; ===== DNF / CNF preserve meaning =====
(define f2 '(iff (atom p) (and (atom q) (or (atom r) (not (atom p))))))
(check-true (tautology `(iff ,f2 ,(dnf f2))))
(check-true (tautology `(iff ,f2 ,(cnf f2))))

;; ===== set-of-sets normal forms: edge cases =====
(check-equal? (simpcnf #t) '())
(check-equal? (simpcnf #f) (list '()))
(check-equal? (simpdnf #t) (list '()))
(check-equal? (simpdnf #f) '())

;; ===== printer =====
(check-equal? (prop-formula->string '(imp (atom p) (and (atom q) (atom r)))) "p ==> q /\\ r")
(check-equal? (prop-formula->string '(and (or (atom p) (atom q)) (atom r))) "(p \\/ q) /\\ r")
;; matches Harrison: prefix operands print at precedence 11, so nested ~ brackets
(check-equal? (prop-formula->string '(not (not (atom p)))) "~(~p)")
