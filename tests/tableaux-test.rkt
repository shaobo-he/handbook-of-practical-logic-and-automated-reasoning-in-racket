#lang racket/base

;; Unit tests for tableaux.rkt: literal unification helpers (unify-literals,
;; unify-complements) and the Prawitz / analytic-tableau provers. The provers
;; are semi-decidable, so they are exercised ONLY on known theorems.

(require rackunit)
(require "../fol/tableaux.rkt")
(require (only-in "../core/lib.rkt" undefined update))

;; ===== unify-literals: unify two same-polarity literals =====
;; identical atoms unify with no new bindings
(check-equal? (unify-literals undefined (cons '(atom (rel p)) '(atom (rel p)))) undefined)
;; a variable is bound to make the atoms match
(check-equal? (unify-literals undefined (cons '(atom (rel p (var x))) '(atom (rel p (fn a)))))
              (update 'x '(fn a) undefined))
;; negated literals unify through the negation
(check-equal? (unify-literals undefined
                              (cons '(not (atom (rel p (var x)))) '(not (atom (rel p (fn a))))))
              (update 'x '(fn a) undefined))
;; different relations cannot be unified
(check-exn exn:fail? (λ () (unify-literals undefined (cons '(atom (rel p)) '(atom (rel q))))))
;; mixed polarity is not handled by unify-literals (that is unify-complements' job)
(check-exn exn:fail? (λ () (unify-literals undefined (cons '(atom (rel p)) '(not (atom (rel p)))))))

;; ===== unify-complements: unify a literal with the COMPLEMENT of another =====
;; P(x) against the complement of (not P(a)) = P(a) -> binds x to a
(check-equal? (unify-complements undefined
                                 (cons '(atom (rel p (var x))) '(not (atom (rel p (fn a))))))
              (update 'x '(fn a) undefined))
;; two literals of the SAME polarity are not complementary -> raise
(check-exn exn:fail?
           (λ () (unify-complements undefined (cons '(atom (rel p (var x))) '(atom (rel p (fn a)))))))

;; ===== known theorems for the provers =====
(define peirce '(imp (imp (imp (atom (rel P)) (atom (rel Q))) (atom (rel P))) (atom (rel P))))
(define lem '(or (atom (rel p)) (not (atom (rel p)))))
(define drinker '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y)))))))

;; ===== Prawitz-style procedure: returns the number of instantiation rounds =====
(check-pred exact-nonnegative-integer? (prawitz peirce))
(check-pred exact-nonnegative-integer? (prawitz drinker))

;; ===== analytic tableau: returns the depth at which a refutation was found =====
(check-equal? (tab peirce) 0) ; purely propositional: closes at depth 0
(check-equal? (tab lem) 0)
(check-pred exact-nonnegative-integer? (tab drinker))
;; splittab refutes each DNF disjunct of the negated goal
(check-pred (λ (l) (andmap exact-nonnegative-integer? l)) (splittab drinker))

;; ===== compare-instances: (prawitz . davisputnam) instance counts agree here =====
(check-equal? (compare-instances drinker) '(2 . 2))
