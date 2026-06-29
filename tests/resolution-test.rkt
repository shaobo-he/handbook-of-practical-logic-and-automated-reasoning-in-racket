#lang racket/base

;; Unit tests for resolution.rkt: the most-general-unifier of a literal list
;; (mgu), unifiability, variable renaming, subsumption (term-match /
;; match-literals / subsumes-clause), the resolution rule with factoring
;; (resolve-clauses) and clause-set maintenance (replace / incorporate). The
;; full search loops are exercised end-to-end only on known theorems.

(require rackunit)
(require "../fol/resolution.rkt")
(require (only-in "../core/lib.rkt" undefined update))

;; ===== mgu: most general unifier of a list of literals =====
(check-equal? (mgu '((atom (rel P (var x))) (atom (rel P (fn a)))) undefined)
              (update 'x '(fn a) undefined))
;; incompatible relations -> raise
(check-exn exn:fail? (λ () (mgu '((atom (rel P (var x))) (atom (rel Q (fn a)))) undefined)))

;; ===== unifiable: boolean wrapper over unify-literals =====
(check-true (unifiable '(atom (rel P (var x))) '(atom (rel P (fn a)))))
(check-false (unifiable '(atom (rel P (var x))) '(atom (rel Q (fn a)))))
(check-true (unifiable '(not (atom (rel P (var x)))) '(not (atom (rel P (fn a))))))
;; mixed polarity is not unifiable (as literals)
(check-false (unifiable '(atom (rel P)) '(not (atom (rel P)))))

;; ===== rename: prefix every variable of a clause =====
(check-equal? (rename "x"
                      '((atom (rel P (var a)))))
              '((atom (rel P (var xa)))))
(check-equal? (rename "x"
                      '((atom (rel P (var a) (var b)))))
              '((atom (rel P (var xa) (var xb)))))

;; ===== term-match / match-literals: one-way (subsumption) matching =====
;; pattern variables in the FIRST literal are bound to subterms of the second
(check-equal? (match-literals undefined
                              (cons '(atom (rel P (var x) (var y))) '(atom (rel P (fn a) (fn b)))))
              (hash 'x '(fn a) 'y '(fn b)))
;; matching is not symmetric: a constant cannot match a variable
(check-exn exn:fail?
           (λ () (match-literals undefined (cons '(atom (rel P (fn a))) '(atom (rel P (var x)))))))

;; ===== subsumes-clause: does clause1 subsume clause2? =====
(check-true (subsumes-clause '((atom (rel P (var x)))) '((atom (rel P (var x)))))) ; reflexive
(check-true (subsumes-clause '((atom (rel P (var x)))) '((atom (rel P (fn a)))))) ; more general
(check-false (subsumes-clause '((atom (rel P (fn a)))) '((atom (rel P (var x)))))) ; not reverse
;; a shorter clause subsumes a longer one it matches into
(check-true (subsumes-clause '((atom (rel P (var x)))) '((atom (rel P (fn a))) (atom (rel Q)))))
(check-false (subsumes-clause '((atom (rel P (var x))) (atom (rel Q))) '((atom (rel P (fn a))))))

;; ===== resolve-clauses: binary resolution with factoring =====
;; p and ~p resolve to the empty clause
(check-equal? (resolve-clauses '((atom (rel p))) '((not (atom (rel p))))) '(()))
;; clauses with no complementary literals have no resolvents
(check-equal? (resolve-clauses '((atom (rel p))) '((atom (rel q)))) '())

;; ===== replace: drop a clause subsumed by cl, else append cl =====
(check-equal? (replace '((atom (rel P (var x)))) '(((atom (rel P (fn a)))) ((atom (rel Q)))))
              '(((atom (rel P (var x)))) ((atom (rel Q)))))
(check-equal? (replace '((atom (rel R))) '(((atom (rel Q))))) '(((atom (rel Q))) ((atom (rel R)))))

;; ===== incorporate: reject trivial/subsumed clauses, else add via replace =====
;; a tautological clause (p and ~p) is rejected: unused returned unchanged
(check-equal?
 (incorporate '((atom (rel r))) '((not (atom (rel p))) (atom (rel p))) '(((atom (rel s)))))
 '(((atom (rel s)))))
;; a fresh, non-subsumed clause is added to unused
(check-equal? (incorporate '((atom (rel r))) '((atom (rel p))) '(((atom (rel q)))))
              '(((atom (rel q))) ((atom (rel p)))))
;; the empty clause subsumes everything, so any cl is rejected against it
(check-equal? (incorporate '() '((atom (rel p))) '(((atom (rel q))))) '(((atom (rel q)))))

;; ===== end-to-end on known theorems (each refuted disjunct marked #t) =====
(define peirce '(imp (imp (imp (atom (rel P)) (atom (rel Q))) (atom (rel P))) (atom (rel P))))
(define drinker '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y)))))))
(define (all-true? l)
  (andmap (λ (x) (eq? x #t)) l))
(check-true (all-true? (resolution003 peirce)))
(check-true (all-true? (presolution drinker)))
