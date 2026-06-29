#lang racket/base

;; Unit tests for prop/stal (Stalmarck's method): the literal ordering
;; prop-atom<?, double-negation cleanup ddnegate, trigger generation, the
;; triplet (Tseitin) transform, and completeness on tautologies that fall
;; within the depth-2 "easiness" limit.

(require rackunit)
(require (only-in "../prop/prop.rkt" satisfiable))
(require (only-in "../core/formulas.rkt" list-conj))
(require (only-in "../prop/propexamples.rkt" mk-adder-test))
(require "../prop/stal.rkt")

;; ===== prop-atom<?: a strict total order with #t as the least element =====
(check-true (prop-atom<? '(atom p) '(atom q)))
(check-false (prop-atom<? '(atom q) '(atom p)))
(check-false (prop-atom<? '(atom p) '(atom p))) ; irreflexive
(check-true (prop-atom<? #t '(atom p))) ; #t precedes every atom
(check-false (prop-atom<? '(atom p) #t))
(check-false (prop-atom<? #t #t))

;; ===== ddnegate: cancel a double negation, leave everything else alone =====
(check-equal? (ddnegate '(not (not (atom p)))) '(atom p))
(check-equal? (ddnegate '(atom p)) '(atom p))
(check-equal? (ddnegate '(not (atom p))) '(not (atom p)))

;; ===== triggers: each standard triplet yields a non-empty trigger table =====
(define tand (triggers '(iff (atom p) (and (atom q) (atom r)))))
(check-true (pair? tand))
;; every entry pairs an equation with a non-empty list of consequences
(check-true (andmap (λ (e) (pair? (cdr e))) tand))

;; ===== triplicate: Tseitin transform preserves satisfiability =====
;; the conjunction of the root variable with its definitions is satisfiable iff
;; the original formula is
(let-values ([(p triplets) (triplicate '(or (atom p) (atom q)))])
  (check-true (satisfiable (list-conj (cons p triplets)))))
(let-values ([(p triplets) (triplicate '(and (atom p) (not (atom p))))])
  (check-false (satisfiable (list-conj (cons p triplets)))))

;; ===== stalmarck is complete on depth-2-easy tautologies (returns #t) =====
(for ([fm (in-list
           (list '(imp (atom p) (atom p))
                 '(or (atom p) (not (atom p)))
                 '(imp (and (atom p) (imp (atom p) (atom q))) (atom q)) ; modus ponens
                 '(iff (and (atom p) (atom q)) (and (atom q) (atom p))) ; commutativity
                 '(imp (and (atom p) (atom q)) (atom p))
                 '(imp (imp (not (atom p)) (not (atom q))) (imp (atom q) (atom p))) ; contraposition
                 '(iff (not (and (atom p) (atom q))) (or (not (atom p)) (not (atom q)))) ; De Morgan
                 '(imp (and (imp (atom p) (atom q)) (imp (atom q) (atom r)))
                       (imp (atom p) (atom r)))))]) ; transitivity
  (check-true (stalmarck fm) (format "stalmarck failed to prove ~s" fm)))
(check-true (stalmarck (mk-adder-test 2 1)))

;; ===== stalmarck raises (rather than returning #f) on a non-tautology =====
(check-exn exn:fail? (λ () (stalmarck '(or (atom p) (atom q)))))
(check-exn exn:fail? (λ () (stalmarck '(imp (or (atom p) (atom q)) (and (atom p) (atom q))))))
