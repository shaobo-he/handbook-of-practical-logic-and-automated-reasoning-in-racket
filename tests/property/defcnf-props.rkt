#lang racket/base

;; Property tests for prop/defcnf: definitional CNF preserves satisfiability
;; (cross-checked with an independent BDD oracle), fresh variables never clash
;; with p_* atoms already in the input, defcnf3 stays within 3 literals per
;; clause, and mkprop!/var-index round-trip.

(require rackunit
         rackcheck
         racket/list
         "common.rkt")
(require (only-in "../../prop/prop.rkt" satisfiable))
(require (only-in "../../prop/bdd.rkt" bddtaut))
(require (only-in "../../prop/defcnf.rkt" defcnf defcnf3 defcnf-orig mkprop! var-index))
(require (only-in "../../core/formulas.rkt" conjuncts disjuncts))

;; independent satisfiability oracle: a formula is satisfiable iff its negation
;; is not a tautology. bddtaut shares no code with the defcnf pipeline, so it is
;; a fair referee for the (large, fresh-variable-laden) CNF output.
(define (bddsat fm)
  (not (bddtaut `(not ,fm))))

(define (clauses-of fm)
  (map disjuncts (conjuncts fm)))

;; ===== defcnf / defcnf3 / defcnf-orig are equisatisfiable with the input =====
(check-property big (property ([fm gen:prop]) (eq? (bddsat (defcnf fm)) (satisfiable fm))))
(check-property big (property ([fm gen:prop]) (eq? (bddsat (defcnf3 fm)) (satisfiable fm))))
(check-property big (property ([fm gen:prop]) (eq? (bddsat (defcnf-orig fm)) (satisfiable fm))))

;; ===== fresh-variable non-collision: inputs may already use p_* atoms =====
;; if the counter were not started past the largest existing p_<k>, a fresh
;; variable would alias an input atom and break equisatisfiability. Generating
;; over p_0/p_1 alongside p/q stresses exactly that.
(define gen:prop-pvars (prop-gen-over '((atom p) (atom q) (atom p_0) (atom p_1)) 4))
(check-property mid (property ([fm gen:prop-pvars]) (eq? (bddsat (defcnf fm)) (satisfiable fm))))
(check-property mid (property ([fm gen:prop-pvars]) (eq? (bddsat (defcnf3 fm)) (satisfiable fm))))

;; ===== defcnf3 never emits a clause with more than three literals =====
(check-property mid
                (property ([fm gen:prop])
                          (andmap (λ (cl) (<= (length cl) 3)) (clauses-of (defcnf3 fm)))))

;; ===== mkprop!/var-index round-trip and distinctness =====
(define gen:counter-start (gen:integer-in 0 100000))
;; the n-th fresh variable is p_<n>, and var-index recovers n
(check-property low
                (property ([n gen:counter-start]) (= (var-index "p_" (cadr (mkprop! (box n)))) n)))
;; ten successive calls on one counter yield ten distinct atoms
(check-property low
                (property ([n gen:counter-start])
                          (let ([c (box n)])
                            (= 10
                               (length (remove-duplicates (for/list ([i (in-range 10)])
                                                            (mkprop! c))))))))
