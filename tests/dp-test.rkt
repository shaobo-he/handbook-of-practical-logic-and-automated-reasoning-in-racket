#lang racket/base

(require rackunit)
(require (only-in "../prop/prop.rkt" tautology satisfiable))
(require "../prop/defcnf.rkt")
(require "../prop/dp.rkt")

;; ===== direct DP on hand-built clause sets =====
;; literals are (atom p) / (not (atom p)); a clause is a list of literals
(check-true (dp '()))                       ; no clauses -> satisfiable
(check-false (dp (list '())))               ; contains the empty clause -> unsat
(check-true (dp '(((atom p)))))             ; single unit clause
;; (p|q)(~p|q)(p|~q)(~p|~q) is unsatisfiable -> exercises the resolution rule
(define unsat-clauses
  '(((atom p) (atom q))
    ((not (atom p)) (atom q))
    ((atom p) (not (atom q)))
    ((not (atom p)) (not (atom q)))))
(check-false (dp unsat-clauses))
(check-false (dpll unsat-clauses))

;; ===== every procedure must agree with the truth-table reference =====
(define formulas
  (list
   '(or (atom p) (not (atom p)))                                   ; valid
   '(or (atom p) (atom q))                                         ; satisfiable, not valid
   '(and (atom p) (not (atom p)))                                  ; unsatisfiable
   '(imp (and (imp (atom p) (atom q)) (imp (atom q) (atom r)))
         (imp (atom p) (atom r)))                                  ; valid (syllogism)
   '(iff (not (and (atom p) (atom q)))
         (or (not (atom p)) (not (atom q))))                       ; valid (De Morgan)
   '(iff (atom p) (and (atom q) (or (atom r) (not (atom p)))))     ; contingent
   '(imp (or (atom p) (atom q)) (and (atom p) (atom q)))           ; contingent
   ;; unsatisfiable conjunction, drives DP past the easy rules
   '(and (and (or (atom p) (atom q)) (or (not (atom p)) (atom q)))
         (and (or (atom p) (not (atom q))) (or (not (atom p)) (not (atom q)))))))

(define taut-procs (list dptaut dplltaut dplitaut dplbtaut))
(define sat-procs (list dpsat dpllsat dplisat dplbsat))

(for ([fm (in-list formulas)])
  (define t (tautology fm))
  (define s (satisfiable fm))
  (for ([p (in-list taut-procs)])
    (check-equal? (p fm) t (format "tautology disagreement on ~s" fm)))
  (for ([p (in-list sat-procs)])
    (check-equal? (p fm) s (format "satisfiability disagreement on ~s" fm))))

;; ===== defcnf is equisatisfiable with its input (not equivalent) =====
(for ([fm (in-list formulas)])
  (check-equal? (satisfiable (defcnf fm)) (satisfiable fm)
                (format "defcnf changed satisfiability of ~s" fm))
  (check-equal? (satisfiable (defcnf3 fm)) (satisfiable fm)
                (format "defcnf3 changed satisfiability of ~s" fm)))
