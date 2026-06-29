#lang racket/base

(require rackunit)
(require racket/set)
(require (only-in "../prop/prop.rkt" tautology satisfiable))
(require "../prop/defcnf.rkt")
(require "../prop/dp.rkt")

;; ===== direct DP on hand-built clause sets =====
;; literals are (atom p) / (not (atom p)); a clause is a list of literals
(check-true (dp '())) ; no clauses -> satisfiable
(check-false (dp (list '()))) ; contains the empty clause -> unsat
(check-true (dp '(((atom p))))) ; single unit clause
;; (p|q)(~p|q)(p|~q)(~p|~q) is unsatisfiable -> exercises the resolution rule
(define unsat-clauses
  '(((atom p) (atom q)) ((not (atom p)) (atom q))
                        ((atom p) (not (atom q)))
                        ((not (atom p)) (not (atom q)))))
(check-false (dp unsat-clauses))
(check-false (dpll unsat-clauses))

;; ===== every procedure must agree with the truth-table reference =====
(define formulas
  (list '(or (atom p) (not (atom p))) ; valid
        '(or (atom p) (atom q)) ; satisfiable, not valid
        '(and (atom p) (not (atom p))) ; unsatisfiable
        '(imp (and (imp (atom p) (atom q)) (imp (atom q) (atom r)))
              (imp (atom p) (atom r))) ; valid (syllogism)
        '(iff (not (and (atom p) (atom q))) (or (not (atom p)) (not (atom q)))) ; valid (De Morgan)
        '(iff (atom p) (and (atom q) (or (atom r) (not (atom p))))) ; contingent
        '(imp (or (atom p) (atom q)) (and (atom p) (atom q))) ; contingent
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
  (check-equal? (satisfiable (defcnf fm))
                (satisfiable fm)
                (format "defcnf changed satisfiability of ~s" fm))
  (check-equal? (satisfiable (defcnf3 fm))
                (satisfiable fm)
                (format "defcnf3 changed satisfiability of ~s" fm)))

;; ===== one-literal (unit) rule =====
;; a unit clause (p) forces p: drop every clause holding p, strike ~p from the rest
(check-equal? (one-literal-rule '(((atom p)) ((not (atom p)) (atom q)))) '(((atom q))))
;; not applicable when there is no unit clause -> #f
(check-false (one-literal-rule '(((atom p) (atom q)) ((not (atom p)) (atom r)))))

;; ===== affirmative-negative (pure literal) rule =====
;; r occurs only positively, so the clause mentioning it is satisfied and dropped;
;; the surviving clauses (which mix both polarities of p and q) are returned in order
(check-equal? (affirmative-negative-rule '(((atom p) (atom q)) ((not (atom p)) (not (atom q)))
                                                               ((atom r) (atom p))))
              '(((atom p) (atom q)) ((not (atom p)) (not (atom q)))))
;; every literal appears in both polarities -> no pure literal -> #f
(check-false (affirmative-negative-rule '(((atom p) (atom q)) ((not (atom p)) (not (atom q))))))

;; ===== resolution heuristic and combinator =====
;; blowup = m*n - m - n, with m/n the count of positive/negative occurrences
(check-equal? (resolution-blowup '(((atom p) (atom a)) ((atom p) (atom b))
                                                       ((not (atom p)) (atom c))
                                                       ((not (atom p)) (atom d))
                                                       ((not (atom p)) (atom e)))
                                 '(atom p))
              1)
;; a literal that does not occur has blowup 0
(check-equal? (resolution-blowup '(((atom q))) '(atom p)) 0)
;; litabs strips a leading negation, leaving positive literals alone
(check-equal? (litabs '(not (atom p))) '(atom p))
(check-equal? (litabs '(atom q)) '(atom q))
;; resolving p combines (p \/ q) with (~p \/ r) into (q \/ r)
(define resolved (resolve-on '(atom p) '(((atom p) (atom q)) ((not (atom p)) (atom r)))))
(check-equal? (length resolved) 1)
(check-equal? (list->set (car resolved)) (set '(atom q) '(atom r)))
;; a tautological resolvent (q \/ ~q) is discarded
(check-equal? (resolve-on '(atom p) '(((atom p) (atom q)) ((not (atom p)) (not (atom q))))) '())

;; ===== trail backtracking =====
;; strip leading 'deduced entries back to the most recent 'guessed decision
(check-equal? (backtrack '(((atom q) . deduced) ((atom r) . deduced) ((atom p) . guessed)))
              '(((atom p) . guessed)))
;; a trail of only deductions backtracks to empty
(check-equal? (backtrack '(((atom p) . deduced) ((atom q) . deduced))) '())
;; a guessed head is already a decision level: the whole trail is left untouched
(check-equal? (backtrack '(((atom p) . guessed) ((atom q) . deduced)))
              '(((atom p) . guessed) ((atom q) . deduced)))

;; ===== unit propagation extends the trail with deductions =====
(let-values ([(cls* trail*) (unit-propagate '(((atom p)) ((atom p) (atom q))) '())])
  (check-equal? trail* (list (cons '(atom p) 'deduced))))

;; ===== iterative solvers agree with dpll on hand-built clause sets =====
(check-false (dpli unsat-clauses '()))
(check-false (dplb unsat-clauses '()))
(check-true (dpli '(((atom p))) '()))
(check-true (dplb '(((atom p))) '()))
(check-true (dpli '(((atom p) (atom q)) ((not (atom p)) (atom q))) '()))
(check-true (dplb '(((atom p) (atom q)) ((not (atom p)) (atom q))) '()))
