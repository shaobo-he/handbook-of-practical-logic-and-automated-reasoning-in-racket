#lang racket/base

;; Property tests for prop/dp: the individual DP rules preserve satisfiability,
;; the trail-based solvers (dpli, dplb) agree with dpll, all four SAT/validity
;; procedures agree with the truth-table oracle, and the litabs/backtrack
;; helpers obey their algebraic laws.

(require rackunit
         rackcheck
         racket/match
         "common.rkt")
(require (only-in "../../prop/prop.rkt" satisfiable tautology negate))
(require (only-in "../../prop/bdd.rkt" bddtaut))
(require (only-in "../../prop/defcnf.rkt" defcnfs))
(require (only-in "../../prop/dp.rkt"
                  one-literal-rule
                  affirmative-negative-rule
                  resolution-rule
                  litabs
                  backtrack
                  dpsat
                  dpllsat
                  dplisat
                  dplbsat
                  dptaut
                  dplltaut
                  dplitaut
                  dplbtaut))

;; independent SAT oracle for clause sets: rebuild a formula (a conjunction of
;; disjunctions) and ask the BDD checker. Shares no code with the DP rules.
(define (clause->formula cl)
  (cond
    [(null? cl) #f]
    [(null? (cdr cl)) (car cl)]
    [else `(or ,(car cl) ,(clause->formula (cdr cl)))]))
(define (clauses->formula clauses)
  (cond
    [(null? clauses) #t]
    [(null? (cdr clauses)) (clause->formula (car clauses))]
    [else `(and ,(clause->formula (car clauses)) ,(clauses->formula (cdr clauses)))]))
(define (clauses-sat? clauses)
  (not (bddtaut `(not ,(clauses->formula clauses)))))

;; ===== each DP rule preserves satisfiability of the clause set =====
;; rules return #f when inapplicable; only assert when they actually fired
(check-property mid
                (property ([fm gen:prop])
                          (define clauses (defcnfs fm))
                          (define after (one-literal-rule clauses))
                          (or (not after) (eq? (clauses-sat? clauses) (clauses-sat? after)))))
(check-property mid
                (property ([fm gen:prop])
                          (define clauses (defcnfs fm))
                          (define after (affirmative-negative-rule clauses))
                          (or (not after) (eq? (clauses-sat? clauses) (clauses-sat? after)))))
;; resolution-rule needs a positive literal to resolve on; once the pure-literal
;; rule reports nothing (no pure literals) and the set is non-trivial, every
;; appearing atom has both polarities, so a positive literal exists
(check-property low
                (property ([fm gen:prop])
                          (define clauses (defcnfs fm))
                          (or (null? clauses)
                              (member '() clauses)
                              (affirmative-negative-rule clauses)
                              (let ([after (resolution-rule clauses)])
                                (eq? (clauses-sat? clauses) (clauses-sat? after))))))

;; ===== dpli and dplb agree with dpll (and with truth-table validity) =====
(check-property
 mid
 (property
  ([fm gen:prop])
  (let ([s (satisfiable fm)])
    (and (eq? s (dpsat fm)) (eq? s (dpllsat fm)) (eq? s (dplisat fm)) (eq? s (dplbsat fm))))))
(check-property
 mid
 (property
  ([fm gen:prop])
  (let ([t (tautology fm)])
    (and (eq? t (dptaut fm)) (eq? t (dplltaut fm)) (eq? t (dplitaut fm)) (eq? t (dplbtaut fm))))))

;; ===== litabs strips polarity; double-negating a literal is the identity =====
(define lit-gen
  (gen:one-of '((atom p) (not (atom p)) (atom q) (not (atom q)) (atom r) (not (atom r)))))
(check-property big
                (property ([l lit-gen])
                          (and (equal? (litabs l) (litabs (negate l))) ; both polarities share an atom
                               (equal? (negate (negate l)) l)))) ; negate is an involution

;; ===== backtrack returns a suffix of the trail with no leading deductions =====
(define status-gen (gen:one-of '(guessed deduced)))
(define entry-gen (gen:map (gen:tuple lit-gen status-gen) (λ (ls) (cons (car ls) (cadr ls)))))
(define trail-gen (gen:list entry-gen #:max-length 8))
(define (suffix? xs ys) ; is xs a tail of ys?
  (or (equal? xs ys) (and (pair? ys) (suffix? xs (cdr ys)))))
(check-property big
                (property ([trail trail-gen])
                          (define bt (backtrack trail))
                          (and (suffix? bt trail)
                               ;; head (if any) is a guessed decision, never a deduction
                               (or (null? bt) (eq? (cdr (car bt)) 'guessed)))))
