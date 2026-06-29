#lang racket/base

;; Unit tests for prop/defcnf: fresh-variable generation, the memoizing
;; definitional-CNF core (maincnf/defstep), counter initialisation that avoids
;; clashing with p_* atoms already present, and the 3-CNF clause-size bound.

(require rackunit)
(require racket/match)
(require (only-in "../prop/prop.rkt" atoms satisfiable))
(require (only-in "../core/formulas.rkt" conjuncts disjuncts))
(require "../prop/defcnf.rkt")

;; clauses of a CNF formula: a conjunction of disjunctions of literals
(define (clauses-of fm)
  (map disjuncts (conjuncts fm)))

;; a literal is an atom or a negated atom
(define (literal? lit)
  (match lit
    [`(atom ,_) #t]
    [`(not (atom ,_)) #t]
    [_ #f]))

;; ===== mkprop! generates sequential p_<n> atoms and bumps the counter =====
(define c0 (box 0))
(check-equal? (mkprop! c0) '(atom p_0))
(check-equal? (mkprop! c0) '(atom p_1))
(check-equal? (unbox c0) 2)

;; ===== var-index extracts the numeric suffix of a p_<k> atom (else 0) =====
(check-equal? (var-index "p_" 'p_42) 42)
(check-equal? (var-index "p_" 'q) 0) ; wrong prefix
(check-equal? (var-index "p_" 'p_) 0) ; empty suffix
(check-equal? (var-index "p_" 'p_0) 0)
(check-equal? (var-index "p_" 'p_007) 7) ; leading zeros are fine
(check-equal? (var-index "p_" 'p_x) 0) ; non-numeric suffix

;; ===== maincnf leaves literals untouched =====
(check-equal? (maincnf '(atom p) (make-hash) (box 0)) '(atom p))
(check-equal? (maincnf '(not (atom p)) (make-hash) (box 0)) '(not (atom p)))

;; ===== maincnf replaces a connective with a fresh var and records its def =====
(let ([defs (make-hash)]
      [counter (box 0)])
  (check-equal? (maincnf '(and (atom p) (atom q)) defs counter) '(atom p_0))
  (check-equal? (hash-count defs) 1)
  ;; defs maps the subformula to (fresh-var . (iff fresh-var subformula))
  (check-equal? (hash-ref defs '(and (atom p) (atom q)))
                (cons '(atom p_0) '(iff (atom p_0) (and (atom p) (atom q))))))

;; ===== a repeated subformula is memoised to a single fresh variable =====
(let ([defs (make-hash)]
      [counter (box 0)])
  (maincnf '(and (and (atom p) (atom q)) (and (atom p) (atom q))) defs counter)
  ;; only two defs: the shared inner /\ (p_0) and the outer /\ (p_1)
  (check-equal? (hash-count defs) 2)
  (check-equal? (car (hash-ref defs '(and (atom p) (atom q)))) '(atom p_0)))

;; ===== the counter starts past the largest p_<k> already in the input =====
;; input mentions p_5, so the first fresh variable is p_6, never p_0..p_5
(let ([out (defcnf '(iff (atom p_5) (atom q)))])
  (check-true (and (memq 'p_6 (atoms out)) #t))
  (check-false (memq 'p_0 (atoms out)))
  (check-false (ormap (λ (a) (and (memq a '(p_0 p_1 p_2 p_3 p_4)) #t)) (atoms out))))

;; ===== defcnf3 guarantees clauses of at most three literals =====
(for ([fm (in-list (list '(iff (atom p) (iff (atom q) (atom r)))
                         '(iff (atom p) (and (atom q) (atom r)))
                         '(or (and (atom p) (atom q)) (and (atom r) (atom p)))
                         '(imp (iff (atom p) (atom q)) (iff (atom q) (atom r)))))])
  (for ([cl (in-list (clauses-of (defcnf3 fm)))])
    (check-true (<= (length cl) 3) (format "defcnf3 clause too big: ~s" cl))))

;; ===== defcnf / defcnf3 / defcnf-orig are equisatisfiable with the input =====
(for ([fm (in-list (list '(iff (atom p) (and (atom q) (atom r)))
                         '(and (or (atom p) (atom q))
                               (and (or (not (atom p)) (atom q))
                                    (and (or (atom p) (not (atom q)))
                                         (or (not (atom p)) (not (atom q))))))
                         '(imp (atom p) (or (atom p) (atom q)))))])
  (check-equal? (satisfiable (defcnf fm)) (satisfiable fm))
  (check-equal? (satisfiable (defcnf3 fm)) (satisfiable fm))
  (check-equal? (satisfiable (defcnf-orig fm)) (satisfiable fm)))

;; ===== defcnfs yields a clause set (list of literal lists) =====
(let ([cs (defcnfs '(iff (atom a) (atom b)))])
  (check-true (list? cs))
  (check-true (andmap list? cs))
  ;; every leaf is a literal: an atom or a negated atom
  (check-true (andmap (λ (cl) (andmap literal? cl)) cs)))
