#lang racket/base

;; dp --- the Davis-Putnam (DP) and Davis-Putnam-Logemann-Loveland
;; (DPLL) satisfiability procedures, plus the iterative trail-based
;; versions with backtracking (dpli) and backjumping/learning (dplb).
;;
;; Each rule returns #f to signal "rule not applicable" (rather than raising),
;; so they dispatch cleanly with `cond ... =>`.

(require racket/match)
(require racket/set)
(require (only-in racket/list partition filter-map))
(require (only-in "../core/lib.rkt"
                  image
                  unions
                  union
                  subtract
                  intersect
                  allpairs
                  non
                  insert
                  minimize
                  maximize))
(require (only-in "prop.rkt" negate negative positive trivial))
(require (only-in "defcnf.rkt" defcnfs))

(provide (all-defined-out))

;; ===== DP rules (each returns the new clause set, or #f if inapplicable) =====
;; pick any unit clause (u); u must be true, so every clause containing u is
;; satisfied (dropped) and ~u is removed from the clauses that remain.
(define (one-literal-rule clauses)
  (define unit (findf (λ (cl) (= (length cl) 1)) clauses))
  (and unit
       (let* ([u (car unit)]
              [u* (negate u)]
              [kept (filter (λ (cl) (not (member u cl))) clauses)])
         (image (λ (cl) (subtract cl (list u*))) kept))))

(define (affirmative-negative-rule clauses)
  (define-values (neg* pos) (partition negative (unions clauses)))
  (define neg (image negate neg*))
  (define pos-only (subtract pos neg))
  (define neg-only (subtract neg pos))
  (define pure (union pos-only (image negate neg-only)))
  (and (not (null? pure)) (filter (λ (cl) (null? (intersect cl pure))) clauses)))

(define (resolve-on p clauses)
  (define p* (negate p))
  (define-values (pos notpos) (partition (λ (cl) (member p cl)) clauses))
  (define-values (neg other) (partition (λ (cl) (member p* cl)) notpos))
  (define pos* (image (λ (cl) (filter (λ (l) (not (equal? l p))) cl)) pos))
  (define neg* (image (λ (cl) (filter (λ (l) (not (equal? l p*))) cl)) neg))
  (define res0 (allpairs union pos* neg*))
  (union other (filter (non trivial) res0)))

;; net change in clause count from resolving on l: the m*n resolvents minus the
;; m+n source clauses deleted. resolution-rule picks the literal minimising this,
;; to keep the clause set from proliferating.
(define (resolution-blowup cls l)
  (define m (length (filter (λ (cl) (member l cl)) cls)))
  (define n (length (filter (λ (cl) (member (negate l) cl)) cls)))
  (- (* m n) m n))

(define (resolution-rule clauses)
  (define pvs (filter positive (unions clauses)))
  (resolve-on (minimize (λ (l) (resolution-blowup clauses l)) pvs) clauses))

;; ===== DP procedure =====
(define (dp clauses)
  (cond
    [(null? clauses) #t]
    [(member '() clauses) #f]
    [(one-literal-rule clauses)
     =>
     dp]
    [(affirmative-negative-rule clauses)
     =>
     dp]
    [else (dp (resolution-rule clauses))]))

(define (dpsat fm)
  (dp (defcnfs fm)))
(define (dptaut fm)
  (not (dpsat `(not ,fm))))

;; ===== DPLL procedure =====
(define (posneg-count cls l)
  (+ (length (filter (λ (cl) (member l cl)) cls))
     (length (filter (λ (cl) (member (negate l) cl)) cls))))

(define (dpll clauses)
  (cond
    [(null? clauses) #t]
    [(member '() clauses) #f]
    [(one-literal-rule clauses)
     =>
     dpll]
    [(affirmative-negative-rule clauses)
     =>
     dpll]
    [else
     (define pvs (filter positive (unions clauses)))
     (define p (maximize (λ (l) (posneg-count clauses l)) pvs))
     (or (dpll (insert (list p) clauses)) (dpll (insert (list (negate p)) clauses)))]))

(define (dpllsat fm)
  (dpll (defcnfs fm)))
(define (dplltaut fm)
  (not (dpllsat `(not ,fm))))

;; ===== iterative DPLL with an explicit trail =====
;; trail entries are (literal . status) with status 'guessed or 'deduced.
(define (litabs p)
  (match p
    [`(not ,q) q]
    [_ p]))

(define (unassigned cls trail)
  (subtract (unions (image (λ (cl) (image litabs cl)) cls)) (image (λ (e) (litabs (car e))) trail)))

;; fixed-point unit propagation: drop falsified literals, collect clauses that
;; have become unit, add their literals to `assigned` (a set of true literals)
;; and to `trail` (the ordered decision history, as 'deduced), then repeat until
;; no new units appear.
(define (unit-subpropagate cls assigned trail)
  (define cls* (map (λ (cl) (filter (λ (l) (not (set-member? assigned (negate l)))) cl)) cls))
  (define newunits
    (unions (filter-map
             (λ (cl) (and (= (length cl) 1) (not (set-member? assigned (car cl))) (list (car cl))))
             cls*)))
  (if (null? newunits)
      (values cls* assigned trail)
      (unit-subpropagate cls*
                         (foldl (λ (u s) (set-add s u)) assigned newunits)
                         (foldr (λ (p t) (cons (cons p 'deduced) t)) trail newunits))))

(define (unit-propagate cls trail)
  (define assigned (foldl (λ (e s) (set-add s (car e))) (set) trail))
  (define-values (cls* assigned* trail*) (unit-subpropagate cls assigned trail))
  (values cls* trail*))

;; pop deduced literals off the front of the trail, exposing the most recent
;; 'guessed decision (the level to flip when a conflict is hit)
(define (backtrack trail)
  (match trail
    [`((,_ . deduced) . ,tt) (backtrack tt)]
    [_ trail]))

(define (dpli cls trail)
  (define-values (cls* trail*) (unit-propagate cls trail))
  (cond
    [(member '() cls*)
     (match (backtrack trail)
       [`((,p . guessed) . ,tt) (dpli cls (cons (cons (negate p) 'deduced) tt))]
       [_ #f])]
    [else
     (define ps (unassigned cls trail*))
     (if (null? ps)
         #t
         (dpli cls (cons (cons (maximize (λ (l) (posneg-count cls* l)) ps) 'guessed) trail*)))]))

(define (dplisat fm)
  (dpli (defcnfs fm) '()))
(define (dplitaut fm)
  (not (dplisat `(not ,fm))))

;; ===== DPLL with non-chronological backjumping and clause learning =====
(define (backjump cls p trail)
  (match (backtrack trail)
    [`((,q . guessed) . ,tt)
     (define-values (cls* trail*) (unit-propagate cls (cons (cons p 'guessed) tt)))
     (if (member '() cls*)
         (backjump cls p tt)
         trail)]
    [_ trail]))

(define (dplb cls trail)
  (define-values (cls* trail*) (unit-propagate cls trail))
  (cond
    [(member '() cls*)
     (match (backtrack trail)
       [`((,p . guessed) . ,tt)
        (define trail** (backjump cls p tt))
        ;; learn a conflict clause: the negation of the decisions (the guessed
        ;; literals plus p) that led here, so this exact assignment is blocked
        ;; from being re-tried
        (define declits (filter (λ (e) (eq? (cdr e) 'guessed)) trail**))
        (define conflict (insert (negate p) (image (λ (e) (negate (car e))) declits)))
        (dplb (cons conflict cls) (cons (cons (negate p) 'deduced) trail**))]
       [_ #f])]
    [else
     (define ps (unassigned cls trail*))
     (if (null? ps)
         #t
         (dplb cls (cons (cons (maximize (λ (l) (posneg-count cls* l)) ps) 'guessed) trail*)))]))

(define (dplbsat fm)
  (dplb (defcnfs fm) '()))
(define (dplbtaut fm)
  (not (dplbsat `(not ,fm))))
