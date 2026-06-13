#lang racket/base

;; prop.fs --- propositional logic: evaluation, truth tables, tautology
;; checking, simplification, NNF/NENF, and DNF/CNF.

(require racket/match)
(require (only-in racket/list partition))
(require (only-in "../core/lib.rkt"
                  tryapplyd setify union subtract intersect image psubset allpairs non))
(require "../core/formulas.rkt")

(provide (all-defined-out))

;; ===== evaluation =====
;; v : atom -> boolean
(define (eval fm v)
  (match fm
    [#t #t]
    [#f #f]
    [`(atom ,x) (v x)]
    [`(not ,p) (not (eval p v))]
    [`(and ,p ,q) (and (eval p v) (eval q v))]
    [`(or ,p ,q) (or (eval p v) (eval q v))]
    [`(imp ,p ,q) (or (not (eval p v)) (eval q v))]
    [`(iff ,p ,q) (eq? (eval p v) (eval q v))]))

(define (atoms fm) (atom-union (λ (a) (list a)) fm))

;; run subfn on every valuation of ats, conjoining the results
(define (onallvaluations subfn v ats)
  (match ats
    ['() (subfn v)]
    [(cons p ps)
     (define (v^ t) (λ (q) (if (equal? q p) t (v q))))
     (and (onallvaluations subfn (v^ #f) ps)
          (onallvaluations subfn (v^ #t) ps))]))

(define (tautology fm)
  (onallvaluations (λ (v) (eval fm v)) (λ (s) #f) (atoms fm)))

(define (unsatisfiable fm) (tautology `(not ,fm)))
(define (satisfiable fm) (not (unsatisfiable fm)))

;; ===== truth tables =====
(define (print-truthtable fm)
  (define ats (atoms fm))
  (define (a->s a) (format "~a" a))
  (define width (add1 (foldl (λ (a w) (max w (string-length (a->s a)))) 5 ats)))
  (define (fixw s) (string-append s (make-string (max 0 (- width (string-length s))) #\space)))
  (define (truth b) (fixw (if b "true" "false")))
  (define (row v)
    (displayln (string-append (apply string-append (map (λ (x) (truth (v x))) ats))
                              "| " (truth (eval fm v))))
    #t)
  (define header (string-append (apply string-append (map (λ (a) (fixw (a->s a))) ats)) "| formula"))
  (define sep (make-string (string-length header) #\-))
  (displayln header)
  (displayln sep)
  (onallvaluations row (λ (s) #f) ats)
  (displayln sep)
  (void))

;; ===== substitution into atoms =====
;; subfn : atom -> formula (partial)
(define (psubst subfn fm)
  (onatoms (λ (p) (tryapplyd subfn p `(atom ,p))) fm))

;; ===== duality =====
(define (dual fm)
  (match fm
    [#f #t]
    [#t #f]
    [`(atom ,p) fm]
    [`(not ,p) `(not ,(dual p))]
    [`(and ,p ,q) `(or ,(dual p) ,(dual q))]
    [`(or ,p ,q) `(and ,(dual p) ,(dual q))]
    [_ (error 'dual "formula involves ==> or <=>")]))

;; ===== simplification =====
(define (psimplify1 fm)
  (define (v o v1 v2 v3)
    (match o
      ['and v1]
      ['or v2]
      ['iff v3]))
  (match fm
    ['(not #f) #t]
    ['(not #t) #f]
    [`(not (not ,p)) p]
    [(cons (and o (or 'and 'or 'iff)) (or (list p #f) (list #f p))) (v o #f p `(not ,p))]
    [(cons (and o (or 'and 'or 'iff)) (or (list p #t) (list #t p))) (v o p #t p)]
    [(cons 'imp (or (list #f p) (list p #t))) #t]
    [`(imp #t ,p) p]
    [`(imp ,p #f) `(not ,p)]
    [_ fm]))

(define (psimplify fm)
  (match fm
    [`(not ,p) (psimplify1 `(not ,(psimplify p)))]
    [(list (and o (or 'and 'or 'imp 'iff)) p q) (psimplify1 `(,o ,(psimplify p) ,(psimplify q)))]
    [_ fm]))

;; ===== literals =====
(define (negative fm) (match fm [`(not ,p) #t] [_ #f]))
(define (positive lit) (not (negative lit)))
(define (negate fm) (match fm [`(not ,p) p] [_ `(not ,fm)]))

;; ===== negation normal form =====
(define (nnf-raw fm)
  (match fm
    [`(and ,p ,q) `(and ,(nnf-raw p) ,(nnf-raw q))]
    [`(or ,p ,q) `(or ,(nnf-raw p) ,(nnf-raw q))]
    [`(imp ,p ,q) `(or ,(nnf-raw `(not ,p)) ,(nnf-raw q))]
    [`(iff ,p ,q) `(or (and ,(nnf-raw p) ,(nnf-raw q)) (and ,(nnf-raw `(not ,p)) ,(nnf-raw `(not ,q))))]
    [`(not (not ,p)) (nnf-raw p)]
    [`(not (and ,p ,q)) `(or ,(nnf-raw `(not ,p)) ,(nnf-raw `(not ,q)))]
    [`(not (or ,p ,q)) `(and ,(nnf-raw `(not ,p)) ,(nnf-raw `(not ,q)))]
    [`(not (imp ,p ,q)) `(and ,(nnf-raw p) ,(nnf-raw `(not ,q)))]
    [`(not (iff ,p ,q)) `(or (and ,(nnf-raw p) ,(nnf-raw `(not ,q))) (and ,(nnf-raw `(not ,p)) ,(nnf-raw q)))]
    [_ fm]))

(define (nnf fm) (nnf-raw (psimplify fm)))

;; negation normal form keeping <=> (used by definitional CNF)
(define (nenf-raw fm)
  (match fm
    [`(not (not ,p)) (nenf-raw p)]
    [`(not (and ,p ,q)) `(or ,(nenf-raw `(not ,p)) ,(nenf-raw `(not ,q)))]
    [`(not (or ,p ,q)) `(and ,(nenf-raw `(not ,p)) ,(nenf-raw `(not ,q)))]
    [`(not (imp ,p ,q)) `(and ,(nenf-raw p) ,(nenf-raw `(not ,q)))]
    [`(not (iff ,p ,q)) `(iff ,(nenf-raw p) ,(nenf-raw `(not ,q)))]
    [`(and ,p ,q) `(and ,(nenf-raw p) ,(nenf-raw q))]
    [`(or ,p ,q) `(or ,(nenf-raw p) ,(nenf-raw q))]
    [`(imp ,p ,q) `(or ,(nenf-raw `(not ,p)) ,(nenf-raw q))]
    [`(iff ,p ,q) `(iff ,(nenf-raw p) ,(nenf-raw q))]
    [_ fm]))

(define (nenf fm) (nenf-raw (psimplify fm)))

;; ===== satisfying valuations / literal lists =====
(define (mk-lits pvs v)
  (list-conj (map (λ (p) (if (eval p v) p `(not ,p))) pvs)))

(define (allsatvaluations subfn v pvs)
  (match pvs
    ['() (if (subfn v) (list v) '())]
    [(cons p ps)
     (define (v^ t) (λ (q) (if (equal? q p) t (v q))))
     (append (allsatvaluations subfn (v^ #f) ps)
             (allsatvaluations subfn (v^ #t) ps))]))

;; ===== disjunctive / conjunctive normal form (set-of-sets) =====
(define (distrib s1 s2) (setify (allpairs union s1 s2)))

(define (purednf fm)
  (match fm
    [`(and ,p ,q) (distrib (purednf p) (purednf q))]
    [`(or ,p ,q) (union (purednf p) (purednf q))]
    [_ (list (list fm))]))

;; formula-level distribution (the raw, non-set version)
(define (distrib-fm fm)
  (match fm
    [`(and ,p (or ,q ,r)) `(or ,(distrib-fm `(and ,p ,q)) ,(distrib-fm `(and ,p ,r)))]
    [`(and (or ,p ,q) ,r) `(or ,(distrib-fm `(and ,p ,r)) ,(distrib-fm `(and ,q ,r)))]
    [_ fm]))

(define (rawdnf fm)
  (match fm
    [`(and ,p ,q) (distrib-fm `(and ,(rawdnf p) ,(rawdnf q)))]
    [`(or ,p ,q) `(or ,(rawdnf p) ,(rawdnf q))]
    [_ fm]))

;; a clause is trivially true/false if it contains a literal and its negation
(define (trivial lits)
  (define-values (pos neg) (partition positive lits))
  (not (null? (intersect pos (image negate neg)))))

(define (simpdnf fm)
  (cond
    [(equal? fm #f) '()]
    [(equal? fm #t) (list '())]
    [else
     (define djs (filter (non trivial) (purednf (nnf fm))))
     (filter (λ (d) (not (ormap (λ (d^) (psubset d^ d)) djs))) djs)]))

(define (dnf fm) (list-disj (map list-conj (simpdnf fm))))

(define (purecnf fm) (image (λ (c) (image negate c)) (purednf (nnf `(not ,fm)))))

(define (simpcnf fm)
  (cond
    [(equal? fm #f) (list '())]
    [(equal? fm #t) '()]
    [else
     (define cjs (filter (non trivial) (purecnf fm)))
     (filter (λ (c) (not (ormap (λ (c^) (psubset c^ c)) cjs))) cjs)]))

(define (cnf fm) (list-conj (map list-disj (simpcnf fm))))

;; ===== printing propositional formulas =====
(define (print-propvar prec p) (symbol->string p))
(define (prop-formula->string fm) (formula->string print-propvar fm))
(define (print-prop-formula fm) (display (string-append "<<" (prop-formula->string fm) ">>")))
