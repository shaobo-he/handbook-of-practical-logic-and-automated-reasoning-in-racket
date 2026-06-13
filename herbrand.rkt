#lang racket/base

;; herbrand.fs --- the link between first-order and propositional logic:
;; Herbrand's theorem realized as ground-instance enumeration, giving a
;; Gilmore procedure and a first-order Davis-Putnam procedure.

(require racket/match)
(require (only-in racket/list partition range))
(require (only-in "lib.rkt" allpairs image union non fpf))
(require (only-in "prop.rkt" eval simpdnf simpcnf trivial distrib))
(require (only-in "fol.rkt" functions subst fv generalize))
(require (only-in "skolem.rkt" skolemize))
(require (only-in "dp.rkt" dpll))

(provide (all-defined-out))

;; when #t, herbloop reports progress (matches Harrison's printout)
(define herbrand-verbose (make-parameter #f))

;; ===== propositional valuation of a first-order atom set =====
(define (pholds d fm) (eval fm (λ (p) (d `(atom ,p)))))

;; ===== Herbrand universe: constants and functions =====
(define (herbfuns fm)
  (define-values (cns fns) (partition (λ (fa) (= (cdr fa) 0)) (functions fm)))
  (if (null? cns) (values (list '(c . 0)) fns) (values cns fns)))

;; ===== enumeration of ground terms and m-tuples =====
(define (groundterms cntms funcs n)
  (if (= n 0)
      cntms
      (foldr (λ (fa acc)
               (append (map (λ (args) `(fn ,(car fa) ,@args))
                            (groundtuples cntms funcs (- n 1) (cdr fa)))
                       acc))
             '() funcs)))

(define (groundtuples cntms funcs n m)
  (if (= m 0)
      (if (= n 0) (list '()) '())
      (foldr (λ (k acc)
               (append (allpairs cons
                                 (groundterms cntms funcs k)
                                 (groundtuples cntms funcs (- n k) (- m 1)))
                       acc))
             '() (range 0 (add1 n)))))

;; ===== iterate mfn over ground instances until tfn fails =====
(define (herbloop mfn tfn fl0 cntms funcs fvs n fl tried tuples)
  (when (herbrand-verbose)
    (printf "~a ground instances tried; ~a items in list.\n" (length tried) (length fl)))
  (match tuples
    ['()
     (define newtups (groundtuples cntms funcs n (length fvs)))
     (herbloop mfn tfn fl0 cntms funcs fvs (add1 n) fl tried newtups)]
    [(cons tup tups)
     (define fl* (mfn fl0 (λ (f) (subst (fpf fvs tup) f)) fl))
     (if (not (tfn fl*))
         (cons tup tried)
         (herbloop mfn tfn fl0 cntms funcs fvs n fl* (cons tup tried) tups))]))

;; ===== Gilmore procedure (DNF, stop when the disjunction collapses) =====
(define (gilmore-mfn djs0 ifn djs)
  (filter (non trivial) (distrib (image (λ (d) (image ifn d)) djs0) djs)))

(define (gilmore-loop djs0 cntms funcs fvs n fl tried tuples)
  (herbloop gilmore-mfn (λ (djs) (not (null? djs)))
            djs0 cntms funcs fvs n fl tried tuples))

(define (gilmore fm)
  (define sfm (skolemize `(not ,(generalize fm))))
  (define fvs (fv sfm))
  (define-values (consts funcs) (herbfuns sfm))
  (define cntms (image (λ (c) `(fn ,(car c))) consts))
  (length (gilmore-loop (simpdnf sfm) cntms funcs fvs 0 (list '()) '() '())))

;; ===== first-order Davis-Putnam (CNF, stop when ground set is unsat) =====
(define (dp-mfn cjs0 ifn cjs)
  (union (image (λ (c) (image ifn c)) cjs0) cjs))

(define (dp-loop cjs0 cntms funcs fvs n cjs tried tuples)
  (herbloop dp-mfn dpll cjs0 cntms funcs fvs n cjs tried tuples))

(define (davisputnam fm)
  (define sfm (skolemize `(not ,(generalize fm))))
  (define fvs (fv sfm))
  (define-values (consts funcs) (herbfuns sfm))
  (define cntms (image (λ (c) `(fn ,(car c))) consts))
  (length (dp-loop (simpcnf sfm) cntms funcs fvs 0 '() '() '())))

;; ===== refine: keep only the instances actually needed =====
(define (dp-refine cjs0 fvs dunno need)
  (match dunno
    ['() need]
    [(cons cl dknow)
     (define (mfn tup acc) (dp-mfn cjs0 (λ (f) (subst (fpf fvs tup) f)) acc))
     (define need*
       (if (dpll (foldr mfn '() (append need dknow)))
           (cons cl need)
           need))
     (dp-refine cjs0 fvs dknow need*)]))

(define (dp-refine-loop cjs0 cntms funcs fvs n cjs tried tuples)
  (dp-refine cjs0 fvs (dp-loop cjs0 cntms funcs fvs n cjs tried tuples) '()))

(define (davisputnam002 fm)
  (define sfm (skolemize `(not ,(generalize fm))))
  (define fvs (fv sfm))
  (define-values (consts funcs) (herbfuns sfm))
  (define cntms (image (λ (c) `(fn ,(car c))) consts))
  (length (dp-refine-loop (simpcnf sfm) cntms funcs fvs 0 '() '() '())))
