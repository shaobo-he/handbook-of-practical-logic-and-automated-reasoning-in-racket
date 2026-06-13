#lang racket/base

;; completion.fs --- Knuth-Bendix completion: critical pairs, orientation
;; by a term ordering, the completion loop (deferring non-orientable
;; equations), and interreduction.

(require racket/match)
(require (only-in racket/list range))
(require (only-in "../core/lib.rkt" chop-list fpf unions union subtract allpairs can))
(require (only-in "../core/formulas.rkt" list-conj))
(require (only-in "../fol/fol.rkt" fv subst))
(require (only-in "../fol/unif.rkt" fullunify))
(require (only-in "equal.rkt" mk-eq dest-eq))
(require (only-in "rewrite.rkt" rewrite))
(require (only-in "order.rkt" lpo-ge weight))

(provide (all-defined-out))

(define completion-verbose (make-parameter #f))

;; ===== rename the variables of two equations apart =====
(define (renamepair fm1 fm2)
  (define fvs1 (fv fm1))
  (define fvs2 (fv fm2))
  (define-values (nms1 nms2)
    (chop-list (length fvs1)
               (map (λ (n) `(var ,(string->symbol (string-append "x" (number->string n)))))
                    (range 0 (+ (length fvs1) (length fvs2))))))
  (values (subst (fpf fvs1 nms1) fm1) (subst (fpf fvs2 nms2) fm2)))

;; ===== critical pairs via unification-based overlap =====
(define (listcases fn rfn lis acc)
  (match lis
    ['() acc]
    [(cons h t)
     (append (fn h (λ (i h*) (rfn i (cons h* t))))
             (listcases fn (λ (i t*) (rfn i (cons h t*))) t acc))]))

(define (overlaps lr tm rfn)
  (define l (car lr))
  (define r (cdr lr))
  (match tm
    [`(var ,x) '()]
    [`(fn ,f ,@args)
     (listcases (λ (t rf) (overlaps lr t rf))
                (λ (i a) (rfn i `(fn ,f ,@a)))
                args
                (with-handlers ([exn:fail? (λ (e) '())])
                  (list (rfn (fullunify (list (cons l tm))) r))))]))

(define (crit1 eq1 eq2)
  (match* (eq1 eq2)
    [(`(atom (rel = ,l1 ,r1)) `(atom (rel = ,l2 ,r2)))
     (overlaps (cons l1 r1) l2 (λ (i t) (subst i (mk-eq t r2))))]))

(define (critical-pairs fma fmb)
  (define-values (fm1 fm2) (renamepair fma fmb))
  (if (equal? fma fmb)
      (crit1 fm1 fm2)
      (union (crit1 fm1 fm2) (crit1 fm2 fm1))))

;; ===== orient an equation by the ordering, normalizing first =====
(define (normalize-and-orient ord eqs eq)
  (match eq
    [`(atom (rel = ,s ,t))
     (define s* (rewrite eqs s))
     (define t* (rewrite eqs t))
     (cond
       [(ord s* t*) (values s* t*)]
       [(ord t* s*) (values t* s*)]
       [else (error 'normalize-and-orient "Can't orient equation")])]))

(define (status trip eqs0)
  (define eqs (car trip))
  (define def (cadr trip))
  (define crs (caddr trip))
  (when (and (completion-verbose)
             (not (and (equal? eqs eqs0) (not (= 0 (modulo (length crs) 1000))))))
    (printf "~a equations and ~a pending critical pairs + ~a deferred\n"
            (length eqs)
            (length crs)
            (length def))))

;; ===== completion main loop (trip = (list eqs deferred crits)) =====
(define (complete ord trip)
  (define eqs (car trip))
  (define def (cadr trip))
  (define crits (caddr trip))
  (match crits
    [(cons eq ocrits)
     (define trip*
       (with-handlers ([exn:fail? (λ (e) (list eqs (cons eq def) ocrits))])
         (define-values (s* t*) (normalize-and-orient ord eqs eq))
         (if (equal? s* t*)
             (list eqs def ocrits)
             (let ()
               (define eq* (mk-eq s* t*))
               (define eqs* (cons eq* eqs))
               (list eqs*
                     def
                     (append ocrits
                             (foldr (λ (e acc) (append (critical-pairs eq* e) acc)) '() eqs*)))))))
     (status trip* eqs)
     (complete ord trip*)]
    ['()
     (if (null? def)
         eqs
         (let ([e (findf (λ (e) (can (λ (x) (normalize-and-orient ord eqs x)) e)) def)])
           (complete ord (list eqs (subtract def (list e)) (list e)))))]))

;; ===== interreduction =====
(define (interreduce dun eqs)
  (match eqs
    ['() (reverse dun)]
    [(cons `(atom (rel = ,l ,r)) oeqs)
     (define dun*
       (if (not (equal? (rewrite (append dun oeqs) l) l))
           dun
           (cons (mk-eq l (rewrite (append dun eqs) r)) dun)))
     (interreduce dun* oeqs)]))

(define (complete-and-simplify wts eqs)
  (define (ord s t)
    (lpo-ge (λ (p q) (weight wts p q)) s t))
  (define eqs*
    (map (λ (e)
           (define-values (l r) (normalize-and-orient ord '() e))
           (mk-eq l r))
         eqs))
  (interreduce '() (complete ord (list eqs* '() (unions (allpairs critical-pairs eqs* eqs*))))))
