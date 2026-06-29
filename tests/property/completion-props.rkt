#lang racket/base

;; Property tests for completion: variable renaming of equation pairs,
;; orientation by a term ordering, and interreduction never growing a system.

(require rackunit
         rackcheck
         "common.rkt")
(require (only-in "../../equality/equal.rkt" mk-eq))
(require (only-in "../../equality/completion.rkt" renamepair normalize-and-orient interreduce))
(require (only-in "../../equality/order.rkt" lpo-ge weight))
(require (only-in "../../fol/fol.rkt" fv))
(require (only-in "../../core/lib.rkt" intersect can))

;; ground terms (no variables): the lexicographic path order is total on these,
;; so normalize-and-orient never fails to orient a pair of distinct ground terms.
(define (gterm-gen n)
  (if (<= n 0)
      (gen:one-of '((fn a) (fn b) (fn c)))
      (gen:frequency (list (cons 1 (gen:one-of '((fn a) (fn b) (fn c))))
                           (cons 2 (gen:map (gterm-gen (sub1 n)) (λ (t) `(fn f ,t))))
                           (cons 2
                                 (gen:map (gen:tuple (gterm-gen (sub1 n)) (gterm-gen (sub1 n)))
                                          (λ (st) `(fn g ,(car st) ,(cadr st)))))))))
(define gen:gterm (gterm-gen 2))

;; a precedence-based ordering for orienting equations (a < b < c < f < g)
(define ord (λ (s t) (lpo-ge (λ (p q) (weight '(a b c f g) p q)) s t)))

;; ===== renamepair gives the two equations disjoint variable sets =====
(check-property mid
                (property ([s gen:term] [t gen:term] [u gen:term] [v gen:term])
                          (let-values ([(a b) (renamepair (mk-eq s t) (mk-eq u v))])
                            (null? (intersect (fv a) (fv b))))))

;; ===== normalize-and-orient always returns a pair respecting the ordering =====
;; (the input may be unorientable -- then it raises, which `can` filters out)
(check-property mid
                (property ([s gen:term] [t gen:term])
                          (let ([eq (mk-eq s t)])
                            (or (not (can (λ (e) (normalize-and-orient ord '() e)) eq))
                                (let-values ([(l r) (normalize-and-orient ord '() eq)])
                                  (ord l r))))))

;; ===== interreduce never increases the number of equations =====
;; build a terminating rule set by orienting distinct ground pairs with the LPO;
;; a shared reduction order guarantees rewrite (and hence interreduce) terminates.
(check-property
 low
 (property
  ([pairs (gen:list (gen:tuple gen:gterm gen:gterm) #:max-length 4)])
  (let ([rules (for/list ([st (in-list pairs)]
                          #:unless (equal? (car st) (cadr st)))
                 (let-values ([(l r) (normalize-and-orient ord '() (mk-eq (car st) (cadr st)))])
                   (mk-eq l r)))])
    (<= (length (interreduce '() rules)) (length rules)))))
