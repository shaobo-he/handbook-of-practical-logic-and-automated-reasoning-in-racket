#lang racket/base

;; tableaux.fs --- a Prawitz-style procedure and an analytic tableau
;; procedure with unification and iterative deepening.

(require racket/match)
(require (only-in racket/list partition range))
(require (only-in "../core/lib.rkt" allpairs image fpf update undefined tryfind))
(require (only-in "../prop/prop.rkt" negate positive simpdnf distrib))
(require (only-in "fol.rkt" subst fv generalize))
(require (only-in "skolem.rkt" skolemize askolemize))
(require (only-in "herbrand.rkt" davisputnam))
(require (only-in "unif.rkt" unify))

(provide (all-defined-out))

;; ===== unify literals (treat the leading relation like a function) =====
(define (unify-literals env tmp)
  (match tmp
    [(cons `(atom (rel ,p1 ,@a1)) `(atom (rel ,p2 ,@a2)))
     (unify env (list (cons `(fn ,p1 ,@a1) `(fn ,p2 ,@a2))))]
    [(cons `(not ,p) `(not ,q)) (unify-literals env (cons p q))]
    [(cons #f #f) env]
    [_ (error 'unify-literals "Can't unify literals")]))

(define (unify-complements env pq)
  (unify-literals env (cons (car pq) (negate (cdr pq)))))

;; ===== Prawitz-style procedure (unification on DNF) =====
(define (unify-refute djs acc)
  (match djs
    ['() acc]
    [(cons head tail)
     (define-values (pos neg) (partition positive head))
     (tryfind (λ (pq) (unify-refute tail (unify-complements acc pq)))
              (allpairs cons pos neg))]))

(define (prawitz-loop djs0 fvs djs n)
  (define l (length fvs))
  (define newvars
    (map (λ (k) (string->symbol (string-append "_" (number->string (+ (* n l) k)))))
         (range 1 (add1 l))))
  (define inst (fpf fvs (map (λ (x) `(var ,x)) newvars)))
  (define djs1 (distrib (image (λ (d) (image (λ (lit) (subst inst lit)) d)) djs0) djs))
  (with-handlers ([exn:fail? (λ (e) (prawitz-loop djs0 fvs djs1 (add1 n)))])
    (cons (unify-refute djs1 undefined) (add1 n))))

(define (prawitz fm)
  (define fm0 (skolemize `(not ,(generalize fm))))
  (cdr (prawitz-loop (simpdnf fm0) (fv fm0) (list '()) 0)))

;; number of ground instances: prawitz vs. first-order Davis-Putnam
(define (compare-instances fm) (cons (prawitz fm) (davisputnam fm)))

;; ===== analytic tableau, doing DNF incrementally =====
;; cont takes (env k); env is the current unifier, k the fresh-var counter
(define (tableau fms lits n cont env k)
  (if (< n 0)
      (error 'tableau "no proof at this level")
      (match fms
        ['() (error 'tableau "tableau: no proof")]
        [(cons `(and ,p ,q) unexp)
         (tableau (cons p (cons q unexp)) lits n cont env k)]
        [(cons `(or ,p ,q) unexp)
         (tableau (cons p unexp) lits n
                  (λ (env k) (tableau (cons q unexp) lits n cont env k))
                  env k)]
        [(cons `(forall ,x ,p) unexp)
         (define y `(var ,(string->symbol (string-append "_" (number->string k)))))
         (define p* (subst (update x y undefined) p))
         (tableau (cons p* (append unexp (list `(forall ,x ,p)))) lits (sub1 n) cont env (add1 k))]
        [(cons fm unexp)
         (with-handlers ([exn:fail? (λ (e) (tableau unexp (cons fm lits) n cont env k))])
           (tryfind (λ (l) (cont (unify-complements env (cons fm l)) k)) lits))])))

(define deepen-verbose (make-parameter #f))

(define (deepen f n)
  (with-handlers ([exn:fail? (λ (e) (deepen f (add1 n)))])
    (when (deepen-verbose) (printf "Searching with depth limit ~a\n" n))
    (f n)))

(define (tabrefute fms)
  (deepen (λ (n) (tableau fms '() n (λ (env k) env) undefined 0) n) 0))

(define (tab fm)
  (define sfm (askolemize `(not ,(generalize fm))))
  (if (equal? sfm #f) 0 (tabrefute (list sfm))))

;; split into DNF disjuncts first; usually a big speedup
(define (splittab fm)
  (map tabrefute (simpdnf (askolemize `(not ,(generalize fm))))))
