#lang racket/base

;; cong.fs --- congruence closure, and a decision procedure for the
;; satisfiability of ground equations/inequations (and hence validity of
;; universal formulas over equality).

(require racket/match)
(require (only-in racket/list partition))
(require (only-in "../core/lib.rkt"
                  union unions allpairs setify insert
                  update undefined tryapplyl
                  unequal equate equivalent canonize))
(require (only-in "../prop/prop.rkt" positive negate simpdnf))
(require (only-in "../fol/fol.rkt" generalize))
(require (only-in "../fol/skolem.rkt" askolemize))
(require (only-in "equal.rkt" dest-eq))

(provide (all-defined-out))

;; ===== subterms (including the term itself) =====
(define (subterms tm)
  (match tm
    [`(fn ,f ,@args) (foldr (λ (a acc) (union (subterms a) acc)) (list tm) args)]
    [_ (list tm)]))

;; ===== congruence of two terms under an equivalence =====
(define (congruent eqv st)
  (match st
    [(cons `(fn ,f ,@a1) `(fn ,g ,@a2))
     (and (equal? f g) (= (length a1) (length a2))
          (andmap (λ (x y) (equivalent eqv x y)) a1 a2))]
    [_ #f]))

;; ===== merge two terms, propagating congruence closure =====
;; state is (eqv . pfn) where pfn maps a term to its known predecessors
(define (emerge st eqvpfn)
  (define s (car st)) (define t (cdr st))
  (define eqv (car eqvpfn)) (define pfn (cdr eqvpfn))
  (define s* (canonize eqv s))
  (define t* (canonize eqv t))
  (if (equal? s* t*)
      eqvpfn
      (let ()
        (define sp (tryapplyl pfn s*))
        (define tp (tryapplyl pfn t*))
        (define eqv* (equate (cons s t) eqv))
        (define st* (canonize eqv* s*))
        (define pfn* (update st* (union sp tp) pfn))
        (foldr (λ (uv acc)
                 (if (congruent (car acc) uv) (emerge uv acc) acc))
               (cons eqv* pfn*)
               (allpairs cons sp tp)))))

(define (predecessors t pfn)
  (match t
    [`(fn ,f ,@a)
     (foldr (λ (s acc) (update s (insert t (tryapplyl acc s)) acc)) pfn (setify a))]
    [_ pfn]))

(define (ccsatisfiable fms)
  (define-values (pos neg) (partition positive fms))
  (define eqps (map dest-eq pos))
  (define eqns (map (λ (f) (dest-eq (negate f))) neg))
  (define lrs (append (map car eqps) (map cdr eqps) (map car eqns) (map cdr eqns)))
  (define pfn (foldr predecessors undefined (unions (map subterms lrs))))
  (define eqv (car (foldr emerge (cons unequal pfn) eqps)))
  (andmap (λ (lr) (not (equivalent eqv (car lr) (cdr lr)))) eqns))

(define (ccvalid fm)
  (define fms (simpdnf (askolemize `(not ,(generalize fm)))))
  (not (ormap ccsatisfiable fms)))
