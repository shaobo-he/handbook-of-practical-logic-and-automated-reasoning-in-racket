#lang racket/base

;; folderived --- derived first-order inference rules: equality symmetry/
;; transitivity, congruence, substitution (isubst), alpha-conversion, and
;; universal specialization (ispec/spec), all on the LCF kernel.

(require racket/match)
(require (only-in "../core/lib.rkt" funpow union unions update undefined))
(require (only-in "../core/formulas.rkt" dest-imp consequent antecedent))
(require (only-in "../fol/fol.rkt" subst fv fvt var variant))
(require (only-in "../equality/equal.rkt" mk-eq dest-eq lhs rhs))
(require "lcf.rkt")
(require "lcfprop.rkt")

(provide (all-defined-out))

(define (eq-sym s t)
  (define rth (axiom-eqrefl s))
  (funpow 2 (λ (th) (modusponens (imp-swap th) rth)) (axiom-predcong '= (list s s) (list t s))))

(define (eq-trans s t u)
  (define th1 (axiom-predcong '= (list t u) (list s u)))
  (define th2 (modusponens (imp-swap th1) (axiom-eqrefl u)))
  (imp-trans (eq-sym s t) th2))

;; Derives  s=t -> stm=ttm  by structural induction on the two terms: where they
;; already agree, only the trivial s=t hypothesis is needed; where both are
;; applications of the same function, recurse on the arguments and combine the
;; resulting equalities with the funcong axiom.
(define (icongruence s t stm ttm)
  (cond
    [(equal? stm ttm) (add-assum (mk-eq s t) (axiom-eqrefl stm))]
    [(and (equal? stm s) (equal? ttm t)) (imp-refl (mk-eq s t))]
    [else
     (match* (stm ttm)
       [(`(fn ,fs ,@sa) `(fn ,ft ,@ta))
        #:when (and (equal? fs ft) (= (length sa) (length ta)))
        (define ths (map (λ (a b) (icongruence s t a b)) sa ta))
        (define ts (map (λ (th) (consequent (concl th))) ths))
        (imp-trans-chain ths (axiom-funcong fs (map lhs ts) (map rhs ts)))]
       [(_ _) (error 'icongruence "not congruent")])]))

(define (gen-right-th x p q)
  (imp-swap (imp-trans (axiom-impall x p) (imp-swap (axiom-allimp x p q)))))

(define (genimp x th)
  (match-define `(,p . ,q) (dest-imp (concl th)))
  (modusponens (axiom-allimp x p q) (gen x th)))

(define (gen-right x th)
  (match-define `(,p . ,q) (dest-imp (concl th)))
  (modusponens (gen-right-th x p q) (gen x th)))

;; The left-elimination rule for the existential:  (exists x. p) -> (p -> q) -> q
;; (with x not free in q). exists is reduced to ~(forall x. ~p), so the proof
;; chains genimp, gen-right and double-negation over that encoding.
(define (exists-left-th x p q)
  (define p* `(imp ,p #f))
  (define q* `(imp ,q #f))
  (define th1 (genimp x (imp-swap (imp-trans-th p q #f))))
  (define th2 (imp-trans th1 (gen-right-th x q* p*)))
  (define th3 (imp-swap (imp-trans-th q* `(forall ,x ,p*) #f)))
  (define th4 (imp-trans2 (imp-trans th2 th3) (axiom-doubleneg q)))
  (define th5 (imp-add-concl #f (genimp x (iff-imp2 (axiom-not p)))))
  (define th6 (imp-trans (iff-imp1 (axiom-not `(forall ,x (not ,p)))) th5))
  (define th7 (imp-trans (iff-imp1 (axiom-exists x p)) th6))
  (imp-swap (imp-trans th7 (imp-swap th4))))

(define (exists-left x th)
  (match-define `(,p . ,q) (dest-imp (concl th)))
  (modusponens (exists-left-th x p q) (gen x th)))

(define (subspec th)
  (match (concl th)
    [`(imp ,(and e `(atom (rel = (var ,x) ,t))) (imp ,p ,q))
     (define th1 (imp-trans (genimp x (imp-swap th)) (exists-left-th x e q)))
     (modusponens (imp-swap th1) (axiom-existseq x t))]
    [_ (error 'subspec "wrong sort of theorem")]))

(define (subalpha th)
  (match (concl th)
    [`(imp (atom (rel = (var ,x) (var ,y))) (imp ,p ,q))
     (if (equal? x y)
         (genimp x (modusponens th (axiom-eqrefl `(var ,x))))
         (gen-right y (subspec th)))]
    [_ (error 'subalpha "wrong sort of theorem")]))

;; Core substitution rule: derive  s=t -> (sfm -> tfm)  where tfm is sfm with some
;; occurrences of s replaced by t. It recurses structurally: atoms use predcong,
;; implications flip the equality direction on the antecedent, matching
;; quantifiers alpha-convert through a fresh variable, and remaining connectives
;; are first expanded away to their primitive form.
(define (isubst s t sfm tfm)
  (if (equal? sfm tfm)
      (add-assum (mk-eq s t) (imp-refl tfm))
      (match* (sfm tfm)
        [(`(atom (rel ,p ,@sa)) `(atom (rel ,p2 ,@ta)))
         #:when (and (equal? p p2) (= (length sa) (length ta)))
         (define ths (map (λ (a b) (icongruence s t a b)) sa ta))
         (define eqs (map (λ (th) (dest-eq (consequent (concl th)))) ths))
         (imp-trans-chain ths (axiom-predcong p (map car eqs) (map cdr eqs)))]
        [(`(imp ,sp ,sq) `(imp ,tp ,tq))
         (define th1 (imp-trans (eq-sym s t) (isubst t s tp sp)))
         (define th2 (isubst s t sq tq))
         (imp-trans-chain (list th1 th2) (imp-mono-th sp tp sq tq))]
        [(`(forall ,x ,p) `(forall ,y ,q))
         (if (equal? x y)
             (imp-trans (gen-right x (isubst s t p q)) (axiom-allimp x p q))
             (let ()
               (define z `(var ,(variant x (unions (list (fv p) (fv q) (fvt s) (fvt t))))))
               (define th1 (isubst `(var ,x) z p (subst (update x z undefined) p)))
               (define th2 (isubst z `(var ,y) (subst (update y z undefined) q) q))
               (define th3 (subalpha th1))
               (define th4 (subalpha th2))
               (define th5 (isubst s t (consequent (concl th3)) (antecedent (concl th4))))
               (imp-swap (imp-trans2 (imp-trans th3 (imp-swap th5)) th4))))]
        [(_ _)
         (define sth (iff-imp1 (expand-connective sfm)))
         (define tth (iff-imp2 (expand-connective tfm)))
         (define th1 (isubst s t (consequent (concl sth)) (antecedent (concl tth))))
         (imp-swap (imp-trans sth (imp-swap (imp-trans2 th1 tth))))])))

(define (alpha z fm)
  (match fm
    [`(forall ,x ,p)
     (define p* (subst (update x `(var ,z) undefined) p))
     (subalpha (isubst `(var ,x) `(var ,z) p p*))]
    [_ (error 'alpha "not a universal formula")]))

;; Instantiate (forall x. p) at the term t. If t mentions x, first alpha-convert
;; the bound variable to a fresh name to avoid capturing t's own variables, then
;; specialise; otherwise apply the substitution rule directly.
(define (ispec t fm)
  (match fm
    [`(forall ,x ,p)
     (if (member x (fvt t))
         (let ([th (alpha (variant x (union (fvt t) (var p))) fm)])
           (imp-trans th (ispec t (consequent (concl th)))))
         (subspec (isubst `(var ,x) t p (subst (update x t undefined) p))))]
    [_ (error 'ispec "non-universal formula")]))

(define (spec t th)
  (modusponens (ispec t (concl th)) th))
