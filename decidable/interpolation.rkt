#lang racket/base

;; interpolation.fs --- Craig-Robinson interpolation (Kreisel-Krivine style),
;; built up from propositional, to universal, to fully general formulas, and
;; finally lifted to logic with equality.

(require racket/match)
(require (only-in racket/list range))
(require (only-in "../core/lib.rkt" subtract setify fpf union intersect update undefined))
(require (only-in "../core/formulas.rkt" list-conj atom-union mk-exists dest-imp))
(require (only-in "../prop/prop.rkt" psubst atoms psimplify))
(require (only-in "../fol/fol.rkt" fv functions subst))
(require (only-in "../fol/skolem.rkt" specialize prenex nnf skolem))
(require (only-in "../fol/herbrand.rkt" herbfuns dp-refine-loop))
(require (only-in "../prop/defcnf.rkt" var-index))
(require (only-in "../equality/eqelim.rkt" replace))
(require (only-in "../equality/equal.rkt" equalitize))
(require (only-in "../equality/order.rkt" termsize))
(require (only-in "../prop/prop.rkt" simpcnf))

(provide (all-defined-out))

;; ===== propositional interpolation =====
(define (pinterpolate p q)
  (define (orify a r)
    `(or ,(psubst (update a #f undefined) r) ,(psubst (update a #t undefined) r)))
  (psimplify (foldr orify p (subtract (atoms p) (atoms q)))))

;; ===== relation interpolation for universal closed formulas =====
(define (urinterpolate p q)
  (define fm (specialize (prenex `(and ,p ,q))))
  (define fvs (fv fm))
  (define-values (consts funcs) (herbfuns fm))
  (define cntms (map (λ (c) `(fn ,(car c))) consts))
  (define tups (dp-refine-loop (simpcnf fm) cntms funcs fvs 0 '() '() '()))
  (define fmis (map (λ (tup) (subst (fpf fvs tup) fm)) tups))
  (define ps
    (map (λ (f)
           (match f
             [`(and ,a ,b) a]))
         fmis))
  (define qs
    (map (λ (f)
           (match f
             [`(and ,a ,b) b]))
         fmis))
  (pinterpolate (list-conj (setify ps)) (list-conj (setify qs))))

;; ===== topmost terms over a set of function symbols =====
(define (toptermt fns tm)
  (match tm
    [`(var ,x) '()]
    [`(fn ,f ,@args)
     (if (member (cons f (length args)) fns)
         (list tm)
         (foldr (λ (a acc) (union (toptermt fns a) acc)) '() args))]))

(define (topterms fns fm)
  (atom-union (λ (at)
                (match at
                  [`(rel ,p ,@args) (foldr (λ (a acc) (union (toptermt fns a) acc)) '() args)]))
              fm))

;; ===== interpolation for arbitrary universal formulas =====
(define (uinterpolate p q)
  (define fp (functions p))
  (define fq (functions q))
  (define (simpinter tms n c)
    (match tms
      ['() c]
      [`(,(and tm `(fn ,f ,@args)) . ,otms)
       (define v (string->symbol (string-append "v_" (number->string n))))
       (define c* (replace (update tm `(var ,v) undefined) c))
       (define c**
         (if (member (cons f (length args)) fp)
             `(exists ,v ,c*)
             `(forall ,v ,c*)))
       (simpinter otms (+ n 1) c**)]))
  (define c (urinterpolate p q))
  (define tts (topterms (union (subtract fp fq) (subtract fq fp)) c))
  (define tms (sort tts (λ (a b) (> (termsize a) (termsize b)))))
  (simpinter tms 1 c))

;; ===== lift to formulas with no common free variables =====
(define (cinterpolate p q)
  (define fm (nnf `(and ,p ,q)))
  (define efm (foldr mk-exists fm (fv fm)))
  (define fns (map car (functions fm)))
  (define-values (sk _) (skolem efm fns))
  (match sk
    [`(and ,p* ,q*) (uinterpolate p* q*)]))

;; ===== fully general formulas =====
(define (interpolate p q)
  (define vs (map (λ (v) `(var ,v)) (intersect (fv p) (fv q))))
  (define fns (functions `(and ,p ,q)))
  (define n (+ 1 (foldr (λ (f acc) (max acc (var-index "c_" (car f)))) 0 fns)))
  (define cs
    (map (λ (i) `(fn ,(string->symbol (string-append "c_" (number->string i)))))
         (range n (+ n (length vs)))))
  (define fn-vc (fpf vs cs))
  (define fn-cv (fpf cs vs))
  (replace fn-cv (cinterpolate (replace fn-vc p) (replace fn-vc q))))

;; ===== lift to logic with equality =====
(define (einterpolate p q)
  (define p* (equalitize p))
  (define q* (equalitize q))
  (define p**
    (if (equal? p* p)
        p
        `(and ,(car (dest-imp p*)) ,p)))
  (define q**
    (if (equal? q* q)
        q
        `(and ,(car (dest-imp q*)) ,q)))
  (interpolate p** q**))
