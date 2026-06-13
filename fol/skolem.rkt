#lang racket/base

;; skolem.fs --- first-order simplification, negation normal form,
;; prenex normal form, and Skolemization.

(require racket/match)
(require (only-in "../core/lib.rkt" update undefined))
(require (only-in "../prop/prop.rkt" psimplify1))
(require (only-in "fol.rkt" fv subst variant functions))

(provide (all-defined-out))

;; ===== simplification =====
(define (simplify1 fm)
  (match fm
    [`(,(or 'forall 'exists) ,s ,f) (if (not (member s (fv f))) f fm)]
    [_ (psimplify1 fm)]))

(define (simplify fm)
  (match fm
    [`(not ,p) (simplify1 `(not ,(simplify p)))]
    [`(,(and o (or 'and 'or 'imp 'iff)) ,p ,q) (simplify1 `(,o ,(simplify p) ,(simplify q)))]
    [`(,(and q (or 'forall 'exists)) ,s ,p) (simplify1 `(,q ,s ,(simplify p)))]
    [_ fm]))

;; ===== negation normal form (first-order) =====
(define (nnf fm)
  (match fm
    [`(,(and o (or 'and 'or)) ,p ,q) `(,o ,(nnf p) ,(nnf q))]
    [`(imp ,p ,q) `(or ,(nnf `(not ,p)) ,(nnf q))]
    [`(iff ,p ,q) `(or (and ,(nnf p) ,(nnf q)) (and ,(nnf `(not ,p)) ,(nnf `(not ,q))))]
    [`(not (not ,p)) (nnf p)]
    [`(not (and ,p ,q)) `(or ,(nnf `(not ,p)) ,(nnf `(not ,q)))]
    [`(not (or ,p ,q)) `(and ,(nnf `(not ,p)) ,(nnf `(not ,q)))]
    [`(not (imp ,p ,q)) `(and ,(nnf p) ,(nnf `(not ,q)))]
    [`(not (iff ,p ,q)) `(or (and ,(nnf p) ,(nnf `(not ,q))) (and ,(nnf `(not ,p)) ,(nnf q)))]
    [`(,(and q (or 'forall 'exists)) ,s ,p) `(,q ,s ,(nnf p))]
    [`(not (forall ,s ,p)) `(exists ,s ,(nnf `(not ,p)))]
    [`(not (exists ,s ,p)) `(forall ,s ,(nnf `(not ,p)))]
    [_ fm]))

;; ===== prenex normal form =====
(define (pullquants fm)
  (match fm
    [`(and (forall ,x ,p) (forall ,y ,q)) (pullq #t #t fm 'forall 'and x y p q)]
    [`(or (exists ,x ,p) (exists ,y ,q)) (pullq #t #t fm 'exists 'or x y p q)]
    [`(,(and o (or 'and 'or)) (,(and qt (or 'forall 'exists)) ,x ,p) ,q)
     (pullq #t #f fm qt o x x p q)]
    [`(,(and o (or 'and 'or)) ,p (,(and qt (or 'forall 'exists)) ,y ,q))
     (pullq #f #t fm qt o y y p q)]
    [_ fm]))

(define (pullq l r fm qf o x y p q)
  (define z (variant x (fv fm)))
  (define p^
    (if l
        (subst (update x `(var ,z) undefined) p)
        p))
  (define q^
    (if r
        (subst (update y `(var ,z) undefined) q)
        q))
  `(,qf ,z ,(pullquants `(,o ,p^ ,q^))))

(define (prenex fm)
  (match fm
    [`(,(and q (or 'forall 'exists)) ,s ,f) `(,q ,s ,(prenex f))]
    [`(,(and o (or 'and 'or)) ,f1 ,f2) (pullquants `(,o ,(prenex f1) ,(prenex f2)))]
    [_ fm]))

(define pnf (compose prenex nnf simplify))

;; ===== Skolemization =====
(define (skolem fm fns)
  (define (skolem2 o p q fns)
    (define-values (p^ fns^) (skolem p fns))
    (define-values (q^ fns^^) (skolem q fns^))
    (values `(,o ,p^ ,q^) fns^^))
  (match fm
    [`(exists ,y ,p)
     (define xs (fv fm))
     (define f
       (variant (if (null? xs)
                    (string->symbol (string-append "c_" (symbol->string y)))
                    (string->symbol (string-append "f_" (symbol->string y))))
                fns))
     (define fx `(fn ,f ,@(map (λ (x) `(var ,x)) xs)))
     (skolem (subst (update y fx undefined) p) (cons f fns))]
    [`(forall ,x ,p)
     (define-values (p^ fns^) (skolem p fns))
     (values `(forall ,x ,p^) fns^)]
    [`(,(and o (or 'and 'or)) ,p ,q) (skolem2 o p q fns)]
    [_ (values fm fns)]))

(define (askolemize fm)
  (define-values (f _) (skolem (nnf (simplify fm)) (map car (functions fm))))
  f)

(define (specialize fm)
  (match fm
    [`(forall ,x ,p) (specialize p)]
    [_ fm]))

(define skolemize (compose specialize pnf askolemize))
