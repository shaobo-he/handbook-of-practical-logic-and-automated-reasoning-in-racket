#lang racket/base

;; lcf.fs --- an LCF-style kernel for a Tarski/Hilbert system of first-order
;; logic. A "theorem" is just a formula, but (by convention) one only ever
;; produced through these primitive inference rules and axiom schemes.

(require racket/match)
(require (only-in racket/string string-join))
(require (only-in "../core/formulas.rkt" formula->string))
(require (only-in "../equality/equal.rkt" mk-eq))

(provide (all-defined-out))

;; ===== auxiliary =====
(define (occurs-in s t)
  (or (equal? s t)
      (match t
        [`(var ,y) #f]
        [`(fn ,f ,@args) (ormap (λ (a) (occurs-in s a)) args)])))

(define (free-in t fm)
  (match fm
    [(or #t #f) #f]
    [`(not ,p) (free-in t p)]
    [`(,(or 'and 'or 'imp 'iff) ,p ,q) (or (free-in t p) (free-in t q))]
    [`(,(or 'forall 'exists) ,y ,p) (and (not (occurs-in `(var ,y) t)) (free-in t p))]
    [`(atom (rel ,p ,@args)) (ormap (λ (a) (occurs-in t a)) args)]))

;; ===== primitive inference rules =====
(define (modusponens pq p)
  (match pq
    [`(imp ,p* ,q)
     #:when (equal? p p*)
     q]
    [_ (error 'modusponens "modusponens")]))

(define (gen x p)
  `(forall ,x ,p))

;; ===== axiom schemes =====
(define (axiom-addimp p q)
  `(imp ,p (imp ,q ,p)))
(define (axiom-distribimp p q r)
  `(imp (imp ,p (imp ,q ,r)) (imp (imp ,p ,q) (imp ,p ,r))))
(define (axiom-doubleneg p)
  `(imp (imp (imp ,p #f) #f) ,p))
(define (axiom-allimp x p q)
  `(imp (forall ,x (imp ,p ,q)) (imp (forall ,x ,p) (forall ,x ,q))))
(define (axiom-impall x p)
  (if (free-in `(var ,x) p)
      (error 'axiom-impall "variable free in formula")
      `(imp ,p (forall ,x ,p))))
(define (axiom-existseq x t)
  (if (occurs-in `(var ,x) t)
      (error 'axiom-existseq "variable free in term")
      `(exists ,x ,(mk-eq `(var ,x) t))))
(define (axiom-eqrefl t)
  (mk-eq t t))
(define (axiom-funcong f lefts rights)
  (foldr (λ (s t p) `(imp ,(mk-eq s t) ,p)) (mk-eq `(fn ,f ,@lefts) `(fn ,f ,@rights)) lefts rights))
(define (axiom-predcong p lefts rights)
  (foldr (λ (s t acc) `(imp ,(mk-eq s t) ,acc))
         `(imp (atom (rel ,p ,@lefts)) (atom (rel ,p ,@rights)))
         lefts
         rights))
(define (axiom-iffimp1 p q)
  `(imp (iff ,p ,q) (imp ,p ,q)))
(define (axiom-iffimp2 p q)
  `(imp (iff ,p ,q) (imp ,q ,p)))
(define (axiom-impiff p q)
  `(imp (imp ,p ,q) (imp (imp ,q ,p) (iff ,p ,q))))
(define axiom-true `(iff #t (imp #f #f)))
(define (axiom-not p)
  `(iff (not ,p) (imp ,p #f)))
(define (axiom-and p q)
  `(iff (and ,p ,q) (imp (imp ,p (imp ,q #f)) #f)))
(define (axiom-or p q)
  `(iff (or ,p ,q) (not (and (not ,p) (not ,q)))))
(define (axiom-exists x p)
  `(iff (exists ,x ,p) (not (forall ,x (not ,p)))))

(define (concl c)
  c)

;; ===== printing =====
(define (term->string tm)
  (match tm
    [`(var ,x) (symbol->string x)]
    [`(fn ,f) (symbol->string f)]
    [`(fn ,f ,@args)
     (string-append (symbol->string f) "(" (string-join (map term->string args) ",") ")")]))

(define (fol-atom->string prec a)
  (match a
    [`(rel = ,s ,t) (string-append (term->string s) " = " (term->string t))]
    [`(rel ,p) (symbol->string p)]
    [`(rel ,p ,@args)
     (string-append (symbol->string p) "(" (string-join (map term->string args) ",") ")")]))

(define (thm->string th)
  (string-append "|- " (formula->string fol-atom->string (concl th))))
(define (print-thm th)
  (display (thm->string th)))
