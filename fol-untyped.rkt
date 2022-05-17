#lang racket/base

(require racket/match)
(require racket/set)
(require (only-in "set.rkt" unions))
(require (only-in "fpf.rkt" tryapplyd undefine update))

(provide (all-defined-out))
;; grammar of terms
;; term ::= (var symbol)
;;        | (fn symbol term*)

;; grammar of fol
;; fol ::= (rel symbol term*)

;; grammar of formula
;; formula := #t
;;          | #f
;;          | (atom fol)
;;          | (not formula)
;;          | (and formula formula)
;;          | (or formula formula)
;;          | (imp formula formula)
;;          | (iff formula formula)
;;          | (forall symbol formula)
;;          | (exists symbol formula)


;; chapter 3.3
(define (termval func v tm)
  (match tm
    [`(var ,vn) (hash-ref v vn)]
    [`(fn ,f ,@args)
     (func
      f
      (map
       (λ (tm) (termval func v tm))
       args))]))

(define (holds domain func pred v fm)
  (define (do-holds? fm)
    (match fm
      [#t #t]
      [#f #f]
      [`(atom (rel ,rn ,@args))
       (pred
        rn
        (map
         (λ (tm) (termval func v tm))
         args))]
      [`(not ,f) (not (do-holds? f))]
      [`(and ,f1 ,f2) (and (do-holds? f1) (do-holds? f2))]
      [`(or ,f1 ,f2) (or (do-holds? f1) (do-holds? f2))]
      [`(imp ,f1 ,f2) (or (not (do-holds? f1)) (do-holds? f2))]
      [`(iff ,f1 ,f2) (equal? (do-holds? f1) (do-holds? f2))]
      [`(forall ,s ,f)
       (andmap
        (λ (x) (holds domain func pred (hash-set v s x) f))
        domain)]
      [`(exists ,s ,f)
       (ormap
        (λ (x) (holds domain func pred (hash-set v s x) f))
        domain)]))
  (do-holds? fm))

(define (fvt tm)
  (match tm
    [`(var ,vn) (set vn)]
    [`(fn ,f ,@args) (unions (map fvt args))]))

(define (ground/term? tm)
  (set-empty? (fvt tm)))

(define (var fm)
  (match fm
    [(or #t #f) (set)]
    [`(atom (rel ,rn ,@args)) (unions (map fvt args))]
    [`(not ,f) (var f)]
    [(list (or 'and 'or 'imp 'iff) f1 f2) (unions `(,(var f1) ,(var f2)))]
    [(list (or 'forall 'exists) s f) (set-add (var f) s)]))

(define (ground/formula? fm)
  (set-empty? (var fm)))

(define (fv fm)
  (match fm
    [(or #t #f) (set)]
    [`(atom (rel ,rn ,@args)) (unions (map fvt args))]
    [`(not ,f) (fv f)]
    [(list (or 'and 'or 'imp 'iff) f1 f2) (unions `(,(fv f1) ,(fv f2)))]
    [(list (or 'forall 'exists) s f) (set-remove (fv f) s)]))

(define (sentence? fm)
  (set-empty? (fv fm)))

;; chapter 3.4
(define (generalize fm)
  (foldl
   (λ (s f)
     `(forall ,s ,f))
   fm
   (set->list (fv fm))))

(define (tsubst sfn tm)
  (match tm
    [`(var ,vn)
     (with-handlers ([exn:misc:match? (λ (e) tm)])
       (sfn vn))]
    [`(fn ,f ,@args)
     `(fn ,f ,(map (λ (t) (tsubst sfn t)) args))]))

(define (variant x vars)
  (if (member x vars)
      (variant
       (string->symbol
        (string-append (symbol->string x) "^"))
       vars)
      x))

(define (subst subfn fm)
  (match fm
    [(or #t #f) fm]
    [`(atom (rel ,rn ,@args))
     `(atom (rel ,rn ,@(map (λ (a) (tsubst subfn a)) args)))]
    [(list (and op (or 'and 'or 'imp 'iff)) f1 f2)
     `(,op ,(subst subfn f1) ,(subst subfn f2))]
    [(list (or 'forall 'exists) s f) (substq subfn 'forall s f)]))

(define (substq subfn q x p)
  (define x^
    (if
     (ormap
      (λ (y) (set-member? (fvt (tryapplyd subfn y `(var ,y))) x))
      (set->list (set-remove (fv p) x)))
     (variant x (set->list (fv (subst (undefine x subfn) p))))
     x))
  (list q x^ (subst (update x `(var ,x^) subfn) p)))
  