#lang racket/base

;; fol.fs --- first-order logic: terms, semantics, free variables,
;; substitution, and function-symbol collection.
;;
;; Terms:    (var x) | (fn f t ...)
;; Atoms:    (rel R t ...)   (appearing inside (atom ...))

(require racket/match)
(require (only-in "../core/lib.rkt" unions subtract union tryapplyd undefine update undefined))
(require (only-in "../core/formulas.rkt" atom-union onatoms))

(provide (all-defined-out))

;; ===== semantics (3.3) =====
(define (termval func v tm)
  (match tm
    [`(var ,vn) (hash-ref v vn)]
    [`(fn ,f ,@args) (func f (map (λ (tm) (termval func v tm)) args))]))

(define (holds domain func pred v fm)
  (define (do-holds? fm)
    (match fm
      [#t #t]
      [#f #f]
      [`(atom (rel ,rn ,@args)) (pred rn (map (λ (tm) (termval func v tm)) args))]
      [`(not ,f) (not (do-holds? f))]
      [`(and ,f1 ,f2) (and (do-holds? f1) (do-holds? f2))]
      [`(or ,f1 ,f2) (or (do-holds? f1) (do-holds? f2))]
      [`(imp ,f1 ,f2) (or (not (do-holds? f1)) (do-holds? f2))]
      [`(iff ,f1 ,f2) (equal? (do-holds? f1) (do-holds? f2))]
      [`(forall ,s ,f) (andmap (λ (x) (holds domain func pred (hash-set v s x) f)) domain)]
      [`(exists ,s ,f) (ormap (λ (x) (holds domain func pred (hash-set v s x) f)) domain)]))
  (do-holds? fm))

;; ===== free variables =====
(define (fvt tm)
  (match tm
    [`(var ,vn) `(,vn)]
    [`(fn ,f ,@args) (unions (map fvt args))]))

(define (ground/term? tm)
  (null? (fvt tm)))

;; all variables (free and bound)
(define (var fm)
  (match fm
    [(or #t #f) '()]
    [`(atom (rel ,rn ,@args)) (unions (map fvt args))]
    [`(not ,f) (var f)]
    [`(,(or 'and 'or 'imp 'iff) ,f1 ,f2) (unions `(,(var f1) ,(var f2)))]
    [`(,(or 'forall 'exists) ,s ,f) (union (var f) `(,s))]))

(define (ground/formula? fm)
  (null? (var fm)))

(define (fv fm)
  (match fm
    [(or #t #f) '()]
    [`(atom (rel ,rn ,@args)) (unions (map fvt args))]
    [`(not ,f) (fv f)]
    [`(,(or 'and 'or 'imp 'iff) ,f1 ,f2) (unions `(,(fv f1) ,(fv f2)))]
    [`(,(or 'forall 'exists) ,s ,f) (subtract (fv f) `(,s))]))

(define (sentence? fm)
  (null? (fv fm)))

;; ===== universal closure (3.4) =====
(define (generalize fm)
  (foldl (λ (s f) `(forall ,s ,f)) fm (fv fm)))

;; ===== substitution =====
;; subfn is a partial function (hash) from variable name to term
(define (tsubst sfn tm)
  (match tm
    [`(var ,vn) (hash-ref sfn vn tm)]
    [`(fn ,f ,@args) `(fn ,f ,@(map (λ (t) (tsubst sfn t)) args))]))

(define (variant x vars)
  (if (member x vars)
      (variant (string->symbol (string-append (symbol->string x) "^")) vars)
      x))

(define (subst subfn fm)
  (match fm
    [(or #t #f) fm]
    [`(atom (rel ,rn ,@args)) `(atom (rel ,rn ,@(map (λ (a) (tsubst subfn a)) args)))]
    [`(not ,p) `(not ,(subst subfn p))]
    [`(,(and o (or 'and 'or 'imp 'iff)) ,f1 ,f2) `(,o ,(subst subfn f1) ,(subst subfn f2))]
    [`(,(and q (or 'forall 'exists)) ,s ,f) (substq subfn q s f)]))

(define (substq subfn q x p)
  (define x^
    (if (ormap (λ (y) (member x (fvt (hash-ref subfn y `(var ,y))))) (subtract (fv p) `(,x)))
        (variant x (fv (subst (undefine x subfn) p)))
        x))
  `(,q ,x^ ,(subst (update x `(var ,x^) subfn) p)))

;; ===== function symbols =====
(define (funcs tm)
  (match tm
    [`(var ,vn) '()]
    [`(fn ,f ,@args) (foldl (λ (a r) (union r (funcs a))) `(,(cons f (length args))) args)]))

(define (functions fm)
  (atom-union (λ (a)
                (match a
                  [`(rel ,p ,@args) (foldl (λ (arg r) (union r (funcs arg))) '() args)]))
              fm))

;; map a term function over every argument of every atom
(define (onformula f fm)
  (onatoms (λ (a)
             (match a
               [`(rel ,p ,@args) `(atom (rel ,p ,@(map f args)))]))
           fm))
