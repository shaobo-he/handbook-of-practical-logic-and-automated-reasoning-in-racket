#lang racket/base

(require racket/match)
(require (only-in "set.rkt" unions subtract union))
(require (only-in "fpf.rkt" tryapplyd undefine update undefined))
(require (only-in "pl-untyped.rkt" psimplify1))
(require (only-in "formula-untyped.rkt" atom-union))

(provide (all-defined-out))
;; grammar of terms
;; term ::= (var symbol)
;;        | (fn symbol term*)

;; grammar of fol
;; fol ::= (rel symbol term*)

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
    [`(var ,vn) `(,vn)]
    [`(fn ,f ,@args) (unions (map fvt args))]))

(define (ground/term? tm)
  (null? (fvt tm)))

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

;; chapter 3.4
(define (generalize fm)
  (foldl
   (λ (s f)
     `(forall ,s ,f))
   fm
   (fv fm)))

(define (tsubst sfn tm)
  (match tm
    [`(var ,vn)
     (with-handlers ([exn:misc:match? (λ (e) tm)])
       (sfn vn))]
    [`(fn ,f ,@args)
     `(fn ,f ,@(map (λ (t) (tsubst sfn t)) args))]))

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
    [`(not ,p) `(not ,(subst subfn p))]
    [`(,(and o (or 'and 'or 'imp 'iff)) ,f1 ,f2)
     `(,o ,(subst subfn f1) ,(subst subfn f2))]
    [`(,(and q (or 'forall 'exists)) ,s ,f) (substq subfn q s f)]))

(define (substq subfn q x p)
  (define x^
    (if
     (ormap
      (λ (y) (member x (fvt (tryapplyd subfn y `(var ,y)))))
      (subtract (fv p) `(,x)))
     (variant x (fv (subst (undefine x subfn) p)))
     x))
  `(,q ,x^ ,(subst (update x `(var ,x^) subfn) p)))

(define (simplify1 fm)
  (match fm
    [`(,(or 'forall 'exists) ,s ,f)
     (if
      (not (member s (fv f)))
       f
       fm)]
    [_ (psimplify1 fm)]))

(define (simplify fm)
  (match fm
    [`(not ,p) (simplify1 `(not ,(simplify p)))]
    [`(,(and o (or 'and 'or 'imp 'iff)) ,p ,q)
     (simplify1 `(,o ,(simplify p) ,(simplify q)))]
    [`(,(and q (or 'forall 'exists)) ,s ,p)
     (simplify1 `(,q ,s ,(simplify p)))]
    [_ fm]))

(define (nnf fm)
  (match fm
    [`(,(and o (or 'and 'or)) ,p ,q)
     `(,o ,(nnf p) ,(nnf q))]
    [`(imp ,p ,q) `(or ,(nnf `(not ,p)) ,(nnf q))]
    [`(iff ,p ,q)
     `(or
       (and ,(nnf p) ,(nnf q))
       (and ,(nnf `(not ,p)) ,(nnf `(not ,q))))]
    [`(not (not ,p)) (nnf p)]
    [`(not (and ,p ,q)) `(or ,(nnf `(not ,p)) ,(nnf `(not ,q)))]
    [`(not (or ,p ,q)) `(and ,(nnf `(not ,p)) ,(nnf `(not ,q)))]
    [`(not (imp ,p ,q)) `(and ,(nnf p) ,(nnf `(not ,q)))]
    [`(not (iff ,p ,q))
     `(or
       (and ,(nnf p) ,(nnf `(not ,q)))
       (and ,(nnf `(not ,p)) ,(nnf q)))]
    [`(,(and q (or 'forall 'exists)) ,s ,p) `(,q ,s ,(nnf p))]
    [`(not (forall ,s ,p)) `(exists ,s ,(nnf `(not ,p)))]
    [`(not (exists ,s ,p)) `(forall ,s ,(nnf `(not ,p)))]
    [_ fm]))

(define (pullquants fm)
  (match fm
    [`(and (forall ,x ,p) (forall ,y ,q)) (pullq #t #t fm 'forall 'and x y p q)]
    [`(or (exists ,x ,p) (exists ,y ,q)) (pullq #t #t fm 'exists 'or x y p q)]
    [`(,(and o (or 'and 'or)) (,(and qt (or 'forall 'exists)) ,x ,p) ,q) (pullq #t #f fm qt o x x p q)]
    [`(,(and o (or 'and 'or)) ,p (,(and qt (or 'forall 'exists)) ,y ,q)) (pullq #f #t fm qt o y y p q)]
    [_ fm]))

(define (pullq l r fm qf o x y p q)
  (define z (variant x (fv fm)))
  (define p^ (if l (subst (update x `(var ,z) undefined) p) p))
  (define q^ (if r (subst (update y `(var ,z) undefined) q) q))
  `(,qf ,z ,(pullquants `(,o ,p^ ,q^))))

(define (prenex fm)
  (match fm
    [`(,(and q (or 'forall 'exists)) ,s ,f) `(,q ,s ,(prenex f))]
    [`(,(and o (or 'and 'or)) ,f1 ,f2) (pullquants `(,o ,(prenex f1) ,(prenex f2)))]
    [_ fm]))

(define pnf (compose prenex nnf simplify))

(define (funcs tm)
  (match tm
    [`(var ,vn) '()]
    [`(fn ,f ,@args)
     (foldl
      (λ (a r)
        (union r (funcs a)))
      `(,(cons f (length args)))
      args)]))

(define (functions fm)
  (atom-union
   (λ (a)
     (match a
       [`(rel ,p ,@args)
        (foldl
         (λ (arg r)
           (union r (funcs arg)))
         '()
         args)]))
   fm))

(define (skolem fm fns)
  (define (skolem2 o p q fns)
    (define-values (p^ fns^) (skolem p fns))
    (define-values (q^ fns^^) (skolem q fns^))
    (values `(,o ,p^ ,q^) fns^^))
  (match fm
    [`(exists ,y ,p)
     (define xs (fv fm))
     (define f
       (variant
        (if (null? xs)
            (string->symbol
             (string-append "c_" (symbol->string y)))
            (string->symbol
             (string-append "f_" (symbol->string y))))
        fns))
     (define fx `(fn ,f ,@(map (λ (x) `(var ,x)) xs)))
     (skolem (subst (update y fx undefined) p) (cons f fns))]
    [`(forall ,x ,p)
     (define-values (p^ fns^) (skolem p fns))
     (values `(forall ,x ,p^) fns^)]
    [`(,(and o (or 'and 'or)) ,p ,q) (skolem2 o p q fns)]
    [_ (values fm fns)]))

(define (askolemize fm)
  (define-values (f _)
    (skolem (nnf (simplify fm)) (map car (functions fm))))
  f)

(define (specialize fm)
  (match fm
    [`(forall ,x ,p) (specialize p)]
    [_ fm]))

(define skolemize
  (compose specialize pnf askolemize))