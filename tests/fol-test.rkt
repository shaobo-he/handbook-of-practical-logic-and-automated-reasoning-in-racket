#lang racket/base

(require rackunit)
(require racket/match)
(require (only-in racket/list range))
(require (only-in math/number-theory prime?))
(require "../fol/fol.rkt")
(require "../fol/skolem.rkt")

;; domain, func, pred for Boolean and modulo n
(define b-domain '(#t #f))

(define (b-func f args)
  (match f
    ['|0| #f]
    ['|1| #t]
    ['+ (not (apply equal? args))]
    ['* (apply (λ (x y) (and x y)) args)]))

(define (b-pred p args)
  (match p
    ['= (apply equal? args)]))

(define (m-domain n)
  (range n))

(define (m-func n)
  (λ (f args)
    (match f
      ['|0| 0]
      ['|1| (modulo 1 n)]
      ['+ (apply (λ (x y) (modulo (+ x y) n)) args)]
      ['* (apply (λ (x y) (modulo (* x y) n)) args)])))

(define (m-pred n)
  (λ (p args)
    (match p
      ['= (apply equal? args)])))

;; simple term and formula
(define *11 '(fn * (fn |1|) (fn |1|)))
(define *11=0 `(atom (rel = (fn |0|) ,*11)))

(check-true (termval b-func #f *11))
(check-false (holds b-domain b-func b-pred #f *11=0))

;; quantified formulas
(define 0or1 '(forall x (or (atom (rel = (var x) (fn |0|))) (atom (rel = (var x) (fn |1|))))))
(define v (make-immutable-hash))

(check-true (holds b-domain b-func b-pred v 0or1))
(check-true (holds (m-domain 2) (m-func 2) (m-pred 2) v 0or1))
(check-false (holds (m-domain 3) (m-func 3) (m-pred 3) v 0or1))

(define mul-rev
  '(forall x
           (imp (not (atom (rel = (var x) (fn |0|))))
                (exists y (atom (rel = (fn * (var x) (var y)) (fn |1|)))))))
(check-equal? (filter (λ (n) (holds (m-domain n) (m-func n) (m-pred n) v mul-rev)) (range 1 45))
              (cons 1 (filter prime? (range 1 45))))

;; groundness and sentence tests
(check-true (ground/term? *11))
(check-true (ground/formula? *11=0))
(check-true (sentence? 0or1))
(check-true (sentence? mul-rev))

;; generalize
(define xy+z '(exists y (atom (rel < (var x) (fn '+ (var y) (var z))))))
(check-true (sentence? (generalize xy+z)))

;; substitution in terms
(define x≤y '(fn ≤ (var x) (var y)))
(check-equal? (tsubst (hash 'x '(fn |1|)) x≤y) '(fn ≤ (fn |1|) (var y)))

;; substituion in formulas
(check-equal? 'x (variant 'x '(z y)))
(check-equal? 'x^ (variant 'x '(x y)))
(check-equal? 'x^^ (variant 'x '(x x^)))
(define sfn (hash 'y '(var x)))
(define qx=y '(forall x (atom (rel = (var x) (var y)))))
(check-equal? (subst sfn qx=y) '(forall x^ (atom (rel = (var x^) (var x)))))
(define qxx^y
  '(forall x (forall x^ (imp (atom (rel = (var x) (var y))) (atom (rel = (var x) (var x^)))))))
(check-equal?
 (subst sfn qxx^y)
 '(forall x^ (forall x^^ (imp (atom (rel = (var x^) (var x))) (atom (rel = (var x^) (var x^^)))))))

;; prenex normal form
(define nnf-test
  '(imp (forall x (atom (rel P (var x))))
        (iff (exists y (atom (rel Q (var y))))
             (exists z (and (atom (rel P (var z))) (atom (rel Q (var z))))))))
(check-equal?
 (nnf nnf-test)
 '(or (exists x (not (atom (rel P (var x)))))
      (or (and (exists y (atom (rel Q (var y))))
               (exists z (and (atom (rel P (var z))) (atom (rel Q (var z))))))
          (and (forall y (not (atom (rel Q (var y)))))
               (forall z (or (not (atom (rel P (var z)))) (not (atom (rel Q (var z))))))))))
(define prenex-test
  '(imp (forall x (or (atom (rel P (var x))) (atom (rel R (var y)))))
        (exists y
                (exists z
                        (or (atom (rel Q (var y)))
                            (not (exists z (and (atom (rel P (var z))) (atom (rel Q (var z)))))))))))

(check-equal? (pnf prenex-test)
              '(exists x
                       (forall z
                               (or (and (not (atom (rel P (var x)))) (not (atom (rel R (var y)))))
                                   (or (atom (rel Q (var x)))
                                       (or (not (atom (rel P (var z))))
                                           (not (atom (rel Q (var z))))))))))

;; Skolemization
(check-equal? (funcs *11) '((* . 2) (|1| . 0)))
(check-equal? (functions *11=0) '((* . 2) (|0| . 0) (|1| . 0)))
(check-true (null? (functions prenex-test)))
(define skolem-test1
  '(exists y
           (imp (atom (rel < (var x) (var y)))
                (forall u (exists v (atom (rel < (fn * (var x) (var u)) (fn * (var y) (var v)))))))))

(define skolem-test2
  '(forall x
           (imp (atom (rel P (var x)))
                (exists y
                        (exists z
                                (or (atom (rel Q (var y)))
                                    (not (exists z
                                                 (and (atom (rel P (var z)))
                                                      (atom (rel Q (var z))))))))))))
(check-equal?
 (skolemize skolem-test1)
 '(or (not (atom (rel < (var x) (fn f_y (var x)))))
      (atom (rel < (fn * (var x) (var u)) (fn * (fn f_y (var x)) (fn f_v (var x) (var u)))))))
(check-equal? (skolemize skolem-test2)
              '(or (not (atom (rel P (var x))))
                   (or (atom (rel Q (fn c_y)))
                       (or (not (atom (rel P (var z)))) (not (atom (rel Q (var z))))))))

;; ===== free / all variables, simplify =====
(check-equal? (sort (fvt '(fn f (var x) (fn g (var y)))) symbol<?) '(x y))
(check-equal? (sort (var '(forall x (atom (rel P (var x) (var y))))) symbol<?) '(x y))
(check-equal? (fv '(forall x (atom (rel P (var x) (var y))))) '(y)) ; bound x not free
(check-equal? (simplify '(forall x (atom (rel P)))) '(atom (rel P))) ; vacuous quantifier dropped
(check-equal? (simplify '(and #t (atom (rel P)))) '(atom (rel P)))

;; ===== onformula: map a term function over every argument of every atom =====
;; the function is applied to each top-level argument of each atom, not recursively
;; rebuilt term-by-term (so f sees whole arguments like (fn f (var y)), not subterms)
(check-equal? (onformula (λ (t) `(fn succ ,t)) '(atom (rel P (var x) (fn f (var y)))))
              '(atom (rel P (fn succ (var x)) (fn succ (fn f (var y))))))
;; onformula recurses through the logical structure, hitting atoms under quantifiers
(check-equal? (onformula (λ (t) `(fn succ ,t))
                         '(forall x (and (atom (rel P (var x))) (atom (rel Q (var y))))))
              '(forall x (and (atom (rel P (fn succ (var x)))) (atom (rel Q (fn succ (var y)))))))
;; identity transformation leaves the formula unchanged
(check-equal? (onformula (λ (t) t) qx=y) qx=y)

;; ===== termval: a custom interpretation that recurses through nesting =====
;; here func ignores f and returns the argument count, so the value is the arity
;; of the *outermost* application (1 for (fn f ...)) after recursively evaluating
(check-equal? (termval (λ (f args) (length args)) (hash 'x 0) '(fn f (fn g (var x)))) 1)
(check-equal? (termval (λ (f args) (length args)) (hash 'x 0) '(fn g (var x) (fn h))) 2)

;; ===== funcs / functions on constants (0-arity) =====
(check-equal? (funcs '(fn a)) '((a . 0))) ; a constant is a 0-arity function
(check-equal? (sort (functions '(atom (rel P (fn a) (fn b)))) symbol<? #:key car) '((a . 0) (b . 0)))

;; ===== tsubst: composition law (apply two substitutions = apply the composite) =====
(let ([s2 (hash 'x '(fn f (var y)) 'y '(fn a))]
      [s1 (hash 'x '(fn b) 'y '(fn g (var z)) 'z '(fn c))])
  (define t '(fn h (var x) (fn k (var y) (var z))))
  ;; composing s1 after s2: push s2's range through s1 (domains coincide here)
  (check-equal?
   (tsubst s1 (tsubst s2 t))
   (tsubst (hash 'x (tsubst s1 (hash-ref s2 'x)) 'y (tsubst s1 (hash-ref s2 'y)) 'z '(fn c)) t)))

;; ===== subst: capture-avoidance corner cases =====
;; no clash: bound x is left alone when the substituted term has no x
(check-equal? (subst (hash 'y '(fn a)) '(forall x (atom (rel P (var x) (var y)))))
              '(forall x (atom (rel P (var x) (fn a)))))
;; clash: substituting y -> (var x) under (forall x ...) would capture x, so the
;; bound x is renamed to x^ first
(check-equal? (subst (hash 'y '(var x)) '(forall x (atom (rel P (var x) (var y)))))
              '(forall x^ (atom (rel P (var x^) (var x)))))
;; substituting an away-bound variable is a no-op (y is bound, not free)
(check-equal? (subst (hash 'y '(var x)) '(forall y (atom (rel = (var x) (var y)))))
              '(forall y (atom (rel = (var x) (var y)))))
