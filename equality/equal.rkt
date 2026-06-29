#lang racket/base

;; equal --- first-order logic with equality: equality axioms and the
;; reduction of equality reasoning to ordinary first-order proving.

(require racket/match)
(require (only-in racket/list range))
(require (only-in "../core/lib.rkt" subtract union))
(require (only-in "../core/formulas.rkt" mk-and mk-forall atom-union end-itlist))
(require (only-in "../fol/fol.rkt" functions))

(provide (all-defined-out))

(define (is-eq fm)
  (match fm
    [`(atom (rel = ,_ ,_)) #t]
    [_ #f]))
(define (mk-eq s t)
  `(atom (rel = ,s ,t)))

;; raises unless fm is a well-formed equation (an atom over rel = of two args)
(define (dest-eq fm)
  (match fm
    [`(atom (rel = ,s ,t)) (cons s t)]
    [_ (error 'dest-eq "not an equation")]))

(define (lhs eq)
  (car (dest-eq eq)))
(define (rhs eq)
  (cdr (dest-eq eq)))

;; ===== predicates appearing in a formula =====
(define (predicates fm)
  (atom-union (λ (a)
                (match a
                  [`(rel ,p ,@args) (list (cons p (length args)))]))
              fm))

;; ===== congruence axioms =====
;; For an n-ary function f, the axiom  x1=y1 /\ ... /\ xn=yn -> f(x...) = f(y...).
;; A constant (n = 0) needs no axiom: c = c already holds by reflexivity. The
;; variables are named x1..xn (left side) and y1..yn (right side).
(define (function-congruence fn)
  (define f (car fn))
  (define n (cdr fn))
  (if (= n 0)
      '()
      (let ()
        (define xs
          (map (λ (i) (string->symbol (string-append "x" (number->string i)))) (range 1 (add1 n))))
        (define ys
          (map (λ (i) (string->symbol (string-append "y" (number->string i)))) (range 1 (add1 n))))
        (define ax (map (λ (x) `(var ,x)) xs))
        (define ay (map (λ (y) `(var ,y)) ys))
        (define ant (end-itlist mk-and (map mk-eq ax ay)))
        (define con (mk-eq `(fn ,f ,@ax) `(fn ,f ,@ay)))
        (list (foldr mk-forall `(imp ,ant ,con) (append xs ys))))))

;; Like function-congruence, but the consequent is an implication P(x...) -> P(y...)
;; rather than an equality: predicates denote truth values, not objects.
(define (predicate-congruence pn)
  (define p (car pn))
  (define n (cdr pn))
  (if (= n 0)
      '()
      (let ()
        (define xs
          (map (λ (i) (string->symbol (string-append "x" (number->string i)))) (range 1 (add1 n))))
        (define ys
          (map (λ (i) (string->symbol (string-append "y" (number->string i)))) (range 1 (add1 n))))
        (define ax (map (λ (x) `(var ,x)) xs))
        (define ay (map (λ (y) `(var ,y)) ys))
        (define ant (end-itlist mk-and (map mk-eq ax ay)))
        (define con `(imp (atom (rel ,p ,@ax)) (atom (rel ,p ,@ay))))
        (list (foldr mk-forall `(imp ,ant ,con) (append xs ys))))))

;; Reflexivity plus the combined (x=y /\ x=z) -> y=z; together these give a full
;; equivalence relation -- symmetry and transitivity both follow from the second.
(define equivalence-axioms
  (list '(forall x (atom (rel = (var x) (var x))))
        '(forall x
                 (forall y
                         (forall z
                                 (imp (and (atom (rel = (var x) (var y)))
                                           (atom (rel = (var x) (var z))))
                                      (atom (rel = (var y) (var z)))))))))

;; Reduce equality reasoning to ordinary first-order logic: if = occurs, return
;; (imp <all relevant congruence and equivalence axioms> fm), which is valid over
;; plain FOL exactly when fm is valid in the theory of equality.
(define (equalitize fm)
  (define allpreds (predicates fm))
  (if (not (member (cons '= 2) allpreds))
      fm
      (let ()
        (define preds (subtract allpreds (list (cons '= 2))))
        (define funcs (functions fm))
        (define axioms
          (foldr (λ (f acc) (union (function-congruence f) acc))
                 (foldr (λ (p acc) (union (predicate-congruence p) acc)) equivalence-axioms preds)
                 funcs))
        `(imp ,(end-itlist mk-and axioms) ,fm))))
