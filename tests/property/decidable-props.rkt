#lang racket/base

;; Property tests for decidable theories: the complex/grobner/real polynomial
;; rings satisfy ring and derivative laws, Cooper linearization matches native
;; arithmetic, QE decides ground (in)equalities, DLO QE removes all quantifiers,
;; and grobner-decide confirms field congruences.

(require rackunit
         rackcheck
         racket/match
         "common.rkt")
(require (only-in racket/list last take remove-duplicates))
(require (only-in "../../decidable/decidable.rkt"
                  alltuples
                  allmappings
                  aedecide
                  wang
                  miniscope
                  decide-finite))
(require (only-in "../../decidable/cooper.rkt"
                  integer-qelim
                  lint
                  dest-numeral
                  mk-numeral
                  linear-add
                  linear-cmul
                  linear-neg
                  evalc
                  zero
                  one))
(require (only-in "../../decidable/qelim.rkt" quelim-dlo cnnf))
(require (only-in "../../decidable/complex.rkt"
                  complex-qelim
                  polynate
                  poly-add
                  poly-neg
                  poly-mul
                  poly-pow
                  poly-sub
                  coefficients
                  degree
                  is-constant
                  head
                  headconst
                  monic))
(require (only-in "../../decidable/real.rkt" real-qelim poly-diff))
(require (only-in "../../decidable/grobner.rkt"
                  grobner-decide
                  mpolynate
                  mpoly-add
                  mpoly-neg
                  mpoly-mul
                  mmul
                  mdiv
                  mlcm
                  morder-lt
                  spoly))
(require (only-in "../../decidable/geom.rkt" coordinate))
(require (only-in "../../decidable/interpolation.rkt" pinterpolate toptermt))
(require (only-in "../../decidable/combining.rkt" add-default int-lang langpartition homogenize))
(require (only-in "../../prop/prop.rkt" tautology))
(require (only-in "../../fol/fol.rkt" fv))

(define (cnum k)
  `(fn ,(string->symbol (number->string k))))

;; polynomial terms over {x,y} with +,-,*,^ (numeral exponent)
(define (poly-term-gen n)
  (if (<= n 0)
      (gen:choice (gen:one-of '((var x) (var y))) (gen:map (gen:integer-in 0 4) cnum))
      (gen:frequency (list (cons 1 (gen:one-of '((var x) (var y))))
                           (cons 1 (gen:map (gen:integer-in 0 4) cnum))
                           (cons 3
                                 (gen:bind (gen:one-of '(+ - *))
                                           (λ (op)
                                             (gen:map (gen:tuple (poly-term-gen (sub1 n))
                                                                 (poly-term-gen (sub1 n)))
                                                      (λ (ab) `(fn ,op ,(car ab) ,(cadr ab)))))))
                           (cons 1
                                 (gen:map (gen:tuple (poly-term-gen (sub1 n)) (gen:integer-in 0 3))
                                          (λ (te) `(fn ^ ,(car te) ,(cnum (cadr te))))))))))
(define pv '(x y))
(define zero-poly (polynate pv '(fn |0|)))
(define zero-mpoly (mpolynate pv '(fn |0|)))

;; complex.rkt nested polynomial ring laws (canonical form => structural equality)
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
                          (equal? (poly-add pv (polynate pv t1) (polynate pv t2))
                                  (poly-add pv (polynate pv t2) (polynate pv t1)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)] [t3 (poly-term-gen 2)])
                          (define p (polynate pv t1))
                          (define q (polynate pv t2))
                          (define r (polynate pv t3))
                          (equal? (poly-mul pv p (poly-add pv q r))
                                  (poly-add pv (poly-mul pv p q) (poly-mul pv p r)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)])
                          (equal? (poly-add pv (polynate pv t1) (poly-neg (polynate pv t1)))
                                  zero-poly)))
;; grobner.rkt monomial-list ring laws
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
                          (equal? (mpoly-add (mpolynate pv t1) (mpolynate pv t2))
                                  (mpoly-add (mpolynate pv t2) (mpolynate pv t1)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)] [t3 (poly-term-gen 2)])
                          (define p (mpolynate pv t1))
                          (define q (mpolynate pv t2))
                          (define r (mpolynate pv t3))
                          (equal? (mpoly-mul p (mpoly-add q r))
                                  (mpoly-add (mpoly-mul p q) (mpoly-mul p r)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)])
                          (equal? (mpoly-add (mpolynate pv t1) (mpoly-neg (mpolynate pv t1)))
                                  zero-mpoly)))
;; real.rkt formal differentiation: linearity and the product rule
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
                          (define p (polynate pv t1))
                          (define q (polynate pv t2))
                          (equal? (poly-diff pv (poly-add pv p q))
                                  (poly-add pv (poly-diff pv p) (poly-diff pv q)))))
(check-property
 poly
 (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
           (define p (polynate pv t1))
           (define q (polynate pv t2))
           (equal? (poly-diff pv (poly-mul pv p q))
                   (poly-add pv (poly-mul pv (poly-diff pv p) q) (poly-mul pv p (poly-diff pv q))))))

;; cooper linearization of a ground term equals its native value
(define (cterm-gen n)
  (if (<= n 0)
      (gen:map (gen:integer-in 0 4) cnum)
      (gen:bind (gen:one-of '(+ - *))
                (λ (op)
                  (gen:map (gen:tuple (cterm-gen (sub1 n)) (cterm-gen (sub1 n)))
                           (λ (ab) `(fn ,op ,(car ab) ,(cadr ab))))))))
(define (cterm-value t)
  (match t
    [`(fn + ,a ,b) (+ (cterm-value a) (cterm-value b))]
    [`(fn - ,a ,b) (- (cterm-value a) (cterm-value b))]
    [`(fn * ,a ,b) (* (cterm-value a) (cterm-value b))]
    [`(fn ,k) (string->number (symbol->string k))]))
(check-property big (property ([t (cterm-gen 2)]) (= (dest-numeral (lint '() t)) (cterm-value t))))

;; QE procedures decide ground (in)equalities correctly
(define (rel-true? op av bv)
  (case op
    [(=) (= av bv)]
    [(<) (< av bv)]
    [(<=) (<= av bv)]
    [(>) (> av bv)]
    [(>=) (>= av bv)]))
(check-property mid
                (property ([op (gen:one-of '(= < <= > >=))] [a (cterm-gen 2)] [b (cterm-gen 2)])
                          (eq? (integer-qelim `(atom (rel ,op ,a ,b)))
                               (rel-true? op (cterm-value a) (cterm-value b)))))
(check-property mid
                (property ([op (gen:one-of '(= < <= > >=))] [a (cterm-gen 2)] [b (cterm-gen 2)])
                          (eq? (real-qelim `(atom (rel ,op ,a ,b)))
                               (rel-true? op (cterm-value a) (cterm-value b)))))
(check-property mid
                (property ([a (cterm-gen 2)] [b (cterm-gen 2)])
                          (eq? (complex-qelim `(atom (rel = ,a ,b)))
                               (= (cterm-value a) (cterm-value b)))))

;; DLO quantifier elimination removes all quantifiers
(define (qfree? fm)
  (match fm
    [`(,(or 'forall 'exists) ,_ ,_) #f]
    [`(not ,p) (qfree? p)]
    [`(,(or 'and 'or 'imp 'iff) ,p ,q) (and (qfree? p) (qfree? q))]
    [_ #t]))
(define (dlo-gen n)
  (define as
    '((atom (rel < (var x) (var y))) (atom (rel < (var y) (var x))) (atom (rel = (var x) (var y)))))
  (if (<= n 0)
      (gen:one-of as)
      (gen:frequency (list (cons 1 (gen:one-of as))
                           (cons 2 (gen:map (dlo-gen (sub1 n)) (λ (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or imp) dlo-gen n))
                           (cons 2 (quant-gen '(forall exists) '(x y z) dlo-gen n))))))
(check-property mid (property ([fm (dlo-gen 3)]) (qfree? (quelim-dlo fm))))

;; grobner-decide confirms congruence over a field: x=y => p(x)=p(y)
(define (x->y t)
  (match t
    [`(var x) '(var y)]
    [`(fn ,f . ,as) `(fn ,f ,@(map x->y as))]
    [_ t]))
(check-property low
                (property ([t (poly-term-gen 2)])
                          (grobner-decide `(imp (atom (rel = (var x) (var y)))
                                                (atom (rel = ,t ,(x->y t)))))))

;; ===== decidable.rkt: finite-model combinatorics =====
;; alltuples n L enumerates exactly |L|^n tuples (0^0 = 1, alltuples 0 = (())).
(define dom-gen (gen:one-of '(() (1) (1 2) (1 2 3))))
(define ran-gen (gen:one-of '((a) (a b) (a b c))))
(check-property big
                (property ([n (gen:integer-in 0 3)] [l
                                                     (gen:one-of '(() (a) (a b) (a b c) (a b c d)))])
                          (= (length (alltuples n l)) (expt (length l) n))))
;; every produced tuple has length n, all elements drawn from L, and (for distinct
;; L) the tuples are pairwise distinct.
(check-property big
                (property ([n (gen:integer-in 0 3)] [l (gen:one-of '((a) (a b) (a b c) (a b c d)))])
                          (define tups (alltuples n l))
                          (and (andmap (λ (t) (and (= (length t) n) (andmap (λ (e) (member e l)) t)))
                                       tups)
                               (= (length tups) (length (remove-duplicates tups))))))
;; allmappings Dom Ran enumerates exactly |Ran|^|Dom| functions.
(check-property big
                (property ([d dom-gen] [r ran-gen])
                          (= (length (allmappings d r)) (expt (length r) (length d)))))

;; ===== decidable.rkt: AE decision (aedecide / wang) over function-free FOL =====
(define (try thunk)
  (with-handlers ([exn:fail? (λ (e) 'threw)])
    (thunk)))
;; unary predicates P,Q over x,y -- no function symbols, so we stay in (or near)
;; the AE-decidable fragment.
(define fol-atoms
  '((atom (rel P (var x))) (atom (rel P (var y))) (atom (rel Q (var x))) (atom (rel Q (var y)))))
;; NNF-style formulas (no imp/iff): miniscope's pushquant logic is built for these.
(define (nnf-fol-gen n)
  (if (<= n 0)
      (gen:one-of fol-atoms)
      (gen:frequency (list (cons 1 (gen:one-of fol-atoms))
                           (cons 2 (gen:map (nnf-fol-gen (sub1 n)) (λ (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or) nnf-fol-gen n))
                           (cons 2 (quant-gen '(forall exists) '(x y) nnf-fol-gen n))))))
;; full propositional connectives too (for aedecide/wang, which nnf internally).
(define (fol-gen n)
  (if (<= n 0)
      (gen:one-of fol-atoms)
      (gen:frequency (list (cons 1 (gen:one-of fol-atoms))
                           (cons 2 (gen:map (fol-gen (sub1 n)) (λ (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or imp iff) fol-gen n))
                           (cons 2 (quant-gen '(forall exists) '(x y) fol-gen n))))))
;; miniscope preserves logical equivalence: it decides identically to the original
;; over all finite models of size 1 and 2 (oracle: decide-finite).
(check-property low
                (property ([fm (nnf-fol-gen 3)])
                          (and (eq? (decide-finite 1 fm) (decide-finite 1 (miniscope fm)))
                               (eq? (decide-finite 2 fm) (decide-finite 2 (miniscope fm))))))
;; aedecide and wang are both complete validity tests for the formulas they accept,
;; so whenever both return a boolean (neither rejects the input) they must agree.
(check-property low
                (property ([fm (fol-gen 3)])
                          (define a (try (λ () (aedecide fm))))
                          (define w (try (λ () (wang fm))))
                          (or (eq? a 'threw) (eq? w 'threw) (eq? a w))))
;; a formula and its negation can never both be valid (negation round-trip).
(check-property low
                (property ([fm (fol-gen 3)])
                          (define a (try (λ () (aedecide fm))))
                          (define an (try (λ () (aedecide `(not ,fm)))))
                          (or (not (boolean? a)) (not (boolean? an)) (not (and a an)))))

;; ===== cooper.rkt: numerals and canonical linear-term arithmetic =====
;; mk-numeral / dest-numeral are inverse on the integers.
(check-property big (property ([n (gen:integer-in -1000 1000)]) (= (dest-numeral (mk-numeral n)) n)))
;; canonical linear terms over {x,y}; coefficients/constant are small integers.
(define (lin-gen n)
  (if (<= n 0)
      (gen:choice (gen:one-of '((var x) (var y))) (gen:map (gen:integer-in -5 5) mk-numeral))
      (gen:frequency (list (cons 1 (gen:one-of '((var x) (var y))))
                           (cons 1 (gen:map (gen:integer-in -5 5) mk-numeral))
                           (cons 3
                                 (gen:bind (gen:one-of '(+ -))
                                           (λ (op)
                                             (gen:map (gen:tuple (lin-gen (sub1 n))
                                                                 (lin-gen (sub1 n)))
                                                      (λ (ab) `(fn ,op ,(car ab) ,(cadr ab)))))))))))
(define lvars '(x y))
(define (lin t)
  (lint lvars t))
;; linear-add is commutative on canonical forms (structural equality).
(check-property poly
                (property ([s (lin-gen 3)] [t (lin-gen 3)])
                          (equal? (linear-add lvars (lin s) (lin t))
                                  (linear-add lvars (lin t) (lin s)))))
;; linear-add associativity.
(check-property poly
                (property ([s (lin-gen 2)] [t (lin-gen 2)] [u (lin-gen 2)])
                          (equal? (linear-add lvars (linear-add lvars (lin s) (lin t)) (lin u))
                                  (linear-add lvars (lin s) (linear-add lvars (lin t) (lin u))))))
;; zero is a two-sided identity for linear-add.
(check-property poly
                (property ([t (lin-gen 3)])
                          (and (equal? (linear-add lvars zero (lin t)) (lin t))
                               (equal? (linear-add lvars (lin t) zero) (lin t)))))
;; linear-neg is an involution.
(check-property poly (property ([t (lin-gen 3)]) (equal? (linear-neg (linear-neg (lin t))) (lin t))))
;; linear-cmul distributes over linear-add.
(check-property
 poly
 (property ([k (gen:integer-in -6 6)] [s (lin-gen 2)] [t (lin-gen 2)])
           (equal? (linear-cmul k (linear-add lvars (lin s) (lin t)))
                   (linear-add lvars (linear-cmul k (lin s)) (linear-cmul k (lin t))))))
;; evalc on a ground atom matches native arithmetic for every relation, including
;; divisibility.
(define (rel-op->proc op)
  (case op
    [(=) =]
    [(<) <]
    [(<=) <=]
    [(>) >]
    [(>=) >=]
    [(divides) (λ (a b) (= (modulo b a) 0))]))
(check-property big
                (property ([op (gen:one-of '(= < <= > >= divides))] [a (gen:integer-in 1 40)]
                                                                    [b (gen:integer-in 1 40)])
                          (eq? (evalc `(atom (rel ,op ,(mk-numeral a) ,(mk-numeral b))))
                               ((rel-op->proc op) a b))))

;; ===== qelim.rkt: cnnf is idempotent (already simplified output) =====
(define cnnf-id (cnnf (λ (x) x)))
(check-property big (property ([fm gen:prop]) (equal? (cnnf-id (cnnf-id fm)) (cnnf-id fm))))

;; ===== complex.rkt: canonical nested-polynomial ring laws =====
;; multiplication is commutative and associative.
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
                          (equal? (poly-mul pv (polynate pv t1) (polynate pv t2))
                                  (poly-mul pv (polynate pv t2) (polynate pv t1)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)] [t3 (poly-term-gen 2)])
                          (define p (polynate pv t1))
                          (define q (polynate pv t2))
                          (define r (polynate pv t3))
                          (equal? (poly-mul pv (poly-mul pv p q) r)
                                  (poly-mul pv p (poly-mul pv q r)))))
;; 1 and 0 are the multiplicative identity / annihilator.
(check-property poly
                (property ([t (poly-term-gen 2)])
                          (define p (polynate pv t))
                          (and (equal? (poly-mul pv p one) p) (equal? (poly-mul pv one p) p))))
(check-property poly
                (property ([t (poly-term-gen 2)])
                          (equal? (poly-mul pv (polynate pv t) zero-poly) zero-poly)))
;; poly-sub p p = 0.
(check-property poly
                (property ([t (poly-term-gen 2)])
                          (equal? (poly-sub pv (polynate pv t) (polynate pv t)) zero-poly)))
;; poly-pow is iterated multiplication: ^0 = 1, ^1 = p, ^2 = p*p.
(check-property poly
                (property ([t (poly-term-gen 2)])
                          (define p (polynate pv t))
                          (and (equal? (poly-pow pv p 0) one)
                               (equal? (poly-pow pv p 1) p)
                               (equal? (poly-pow pv p 2) (poly-mul pv p p)))))
;; structural invariants: degree = #coefficients - 1, head = leading coefficient,
;; constant <=> degree 0.
(check-property poly
                (property ([t (poly-term-gen 2)])
                          (define p (polynate pv t))
                          (and (= (length (coefficients pv p)) (add1 (degree pv p)))
                               (equal? (head pv p) (last (coefficients pv p)))
                               (eq? (is-constant pv p) (= (degree pv p) 0)))))
;; monic normalises the leading coefficient to 1 (or leaves the zero polynomial).
(check-property poly
                (property ([t (poly-term-gen 2)])
                          (define p (polynate pv t))
                          (define-values (p* neg?) (monic p))
                          (= (headconst p*) (if (= (headconst p) 0) 0 1))))

;; ===== grobner.rkt: monomial arithmetic and the polynomial ring =====
;; exponent lists of fixed arity 3, nonzero small integer coefficients.
(define exps3-gen
  (gen:map (gen:tuple (gen:integer-in 0 4) (gen:integer-in 0 4) (gen:integer-in 0 4))
           (λ (t) (list (car t) (cadr t) (caddr t)))))
(define mono-gen
  (gen:map (gen:tuple (gen:integer-in 1 6) exps3-gen) (λ (ce) (cons (car ce) (cadr ce)))))
;; mmul is associative.
(check-property big
                (property ([m1 mono-gen] [m2 mono-gen] [m3 mono-gen])
                          (equal? (mmul (mmul m1 m2) m3) (mmul m1 (mmul m2 m3)))))
;; mdiv undoes mmul (exponents always divide, coefficient is exact).
(check-property big (property ([m1 mono-gen] [m2 mono-gen]) (equal? (mdiv (mmul m1 m2) m2) m1)))
;; mlcm takes componentwise max of exponents with unit coefficient.
(check-property big
                (property ([m1 mono-gen] [m2 mono-gen])
                          (equal? (mlcm m1 m2) (cons 1 (map max (cdr m1) (cdr m2))))))
;; morder-lt is a strict total order: trichotomy and transitivity.
(check-property big
                (property ([e1 exps3-gen] [e2 exps3-gen])
                          (define lt12 (morder-lt e1 e2))
                          (define lt21 (morder-lt e2 e1))
                          (define eq12 (equal? e1 e2))
                          ;; exactly one of <, >, = holds
                          (= 1 (+ (if lt12 1 0) (if lt21 1 0) (if eq12 1 0)))))
(check-property big
                (property ([e1 exps3-gen] [e2 exps3-gen] [e3 exps3-gen])
                          (if (and (morder-lt e1 e2) (morder-lt e2 e3))
                              (morder-lt e1 e3)
                              #t)))
;; mpolynate is a ring homomorphism for +, -, *.
(check-property poly
                (property ([op (gen:one-of '(+ - *))] [t1 (poly-term-gen 1)] [t2 (poly-term-gen 1)])
                          (define lhs (mpolynate pv `(fn ,op ,t1 ,t2)))
                          (define p (mpolynate pv t1))
                          (define q (mpolynate pv t2))
                          (define rhs
                            (case op
                              [(+) (mpoly-add p q)]
                              [(-) (mpoly-add p (mpoly-neg q))]
                              [(*) (mpoly-mul p q)]))
                          (equal? lhs rhs)))
;; canonical form is unique: associatively-regrouped sums map to identical lists.
(check-property poly
                (property ([t1 (poly-term-gen 1)] [t2 (poly-term-gen 1)] [t3 (poly-term-gen 1)])
                          (equal? (mpolynate pv `(fn + (fn + ,t1 ,t2) ,t3))
                                  (mpolynate pv `(fn + ,t1 (fn + ,t2 ,t3))))))
;; mpoly-mul is associative.
(check-property poly
                (property ([t1 (poly-term-gen 1)] [t2 (poly-term-gen 1)] [t3 (poly-term-gen 1)])
                          (define p (mpolynate pv t1))
                          (define q (mpolynate pv t2))
                          (define r (mpolynate pv t3))
                          (equal? (mpoly-mul (mpoly-mul p q) r) (mpoly-mul p (mpoly-mul q r)))))
;; the S-polynomial of a polynomial with itself is zero.
(check-property poly
                (property ([t (poly-term-gen 2)]) (define p (mpolynate pv t)) (null? (spoly p p))))

;; ===== geom.rkt: coordinate translation =====
(define geom-preds
  '((collinear . 3) (parallel . 4)
                    (perpendicular . 4)
                    (lengths_eq . 4)
                    (is_midpoint . 3)
                    (is_intersection . 5)
                    (= . 2)))
(define geom-vars '(a b c d e))
(define geom-atom-gen
  (gen:map (gen:one-of geom-preds)
           (λ (pa) `(atom (rel ,(car pa) ,@(map (λ (v) `(var ,v)) (take geom-vars (cdr pa))))))))
(define (geom-gen n)
  (if (<= n 0)
      geom-atom-gen
      (gen:frequency (list (cons 1 geom-atom-gen)
                           (cons 1 (gen:map (geom-gen (sub1 n)) (λ (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or) geom-gen n))))))
;; every coordinate predicate is expanded into algebraic equations: the only
;; relation symbol surviving in the output is `=`.
(define (all-rel-eq? fm)
  (match fm
    [`(atom (rel ,a ,@_)) (eq? a '=)]
    [`(not ,p) (all-rel-eq? p)]
    [`(,(or 'and 'or 'imp 'iff) ,p ,q) (and (all-rel-eq? p) (all-rel-eq? q))]
    [_ #t]))
(check-property big (property ([fm (geom-gen 3)]) (all-rel-eq? (coordinate fm))))

;; ===== interpolation.rkt: propositional Craig interpolation =====
;; (p => I) is a tautology for the interpolant of ANY pair (orify only weakens p).
(check-property big (property ([p gen:prop] [q gen:prop]) (tautology `(imp ,p ,(pinterpolate p q)))))
;; for a guaranteed-unsatisfiable pair p = base /\ x, q = ~base /\ y the full Craig
;; property holds: p => I and I => ~q.
(check-property mid
                (property ([base gen:prop] [x gen:prop] [y gen:prop])
                          (define p `(and ,base ,x))
                          (define q `(and (not ,base) ,y))
                          (define ip (pinterpolate p q))
                          (and (tautology `(imp ,p ,ip)) (tautology `(imp ,ip (not ,q))))))
;; toptermt: variables yield no topmost terms, and every term it returns is headed
;; by a function symbol in the given set.
(define fns-gen
  (gen:one-of '(() ((a . 0)) ((f . 1)) ((g . 2)) ((a . 0) (f . 1)) ((a . 0) (f . 1) (g . 2)))))
(check-property big
                (property ([fns fns-gen] [tm gen:term])
                          (define tts (toptermt fns tm))
                          (andmap (λ (t)
                                    (match t
                                      [`(fn ,f ,@args) (and (member (cons f (length args)) fns) #t)]
                                      [_ #f]))
                                  tts)))

;; ===== combining.rkt: homogenization and language partition =====
;; literals that are cleanly owned by int-lang (arithmetic) or the default theory
;; (uninterpreted functions under equality).
(define ho-pool
  '((atom (rel < (var x) (var y))) (atom (rel <= (fn + (var x) (var y)) (var z)))
                                   (atom (rel > (fn * (var x) (var y)) (var z)))
                                   (atom (rel = (var x) (var y)))
                                   (atom (rel = (fn f (var x)) (var y)))
                                   (atom (rel = (fn g (var x) (var y)) (var z)))))
;; homogenize keeps every original free variable; any variable it introduces is a
;; fresh v_<n>.
(check-property mid
                (property ([fms (gen:list (gen:one-of ho-pool) #:max-length 4)])
                          (define langs (add-default (list int-lang)))
                          (define res (try (λ () (homogenize langs fms))))
                          (cond
                            [(eq? res 'threw) #t]
                            [else
                             (define orig (remove-duplicates (apply append (map fv fms))))
                             (define after (remove-duplicates (apply append (map fv res))))
                             (and (andmap (λ (v) (and (member v after) #t)) orig)
                                  (andmap (λ (v)
                                            (or (member v orig)
                                                (let ([s (symbol->string v)])
                                                  (and (>= (string-length s) 2)
                                                       (string=? (substring s 0 2) "v_")))))
                                          after))])))
;; langpartition is a disjoint cover: the parts concatenate back to the input.
(check-property mid
                (property ([fms (gen:list (gen:one-of ho-pool) #:max-length 4)])
                          (define langs (add-default (list int-lang)))
                          (define flat (apply append (langpartition langs fms)))
                          (and (= (length flat) (length fms))
                               (andmap (λ (f) (and (member f flat) #t)) fms))))
