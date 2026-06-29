#lang racket/base

(require rackunit)
(require "../equality/equal.rkt"
         "../equality/cong.rkt"
         "../equality/rewrite.rkt"
         "../equality/order.rkt")
(require (only-in "../fol/meson.rkt" meson))
(require (only-in "../core/lib.rkt" undefined unequal equate))

;; ===== equal: accessors and axiom generation =====
(check-true (is-eq '(atom (rel = (var x) (var y)))))
(check-false (is-eq '(atom (rel P (var x)))))
(check-equal? (dest-eq '(atom (rel = (fn a) (fn b)))) (cons '(fn a) '(fn b)))
(check-equal? (predicates '(and (atom (rel = (var x) (var y))) (atom (rel P (var x)))))
              (list (cons '= 2) (cons 'P 1)))
;; unary function congruence axiom
(check-equal? (function-congruence (cons 'f 1))
              (list '(forall x1
                             (forall y1
                                     (imp (atom (rel = (var x1) (var y1)))
                                          (atom (rel = (fn f (var x1)) (fn f (var y1)))))))))
;; equalitize wraps the goal in an implication from the axioms
(define eqgoal
  '(imp (forall x (atom (rel = (fn f (var x)) (var x)))) (atom (rel = (fn f (fn c)) (fn c)))))
(check-pred (λ (r) (and (pair? r) (eq? (car r) 'imp))) (equalitize eqgoal))
;; ...and the resulting pure-FOL formula is provable by MESON
(check-pred (λ (l) (andmap exact-nonnegative-integer? l)) (meson (equalitize eqgoal)))

;; ===== cong: congruence-closure validity (a decision procedure) =====
(check-true (ccvalid '(imp (atom (rel = (var c) (var d)))
                           (atom (rel = (fn f (var c)) (fn f (var d)))))))
(check-false (ccvalid '(atom (rel = (var c) (var d)))))

;; ===== rewrite: normalise with equations  0+x=x ; S(x)+y=S(x+y) =====
(define arith-eqs
  (list '(atom (rel = (fn + (fn |0|) (var x)) (var x)))
        '(atom (rel = (fn + (fn S (var x)) (var y)) (fn S (fn + (var x) (var y)))))))
(define (num n)
  (if (= n 0)
      '(fn |0|)
      `(fn S ,(num (- n 1)))))
(check-equal? (rewrite arith-eqs `(fn + ,(num 2) ,(num 2))) (num 4))

;; ===== order: term size and lexicographic path order =====
(check-equal? (termsize '(fn f (fn g (var x)) (var y))) 4)
(define w (λ (p q) (weight '(c f g) p q))) ; precedence c < f < g
(check-true (lpo-gt w '(fn f (var x)) '(var x))) ; f(x) > x  (subterm)
(check-true (weight '(a b) '(b . 0) '(a . 0))) ; b > a
(check-false (weight '(a b) '(a . 0) '(b . 0)))
(check-true (lpo-gt w '(fn g (var x)) '(fn f (var x)))) ; g(x) > f(x) by precedence
(check-false (lpo-gt w '(fn f (var x)) '(fn g (var x))))

;; ===== more equality coverage =====
;; constants (arity 0) get no congruence axiom
(check-equal? (function-congruence (cons 'c 0)) '())
;; congruence closure decides transitivity of equality
(check-true (ccvalid '(imp (and (atom (rel = (var a) (var b))) (atom (rel = (var b) (var c))))
                           (atom (rel = (var a) (var c))))))
;; rewriting to normal form with an idempotence rule  f(f(x)) = f(x)
(check-equal? (rewrite (list '(atom (rel = (fn f (fn f (var x))) (fn f (var x)))))
                       '(fn f (fn f (fn f (var a)))))
              '(fn f (var a)))

;; ===== equal: lhs/rhs accessors and the dest-eq error on non-equations =====
(check-equal? (lhs (mk-eq '(fn f (var x)) '(fn g (var y)))) '(fn f (var x)))
(check-equal? (rhs (mk-eq '(fn f (var x)) '(fn g (var y)))) '(fn g (var y)))
;; lhs/rhs go through dest-eq, which rejects anything that is not (rel = _ _)
(check-exn #rx"dest-eq" (λ () (dest-eq '(atom (rel P (var x))))))
(check-exn exn:fail? (λ () (lhs '(atom (rel P (var x))))))
(check-exn exn:fail? (λ () (rhs '(atom (rel P (var x))))))

;; ===== equal: predicate congruence (dual to function congruence) =====
;; arity 1:  x1 = y1  ->  (P(x1) -> P(y1))   -- note: implication, not equality,
;; because predicates denote truth values rather than objects
(check-equal? (predicate-congruence (cons 'P 1))
              (list '(forall x1
                             (forall y1
                                     (imp (atom (rel = (var x1) (var y1)))
                                          (imp (atom (rel P (var x1))) (atom (rel P (var y1)))))))))
;; arity 2 introduces x1,x2,y1,y2 with that exact quantifier nesting
(check-equal?
 (predicate-congruence (cons 'Q 2))
 (list '(forall x1
                (forall x2
                        (forall y1
                                (forall y2
                                        (imp (and (atom (rel = (var x1) (var y1)))
                                                  (atom (rel = (var x2) (var y2))))
                                             (imp (atom (rel Q (var x1) (var x2)))
                                                  (atom (rel Q (var y1) (var y2)))))))))))
;; a 0-ary predicate (a propositional constant) needs no congruence axiom
(check-equal? (predicate-congruence (cons 'R 0)) '())

;; ===== equal: predicates appearing in a formula =====
(check-equal? (predicates '(atom (rel P (var x)))) (list (cons 'P 1)))
;; the #t/#f constants contain no predicate atoms
(check-equal? (predicates #t) '())
(check-equal? (predicates #f) '())

;; ===== equal: equivalence axioms (reflexivity + combined sym/trans) =====
(check-equal? (length equivalence-axioms) 2)
;; first axiom is reflexivity  forall x. x = x
(check-equal? (car equivalence-axioms) '(forall x (atom (rel = (var x) (var x)))))
;; second axiom is the (x=y and x=z) -> y=z form, from which symmetry follows
(check-eq? (car (cadr equivalence-axioms)) 'forall)

;; ===== equal: equalitize reduces equality reasoning to plain FOL =====
;; with no equality relation the formula is returned unchanged
(check-equal? (equalitize '(atom (rel P (var x)))) '(atom (rel P (var x))))
;; otherwise it becomes (imp <conjoined axioms> <original goal>)
(let ([e (equalitize '(atom (rel = (var x) (var y))))])
  (check-eq? (car e) 'imp)
  (check-equal? (caddr e) '(atom (rel = (var x) (var y)))))

;; ===== cong: subterms = the term itself together with all proper subterms =====
(let ([ss (subterms '(fn f (fn g (var x))))])
  (check-equal? (length ss) 3) ; no duplicates
  (check-true (and (member '(fn f (fn g (var x))) ss) #t))
  (check-true (and (member '(fn g (var x)) ss) #t))
  (check-true (and (member '(var x) ss) #t)))
(let ([ss (subterms '(fn g (fn a) (fn b)))])
  (check-equal? (length ss) 3)
  (check-true (and (member '(fn g (fn a) (fn b)) ss) #t))
  (check-true (and (member '(fn a) ss) #t))
  (check-true (and (member '(fn b) ss) #t)))
;; a variable is its own only subterm
(check-equal? (subterms '(var x)) '((var x)))

;; ===== cong: congruent needs equal symbol, equal arity, equivalent args =====
(check-false (congruent undefined (cons '(fn f (var x)) '(fn f (var y))))) ; args not yet equal
(check-false (congruent unequal (cons '(fn f (var x)) '(fn g (var x))))) ; different symbol
(check-false (congruent unequal (cons '(fn f (var x) (var y)) '(fn f (var x))))) ; different arity
(check-false (congruent unequal (cons '(var x) '(var y)))) ; not compound terms
;; once a = b is asserted, f(a) and f(b) become congruent
(check-true (congruent (equate (cons '(fn a) '(fn b)) unequal) (cons '(fn f (fn a)) '(fn f (fn b)))))

;; ===== cong: ccsatisfiable on ground equations/inequations =====
;; a = b together with a <> b is unsatisfiable
(check-false (ccsatisfiable (list '(atom (rel = (fn a) (fn b))) '(not (atom (rel = (fn a) (fn b)))))))
;; a lone positive equation is satisfiable
(check-true (ccsatisfiable (list '(atom (rel = (fn a) (fn b))))))

;; ===== cong: ccvalid is false on contradictions and bare equations =====
(check-false (ccvalid '(and (atom (rel = (var a) (var b))) (not (atom (rel = (var a) (var b)))))))
(check-false (ccvalid '(atom (rel = (var a) (var b)))))

;; ===== rewrite: rewrite1 rewrites once with the first matching equation =====
(check-equal? (rewrite1 (list (mk-eq '(fn a) '(fn b))) '(fn a)) '(fn b))
;; the first matching equation wins, even when a later one also matches
(check-equal? (rewrite1 (list (mk-eq '(fn a) '(fn b)) (mk-eq '(fn a) '(fn c))) '(fn a)) '(fn b))
;; non-matching equations are skipped until one applies
(check-equal? (rewrite1 (list (mk-eq '(fn f (fn g (var x))) '(fn a)) (mk-eq '(fn g (var y)) '(fn b)))
                        '(fn g (fn c)))
              '(fn b))
;; with no applicable equation rewrite1 raises
(check-exn #rx"rewrite1" (λ () (rewrite1 (list (mk-eq '(fn a) '(fn b))) '(fn c))))
;; a bare variable is never rewritten by a function-headed rule
(check-equal? (rewrite (list (mk-eq '(fn f (var x)) '(var y))) '(var z)) '(var z))

;; ===== order: termsize edges and additivity =====
(check-equal? (termsize '(var x)) 1)
(check-equal? (termsize '(fn c)) 1) ; a constant
(check-equal? (termsize '(fn f (var x) (var y) (var z))) 4)

;; ===== order: lexord (lexicographic extension of an order) =====
;; empty argument lists are never ordered
(check-false (lexord (λ (a b) #t) '() '()))
;; ord on heads decides, but only when the tails have equal length
(check-true (lexord (λ (a b) (< a b)) '(1 2) '(2 1)))
;; a constant-false ord can never order, even with equal heads
(check-false (lexord (λ (a b) #f) '(a a) '(a a)))

;; ===== order: lexicographic path order, more cases =====
(define w3 (λ (p q) (weight '(c f g) p q)))
;; subterm property with a 3-ary function: h(x,y,z) > each argument
(check-true (lpo-gt w3 '(fn h (var x) (var y) (var z)) '(var y)))
;; the strict order is irreflexive
(check-false (lpo-gt w3 '(fn g (fn c) (fn c)) '(fn g (fn c) (fn c))))
;; lpo-ge is reflexive and subsumes the strict subterm case
(check-true (lpo-ge w3 '(fn f (var x)) '(fn f (var x))))
(check-true (lpo-ge w3 '(fn f (var x)) '(var x)))

;; ===== order: weight precedence, with arity as the tie-breaker =====
;; same symbol: the larger arity is the heavier (greater) of the two
(check-false (weight '(a) (cons 'a 0) (cons 'a 1)))
(check-true (weight '(a b) (cons 'a 2) (cons 'a 1)))
(check-false (weight '(a b) (cons 'a 1) (cons 'a 2)))
