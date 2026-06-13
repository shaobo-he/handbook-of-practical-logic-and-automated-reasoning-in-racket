#lang racket/base

(require rackunit)
(require "../equality/equal.rkt"
         "../equality/cong.rkt"
         "../equality/rewrite.rkt"
         "../equality/order.rkt")
(require (only-in "../fol/meson.rkt" meson))

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
