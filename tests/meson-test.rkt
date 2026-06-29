#lang racket/base

;; Unit tests for meson.rkt: clause contrapositives, the cycle-detection helper
;; meson-equal?, and the two MESON drivers (meson001 = basic, meson002 = with
;; repetition checking + divide-and-conquer). The provers run only on theorems.

(require rackunit)
(require "../fol/meson.rkt")
(require (only-in "../core/lib.rkt" undefined update))

;; ===== contrapositives: one (body . head) rule per literal =====
;; a mixed clause yields one rule per literal (the others negated as the body)
(check-equal? (contrapositives (list '(atom (rel P)) '(atom (rel Q))))
              (list (cons (list '(not (atom (rel Q)))) '(atom (rel P)))
                    (cons (list '(not (atom (rel P)))) '(atom (rel Q)))))
;; an all-negative clause adds the special goal rule (positives . #f) up front
(check-equal? (contrapositives (list '(not (atom (rel P))) '(not (atom (rel Q)))))
              (list (cons (list '(atom (rel P)) '(atom (rel Q))) #f)
                    (cons (list '(atom (rel Q))) '(not (atom (rel P))))
                    (cons (list '(atom (rel P))) '(not (atom (rel Q))))))

;; ===== meson-equal?: do the literals unify WITHOUT changing the env? =====
;; identical literals unify with no new binding -> #t
(check-true (meson-equal? undefined '(atom (rel P (var x))) '(atom (rel P (var x)))))
;; already-satisfied under the env (x is bound to q) -> #t
(check-true
 (meson-equal? (update 'x '(fn q) undefined) '(atom (rel P (var x))) '(atom (rel P (fn q)))))
;; unifiable but only by ADDING a binding -> #f (not "equal")
(check-false (meson-equal? undefined '(atom (rel P (var x))) '(atom (rel P (var y)))))
;; not unifiable at all (different relation) -> #f
(check-false (meson-equal? undefined '(atom (rel P (var x))) '(atom (rel Q (var x)))))

;; ===== meson001 / meson002 agree on known theorems =====
(define peirce '(imp (imp (imp (atom (rel P)) (atom (rel Q))) (atom (rel P))) (atom (rel P))))
(define drinker '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y)))))))
(define (all-nat? l)
  (andmap exact-nonnegative-integer? l))

(check-pred all-nat? (meson001 peirce))
(check-pred all-nat? (meson002 peirce))
(check-pred all-nat? (meson001 drinker))
(check-pred all-nat? (meson002 drinker))
;; drinker genuinely needs a refutation, so both return a non-empty proof list
(check-pred pair? (meson001 drinker))
(check-pred pair? (meson002 drinker))
