#lang racket/base

(require rackunit)
(require "../equality/completion.rkt" "../equality/eqelim.rkt" "../equality/paramodulation.rkt" "../fol/skolems.rkt")
(require (only-in "../equality/rewrite.rkt" rewrite))

(define (all-true? l) (andmap (λ (x) (eq? x #t)) l))
(define (all-nat? l) (andmap exact-nonnegative-integer? l))

;; ===== Knuth-Bendix completion of group theory =====
(define group-eqs
  (list '(atom (rel = (fn * (fn * (var x) (var y)) (var z)) (fn * (var x) (fn * (var y) (var z)))))
        '(atom (rel = (fn * (fn |1|) (var x)) (var x)))
        '(atom (rel = (fn * (fn i (var x)) (var x)) (fn |1|)))))
(define group-rules (complete-and-simplify '(|1| * i) group-eqs))
(check-pred list? group-rules)
(check-true (>= (length group-rules) 3))
;; the completed system proves standard group identities by rewriting
(check-equal? (rewrite group-rules '(fn i (fn |1|))) '(fn |1|))              ; i(1) = 1
(check-equal? (rewrite group-rules '(fn i (fn i (var x)))) '(var x))         ; i(i(x)) = x

;; ===== equality reasoning: symmetry a = b ==> b = a =====
(define sym '(imp (atom (rel = (var a) (var b))) (atom (rel = (var b) (var a)))))
(check-true (all-true? (paramodulation sym)))
(check-pred all-nat? (bmeson sym))
(check-pred all-nat? (emeson sym))

;; ===== Skolemizing a set of formulas at once =====
(define sk (skolemizes (list '(exists x (atom (rel P (var x))))
                             '(exists y (atom (rel Q (var y)))))))
(check-equal? (length sk) 2)
