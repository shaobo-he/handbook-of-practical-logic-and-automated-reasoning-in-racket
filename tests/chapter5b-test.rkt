#lang racket/base

(require rackunit)
(require "../decidable/geom.rkt" "../decidable/interpolation.rkt" "../decidable/combining.rkt")
(require (only-in "../prop/prop.rkt" tautology))
(require (only-in "../fol/meson.rkt" meson))

(define (provable? fm) (andmap exact-nonnegative-integer? (meson fm)))

;; ===== geom =====
(check-equal? (coordinate '(atom (rel collinear (var a) (var b) (var c))))
              '(atom (rel = (fn * (fn - (var a_x) (var b_x)) (fn - (var b_y) (var c_y)))
                            (fn * (fn - (var a_y) (var b_y)) (fn - (var b_x) (var c_x))))))
;; Wu's method on the isosceles-triangle theorem runs and yields conditions
(check-pred list?
            (wu '(imp (and (atom (rel is_midpoint (var m) (var a) (var c)))
                           (atom (rel perpendicular (var a) (var c) (var m) (var b))))
                      (atom (rel lengths_eq (var a) (var b) (var c) (var b))))
                '(|a_x| |a_y| |b_x| |b_y| |c_x| |c_y| |m_x| |m_y|) '()))

;; ===== interpolation =====
;; propositional: interpolant of (r /\ q) and (~q /\ s)
(define ip (pinterpolate '(and (atom r) (atom q)) '(and (not (atom q)) (atom s))))
(check-equal? ip '(atom q))
(check-true (tautology `(imp (and (atom r) (atom q)) ,ip)))
(check-true (tautology `(imp ,ip (not (and (not (atom q)) (atom s))))))
;; first-order Craig interpolation for an unsatisfiable P(a)/\Q(a) , ~Q(a)/\S(a)
(define P '(and (atom (rel P (fn a))) (atom (rel Q (fn a)))))
(define Q '(and (not (atom (rel Q (fn a)))) (atom (rel S (fn a)))))
(define c (interpolate P Q))
(check-true (provable? `(imp ,P ,c)))            ; P ==> C
(check-true (provable? `(imp ,c (not ,Q))))      ; C ==> ~Q

;; ===== combining: Nelson-Oppen =====
;; pure congruence (handled by the default/uninterpreted language)
(check-true (nelop (add-default (list int-lang))
                   '(imp (atom (rel = (var x) (var y))) (atom (rel = (fn f (var x)) (fn f (var y)))))))
(check-false (nelop (add-default (list int-lang))
                    '(imp (atom (rel = (fn f (var x)) (fn f (var y)))) (atom (rel = (var x) (var y))))))
;; genuine combination: integer arithmetic forces x = y, then congruence gives f(x)=f(y)
(check-true (nelop (add-default (list int-lang))
                   '(imp (and (and (atom (rel <= (var x) (var y)))
                                   (atom (rel <= (var y) (fn + (var x) (var z)))))
                              (atom (rel = (var z) (fn |0|))))
                         (atom (rel = (fn f (var x)) (fn f (var y)))))))
