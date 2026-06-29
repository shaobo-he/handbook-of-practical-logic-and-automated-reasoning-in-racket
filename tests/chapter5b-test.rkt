#lang racket/base

(require rackunit)
(require "../decidable/geom.rkt"
         "../decidable/interpolation.rkt"
         "../decidable/combining.rkt")
(require (only-in "../prop/prop.rkt" tautology))
(require (only-in "../fol/meson.rkt" meson))

(define (provable? fm)
  (andmap exact-nonnegative-integer? (meson fm)))

;; ===== geom =====
(check-equal? (coordinate '(atom (rel collinear (var a) (var b) (var c))))
              '(atom (rel =
                          (fn * (fn - (var a_x) (var b_x)) (fn - (var b_y) (var c_y)))
                          (fn * (fn - (var a_y) (var b_y)) (fn - (var b_x) (var c_x))))))
;; Wu's method on the isosceles-triangle theorem runs and yields conditions
(check-pred list?
            (wu '(imp (and (atom (rel is_midpoint (var m) (var a) (var c)))
                           (atom (rel perpendicular (var a) (var c) (var m) (var b))))
                      (atom (rel lengths_eq (var a) (var b) (var c) (var b))))
                '(|a_x| |a_y| |b_x| |b_y| |c_x| |c_y| |m_x| |m_y|)
                '()))

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
(check-true (provable? `(imp ,P ,c))) ; P ==> C
(check-true (provable? `(imp ,c (not ,Q)))) ; C ==> ~Q

;; ===== combining: Nelson-Oppen =====
;; pure congruence (handled by the default/uninterpreted language)
(check-true (nelop (add-default (list int-lang))
                   '(imp (atom (rel = (var x) (var y)))
                         (atom (rel = (fn f (var x)) (fn f (var y)))))))
(check-false (nelop (add-default (list int-lang))
                    '(imp (atom (rel = (fn f (var x)) (fn f (var y))))
                          (atom (rel = (var x) (var y))))))
;; genuine combination: integer arithmetic forces x = y, then congruence gives f(x)=f(y)
(check-true (nelop (add-default (list int-lang))
                   '(imp (and (and (atom (rel <= (var x) (var y)))
                                   (atom (rel <= (var y) (fn + (var x) (var z)))))
                              (atom (rel = (var z) (fn |0|))))
                         (atom (rel = (fn f (var x)) (fn f (var y)))))))

;; ===== geom: symbol mangling, coordinate dictionary, coordinatisation =====
(check-equal? (sym+ 'p "_x") 'p_x)
(check-false (equal? (sym+ 'a "_x") (sym+ 'a "_y")))
(check-equal? (length coordinations) 7)
(check-equal? (map car coordinations)
              '(collinear parallel perpendicular lengths_eq is_midpoint is_intersection =))
;; parallel expands to the cross-product-zero equation
(check-equal? (coordinate '(atom (rel parallel (var a) (var b) (var c) (var d))))
              '(atom (rel =
                          (fn * (fn - (var a_x) (var b_x)) (fn - (var c_y) (var d_y)))
                          (fn * (fn - (var a_y) (var b_y)) (fn - (var c_x) (var d_x))))))
;; point equality expands to a conjunction of x- and y-coordinate equalities
(check-equal? (coordinate '(atom (rel = (var p) (var q))))
              '(and (atom (rel = (var p_x) (var q_x))) (atom (rel = (var p_y) (var q_y)))))
;; originate zeroes the first point's coordinates and the second point's y-coordinate
(check-equal? (originate '(atom (rel collinear (var a) (var b) (var c))))
              '(atom (rel =
                          (fn * (fn - (fn |0|) (var b_x)) (fn - (fn |0|) (var c_y)))
                          (fn * (fn - (fn |0|) (fn |0|)) (fn - (var b_x) (var c_x))))))
;; Wu's method on a trivial tautology yields no degenerate conditions
(check-equal? (wu '(imp (atom (rel collinear (var a) (var b) (var c)))
                        (atom (rel collinear (var a) (var b) (var c))))
                  '(|a_x| |a_y| |b_x| |b_y| |c_x| |c_y|)
                  '())
              '())

;; ===== interpolation: topmost-term extraction =====
;; variables contribute nothing; only terms headed by a symbol in the set survive,
;; and the recursion stops at the first matching layer.
(check-equal? (toptermt '((a . 0) (f . 1)) '(var x)) '())
(check-equal? (toptermt '((a . 0)) '(fn a)) '((fn a)))
(check-equal? (toptermt '((f . 1)) '(fn f (var x))) '((fn f (var x))))
(check-equal? (toptermt '((a . 0)) '(fn f (var x))) '())
(check-equal? (toptermt '((a . 0)) '(fn g (fn a) (var y))) '((fn a)))
(check-equal? (topterms '((a . 0) (f . 1)) '(atom (rel P (var x)))) '())
(check-equal? (topterms '((a . 0)) '(atom (rel P (fn a)))) '((fn a)))
;; urinterpolate computes the relational interpolant of an unsatisfiable universal pair
(define ui
  (urinterpolate '(and (atom (rel P (fn a))) (atom (rel Q (fn a))))
                 '(and (not (atom (rel Q (fn a)))) (atom (rel S (fn a))))))
(check-equal? ui '(atom (rel Q (fn a))))
(check-true (tautology `(imp (and (atom (rel P (fn a))) (atom (rel Q (fn a)))) ,ui)))
(check-true (tautology `(imp ,ui (not (and (not (atom (rel Q (fn a)))) (atom (rel S (fn a))))))))
;; a full first-order Craig interpolant (with a quantifier) on an unsatisfiable pair
(define P2
  '(and (atom (rel R (var x))) (forall y (imp (atom (rel R (var y))) (atom (rel S (var y)))))))
(define Q2 '(not (atom (rel S (var x)))))
(define c2 (interpolate P2 Q2))
(check-true (provable? `(imp ,P2 ,c2))) ; P2 ==> C
(check-true (provable? `(imp ,c2 (not ,Q2)))) ; C ==> ~Q2

;; ===== combining: languages, membership, homogenisation =====
;; add-default appends exactly one theory, whose only predicate is equality
(define dl (add-default (list int-lang)))
(check-equal? (length dl) 2)
(check-true ((cadr (cadr dl)) (cons '= 2)))
(check-false ((cadr (cadr dl)) (cons '< 2)))
;; belongs: arithmetic atoms belong to int-lang; equality belongs to every language;
;; an uninterpreted function symbol does not belong to int-lang
(check-true (belongs int-lang '(atom (rel < (var x) (var y)))))
(check-true (belongs int-lang '(atom (rel = (var x) (var y)))))
(check-true (belongs int-lang '(atom (rel < (fn + (var x) (var y)) (var z)))))
(check-false (belongs int-lang '(atom (rel < (fn f (var x)) (var y)))))
;; a formula owned by no supplied language makes langpartition error
(check-exn exn:fail? (λ () (langpartition (list int-lang) '((atom (rel R (var x)))))))
;; homogenize abstracts the alien subterm f(x) into a fresh v_1 with a defining equation
(check-equal? (homogenize dl '((atom (rel < (fn f (var x)) (var y)))))
              '((atom (rel < (var v_1) (var y))) (atom (rel = (var v_1) (fn f (var x))))))
;; arrangement: equalities inside a block, disequalities between block representatives
(check-equal? (arrangement '((x y) (z)))
              '((atom (rel = (var x) (var y))) (not (atom (rel = (var x) (var z))))))
;; redeqs eliminates a trivial definition x = 5 by substituting it everywhere
(check-equal? (redeqs (list '(atom (rel = (var x) (fn |5|))) '(atom (rel < (var x) (var y)))))
              '((atom (rel < (fn |5|) (var y)))))
;; Nelson-Oppen: a clear contradiction is refuted, and congruence holds over the reals
(check-false (nelop dl '(not (atom (rel = (var x) (var x))))))
(check-true (nelop (add-default (list real-lang))
                   '(imp (atom (rel = (var x) (var y)))
                         (atom (rel = (fn f (var x)) (fn f (var y)))))))
