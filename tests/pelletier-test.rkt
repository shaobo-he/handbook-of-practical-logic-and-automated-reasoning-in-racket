#lang racket/base

;; A selection of Pelletier's problems -- the classic regression suite for
;; first-order provers. Propositional ones are checked with the truth-table
;; reference; first-order ones are proved with MESON and the tableau prover.

(require rackunit)
(require (only-in "../prop/prop.rkt" tautology))
(require (only-in "../fol/meson.rkt" meson))
(require (only-in "../fol/tableaux.rkt" tab splittab))

;; MESON returns one proof depth per DNF disjunct of the negated goal;
;; returning a list of naturals (never raising) means "proved".
(define (meson-proves? fm)
  (andmap exact-nonnegative-integer? (meson fm)))
;; tab returns the depth at which a refutation was found.
(define (tab-proves? fm)
  (exact-nonnegative-integer? (tab fm)))

;; ===== propositional (Pelletier 1-17) =====
(check-true (tautology '(iff (imp (atom (rel p)) (atom (rel q)))
                             (imp (not (atom (rel q))) (not (atom (rel p))))))) ; P1
(check-true (tautology '(iff (not (not (atom (rel p)))) (atom (rel p))))) ; P2
(check-true (tautology '(imp (not (imp (atom (rel p)) (atom (rel q))))
                             (imp (atom (rel q)) (atom (rel p)))))) ; P3
(check-true (tautology '(iff (imp (not (atom (rel p))) (atom (rel q)))
                             (imp (not (atom (rel q))) (atom (rel p)))))) ; P4
(check-true (tautology '(imp (imp (imp (atom (rel p)) (atom (rel q))) (atom (rel p)))
                             (atom (rel p))))) ; P8 (Peirce)
(check-true (tautology '(or (imp (atom (rel p)) (atom (rel q)))
                            (imp (atom (rel q)) (atom (rel p)))))) ; P16
(check-true
 (tautology '(iff (imp (and (atom (rel p)) (imp (atom (rel q)) (atom (rel r)))) (atom (rel s)))
                  (and (or (or (not (atom (rel p))) (atom (rel q))) (atom (rel s)))
                       (or (or (not (atom (rel p))) (not (atom (rel r)))) (atom (rel s))))))) ; P17
(check-true (tautology '(imp (imp (or (atom (rel p)) (atom (rel q)))
                                  (or (atom (rel p)) (atom (rel r))))
                             (or (atom (rel p)) (imp (atom (rel q)) (atom (rel r))))))) ; P5
(check-true (tautology '(imp (and (and (or (atom (rel p)) (atom (rel q)))
                                       (or (not (atom (rel p))) (atom (rel q))))
                                  (or (atom (rel p)) (not (atom (rel q)))))
                             (not (or (not (atom (rel p))) (not (atom (rel q)))))))) ; P9

;; ===== first-order (Pelletier 18-39) via MESON =====
(check-true (meson-proves?
             '(exists y (forall x (imp (atom (rel F (var y))) (atom (rel F (var x)))))))) ; P18
(check-true (meson-proves? '(exists x
                                    (forall y
                                            (forall z
                                                    (imp (imp (atom (rel P (var y)))
                                                              (atom (rel Q (var z))))
                                                         (imp (atom (rel P (var x)))
                                                              (atom (rel Q (var x)))))))))) ; P19
(check-true (meson-proves? '(imp (forall x (iff (atom (rel P)) (atom (rel F (var x)))))
                                 (iff (atom (rel P)) (forall x (atom (rel F (var x)))))))) ; P22
(check-true (meson-proves? '(iff (forall x (or (atom (rel P)) (atom (rel F (var x)))))
                                 (or (atom (rel P)) (forall x (atom (rel F (var x)))))))) ; P23
(check-true (meson-proves?
             '(exists x
                      (exists y
                              (imp (atom (rel P (var x) (var y)))
                                   (forall x (forall y (atom (rel P (var x) (var y)))))))))) ; P35
(check-true (meson-proves?
             '(not (exists x
                           (forall y
                                   (iff (atom (rel F (var y) (var x)))
                                        (not (atom (rel F (var y) (var y)))))))))) ; P39 (Russell)
(check-true
 (meson-proves?
  '(imp (forall x
                (forall y
                        (exists z
                                (forall w
                                        (imp (and (atom (rel P (var x))) (atom (rel Q (var y))))
                                             (and (atom (rel R (var z))) (atom (rel U (var w)))))))))
        (imp (exists x (exists y (and (atom (rel P (var x))) (atom (rel Q (var y))))))
             (exists z (atom (rel R (var z)))))))) ; P20
(check-true (meson-proves? '(imp (and (exists x (imp (atom (rel P)) (atom (rel F (var x)))))
                                      (exists x (imp (atom (rel F (var x))) (atom (rel P)))))
                                 (exists x (iff (atom (rel P)) (atom (rel F (var x)))))))) ; P21

;; ===== exercise the tableau prover on a few of the same =====
(check-true (tab-proves?
             '(exists y (forall x (imp (atom (rel F (var y))) (atom (rel F (var x)))))))) ; P18
(check-true (tab-proves? '(not (exists x
                                       (forall y
                                               (iff (atom (rel F (var y) (var x)))
                                                    (not (atom (rel F (var y) (var y)))))))))) ; P39
(check-pred
 (λ (l) (andmap exact-nonnegative-integer? l))
 (splittab '(exists x
                    (forall y
                            (forall z
                                    (imp (imp (atom (rel P (var y))) (atom (rel Q (var z))))
                                         (imp (atom (rel P (var x)))
                                              (atom (rel Q (var x)))))))))) ; P19 via splittab
