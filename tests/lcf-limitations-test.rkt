#lang racket/base

;; Unit tests for the limitative-results chapter (limitations.rkt): the
;; injective pairing and Goedel numbering, diagonalization, the Delta-decider
;; and Sigma/Pi/Delta classifier, the Sigma_1 verifier and bound search, the
;; Turing-machine simulator, and the Robinson ground-term evaluator.

(require rackunit)
(require "../lcf/lcf.rkt"
         "../lcf/lcfprop.rkt"
         "../lcf/folderived.rkt"
         "../lcf/limitations.rkt")
(require (only-in racket/list remove-duplicates))
(require (only-in "../core/formulas.rkt" consequent antecedent))
(require (only-in "../equality/equal.rkt" rhs))

;; ===== numerals =====
(check-equal? (numeral 0) '(fn |0|))
(check-equal? (numeral 3) '(fn S (fn S (fn S (fn |0|)))))

;; ===== pair: injective via the (x+y)^2 + x + 1 encoding =====
(check-equal? (pair 0 0) 1)
(check-equal? (pair 1 2) 11)
(check-equal? (pair 2 1) 12)
;; nearby coordinates yield distinct codes (injectivity sanity check)
(check-equal?
 (length (remove-duplicates (list (pair 0 0) (pair 1 0) (pair 0 1) (pair 1 1) (pair 2 0) (pair 0 2))))
 6)

;; ===== number: bijective base-256 string encoding (first char least significant) =====
(check-equal? (number "") 0)
(check-equal? (number "a") 98) ; 1 + 97
(check-equal? (number "ab") 25442) ; (1+97) + 256*(1+98)

;; ===== gterm / gform / gnumeral =====
(check-equal? (gterm '(fn |0|)) 3) ; pair 1 0
(check-equal? (gterm '(var x)) (pair 0 (number "x")))
(check-equal? (gnumeral 0) (gterm '(fn |0|)))
(check-equal? (gnumeral 2) (gterm (numeral 2)))
(check-equal? (gform #f) 1) ; pair 0 0
(check-equal? (gform #t) 2) ; pair 0 1
;; terms / formulas outside the arithmetic language are rejected
(check-exn exn:fail? (λ () (gterm '(fn h (var x)))))
(check-exn exn:fail? (λ () (gform '(atom (rel P (var x))))))
;; distinct structures get distinct Goedel numbers
(check-false (= (gform '(atom (rel = (var x) (fn |0|)))) (gform '(atom (rel < (var x) (fn |0|))))))

;; ===== diag / qdiag =====
;; NOTE: numeral (gform p) is astronomically large for any p mentioning a
;; variable (gterm of a variable alone is ~14642, so gform is ~10^16), and
;; materialising that many nested S's exhausts memory. So we use a closed p whose
;; Goedel number is small, and otherwise test diag's identity behaviour.
;;
;; qdiag builds (exists x (= x [code p]) /\ p)
(let ([p '(atom (rel = (fn |0|) (fn |0|)))]) ; gform p is small (1683)
  (check-equal? (qdiag 'x p) `(exists x (and (atom (rel = (var x) ,(numeral (gform p)))) ,p))))
;; when x does not occur in p, diag is the identity
(check-equal? (diag 'x '(atom (rel = (fn |0|) (fn |0|)))) '(atom (rel = (fn |0|) (fn |0|))))

;; ===== dtermval: matches native arithmetic =====
(check-equal? (dtermval (hash) (numeral 5)) 5)
(check-equal? (dtermval (hash) '(fn + (fn S (fn |0|)) (fn S (fn S (fn |0|))))) 3)
(check-equal? (dtermval (hash) '(fn * (fn S (fn S (fn |0|))) (fn S (fn S (fn |0|))))) 4)
;; variables are looked up in the valuation
(check-equal? (dtermval (hash 'x 5) '(var x)) 5)
(check-equal? (dtermval (hash 'x 3) '(fn + (var x) (fn S (fn |0|)))) 4)

;; ===== dholds: complex / nested delta formulas =====
;; forall x < 2. exists y <= x. y = y   (vacuously / trivially true)
(check-true (dholds (hash)
                    '(forall x
                             (imp (atom (rel < (var x) (fn S (fn S (fn |0|)))))
                                  (exists y
                                          (and (atom (rel <= (var y) (var x)))
                                               (atom (rel = (var y) (var y)))))))))
;; mixed connectives over bounded quantifiers
(check-true
 (dholds (hash) '(and (atom (rel = (fn |0|) (fn |0|))) (imp (atom (rel < (fn |0|) (fn |0|))) #f))))
;; false: exists x <= 1. x = 2
(check-false (dholds (hash)
                     '(exists x
                              (and (atom (rel <= (var x) (fn S (fn |0|))))
                                   (atom (rel = (var x) (fn S (fn S (fn |0|)))))))))

;; ===== opp / classify =====
(check-equal? (opp 'sigma) 'pi)
(check-equal? (opp 'pi) 'sigma)
(check-equal? (opp 'delta) 'delta)
(check-true (classify 'sigma 2 '(exists x (exists y (atom (rel = (var x) (var y)))))))
(check-true (classify 'pi 1 '(forall x (atom (rel = (var x) (var x))))))
;; a bounded universal quantifier stays Delta_0
(check-true
 (classify 'delta 0 '(forall x (imp (atom (rel < (var x) (fn |0|))) (atom (rel = (var x) (var x)))))))
;; an unbounded existential is not Delta_0
(check-false (classify 'delta 0 '(exists x (atom (rel = (var x) (fn |0|))))))

;; ===== veref / sholds / sigma-bound =====
;; true Sigma_1 with a small enough search bound
(check-true (sholds 5 (hash) `(exists x (atom (rel = (var x) ,(numeral 3))))))
;; bound too small -> not (yet) verified
(check-false (sholds 2 (hash) `(exists x (atom (rel = (var x) ,(numeral 3))))))
(check-true (sholds 0 (hash) '(exists x (atom (rel = (var x) (fn |0|))))))
;; sigma-bound finds the minimal witness
(check-equal? (sigma-bound `(exists x (atom (rel = (var x) ,(numeral 3))))) 3)
(check-equal? (sigma-bound '(exists x (atom (rel = (var x) (fn |0|))))) 0)

;; ===== Turing-machine tape primitives =====
(check-equal? (look (twrite 'one (list 'tape 0 (hash)))) 'one)
(check-equal? (look (move 'stay (twrite 'one (list 'tape 0 (hash))))) 'one)
;; a later write overwrites an earlier one at the same cell
(check-equal? (look (twrite 'blank (twrite 'one (list 'tape 0 (hash))))) 'blank)
;; moving off the written cell sees the default blank
(check-equal? (look (move 'right (twrite 'one (list 'tape 0 (hash))))) 'blank)
;; input/output tape encoding round-trips a single number
(check-equal? (output-tape (input-tape '(4))) 4)
;; empty program halts immediately, copying the input through
(check-equal? (exec (hash) '(0)) 0)
(check-equal? (exec (hash) '(7)) 7)

;; ===== Robinson axioms =====
(check-equal? (length robinson-axioms) 8)
;; every axiom is a theorem  |- robinson -> <conjunct>
(check-true (andmap (λ (ax) (equal? (antecedent (concl ax)) robinson)) robinson-axioms))
;; the add-0 axiom's consequent is the expected universal equation
(check-equal? (consequent (concl add-0)) '(forall n (atom (rel = (fn + (fn |0|) (var n)) (var n)))))

;; ===== right-handed derived rules =====
(check-equal? (concl (right-spec '(var a) (imp-refl '(forall x (atom (rel P (var x)))))))
              '(imp (forall x (atom (rel P (var x)))) (atom (rel P (var a)))))
(check-equal? (concl (right-sym (imp-refl '(atom (rel = (fn a) (fn b))))))
              '(imp (atom (rel = (fn a) (fn b))) (atom (rel = (fn b) (fn a)))))
(check-equal? (concl (right-trans (imp-refl '(atom (rel = (fn a) (fn a))))
                                  (imp-refl '(atom (rel = (fn a) (fn a))))))
              '(imp (atom (rel = (fn a) (fn a))) (atom (rel = (fn a) (fn a)))))

;; ===== robop / robeval ground-term evaluation =====
;; 0 + 1 evaluates to 1
(check-equal? (rhs (consequent (concl (robop '(fn + (fn |0|) (fn S (fn |0|))))))) (numeral 1))
;; robeval normalises 3 * 2 = 6, antecedent threads the Robinson axioms
(let ([th (robeval `(fn * ,(numeral 3) ,(numeral 2)))])
  (check-equal? (rhs (consequent (concl th))) (numeral 6))
  (check-equal? (antecedent (concl th)) robinson))
