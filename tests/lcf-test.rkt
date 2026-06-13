#lang racket/base

(require rackunit)
(require "../lcf/lcf.rkt"
         "../lcf/lcfprop.rkt"
         "../lcf/folderived.rkt"
         "../lcf/lcffol.rkt"
         "../lcf/tactics.rkt"
         "../lcf/limitations.rkt")
(require (only-in "../core/formulas.rkt" consequent))
(require (only-in "../equality/equal.rkt" rhs))

;; ===== LCF kernel tautology prover =====
(define peirce '(imp (imp (imp (atom (rel p)) (atom (rel q))) (atom (rel p))) (atom (rel p))))
(check-equal? (concl (lcftaut peirce)) peirce)
(check-equal? (concl (lcftaut '(imp (atom (rel p)) (atom (rel p)))))
              '(imp (atom (rel p)) (atom (rel p))))
(check-exn exn:fail? (λ () (lcftaut '(atom (rel p))))) ; not a tautology

;; ===== LCF first-order prover =====
(define drinker '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y)))))))
(check-equal? (concl (lcffol drinker)) drinker)

;; ===== tactic proof =====
(define goal '(imp (and (atom (rel p)) (atom (rel q))) (and (atom (rel q)) (atom (rel p)))))
(define th
  (prove goal
         (list (λ (g) (imp-intro-tac "h" g))
               (λ (g) (conj-intro-tac g))
               (λ (g) (auto-tac by (list "h") g))
               (λ (g) (auto-tac by (list "h") g)))))
(check-equal? (concl th) goal)

;; ===== limitations: numerals, Goedel numbering, diagonalization =====
(check-equal? (numeral 3) '(fn S (fn S (fn S (fn |0|)))))
(check-pred exact-positive-integer? (gnumeral 2))
(check-pred exact-positive-integer? (gform '(atom (rel = (var x) (fn |0|)))))

;; ===== delta-decider =====
;; forall x < 2. x * 0 = 0
(check-true (dholds (hash)
                    '(forall x
                             (imp (atom (rel < (var x) (fn S (fn S (fn |0|)))))
                                  (atom (rel = (fn * (var x) (fn |0|)) (fn |0|)))))))
;; exists x <= 2. x = 2
(check-true (dholds (hash)
                    '(exists x
                             (and (atom (rel <= (var x) (fn S (fn S (fn |0|)))))
                                  (atom (rel = (var x) (fn S (fn S (fn |0|)))))))))
;; false: forall x < 2. x = 0
(check-false (dholds (hash)
                     '(forall x
                              (imp (atom (rel < (var x) (fn S (fn S (fn |0|)))))
                                   (atom (rel = (var x) (fn |0|)))))))

;; ===== Sigma/Pi/Delta classification =====
(check-true (classify 'sigma 1 '(exists x (atom (rel = (var x) (fn |0|))))))
(check-false (classify 'delta 0 '(exists x (atom (rel = (var x) (fn |0|))))))

;; ===== Sigma_1 verification / bound search =====
(check-pred exact-nonnegative-integer?
            (sigma-bound '(exists x (atom (rel = (var x) (fn S (fn |0|)))))))

;; ===== Turing machine tape round-trip (empty program halts immediately) =====
(check-equal? (exec (hash) '(2)) 2)
(check-equal? (exec (hash) '(5)) 5)

;; ===== Robinson ground-term evaluation produces a kernel proof of 2+2=4 =====
(define ev (robeval '(fn + (fn S (fn S (fn |0|))) (fn S (fn S (fn |0|))))))
(check-equal? (rhs (consequent (concl ev))) (numeral 4))

;; ===== more LCF / derived-rule / limitations coverage =====
;; another tautology, and kernel-derived equality theorems
(check-equal? (concl (lcftaut '(or (atom (rel p)) (not (atom (rel p))))))
              '(or (atom (rel p)) (not (atom (rel p)))))
(check-equal? (concl (eq-sym '(fn a) '(fn b)))
              '(imp (atom (rel = (fn a) (fn b))) (atom (rel = (fn b) (fn a)))))
(check-equal? (concl (ispec '(fn c) '(forall x (atom (rel P (var x))))))
              '(imp (forall x (atom (rel P (var x)))) (atom (rel P (fn c)))))
;; a tactic proof using universal introduction
(check-equal? (concl (prove '(forall x (imp (atom (rel P (var x))) (atom (rel P (var x)))))
                            (list (λ (g) (forall-intro-tac "y" g))
                                  (λ (g) (imp-intro-tac "h" g))
                                  (λ (g) (auto-tac by (list "h") g)))))
              '(forall x (imp (atom (rel P (var x))) (atom (rel P (var x))))))
;; lcffol on another valid formula (nonempty-domain instantiation)
(check-equal? (concl (lcffol '(imp (forall x (atom (rel P (var x))))
                                   (exists y (atom (rel P (var y)))))))
              '(imp (forall x (atom (rel P (var x)))) (exists y (atom (rel P (var y))))))
;; Pi classification, Goedel-number distinctness, tape primitives, multiplication
(check-true (classify 'pi 1 '(forall x (atom (rel = (var x) (var x))))))
(check-false (= (gnumeral 1) (gnumeral 2)))
(check-equal? (look (twrite 'one (list 'tape 0 (hash)))) 'one)
(check-equal? (look (move 'right (twrite 'one (list 'tape 0 (hash))))) 'blank)
(check-equal?
 (rhs (consequent (concl (robeval '(fn * (fn S (fn S (fn S (fn |0|)))) (fn S (fn |0|)))))))
 (numeral 3))
