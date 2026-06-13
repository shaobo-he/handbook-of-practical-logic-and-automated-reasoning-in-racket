#lang racket/base

(require rackunit)
(require "../core/intro.rkt" "../prop/propexamples.rkt" "../prop/bdd.rkt" "../prop/stal.rkt")
(require (only-in "../prop/prop.rkt" tautology))
(require (only-in "../prop/dp.rkt" dplltaut))

;; ===== intro: parse / simplify / print =====
(check-equal? (parse-exp "2 * 3") '(mul (const 2) (const 3)))
(check-equal? (simplify (parse-exp "(0 * x + 1) * 3")) '(const 3))
(check-equal? (simplify (parse-exp "(0 + x) + (y + 0)")) '(add (var "x") (var "y")))
(check-equal? (sprint-exp (parse-exp "x + 3 * y")) "<<x + 3 * y>>")

;; ===== propexamples: Ramsey =====
(check-false (tautology (ramsey 3 3 5)))   ; R(3,3) > 5
(check-true (dplltaut (ramsey 3 3 6)))     ; R(3,3) = 6

;; ===== propexamples: adders and primality (checked with BDDs) =====
(check-true (bddtaut (mk-adder-test 2 1)))
(check-true (bddtaut (prime 7)))
(check-false (bddtaut (prime 9)))

;; ===== BDD tautology agrees with the reference on small formulas =====
(define peirce
  '(imp (imp (imp (atom p) (atom q)) (atom p)) (atom p)))
(check-true (bddtaut peirce))
(check-false (bddtaut '(or (atom p) (atom q))))
;; ebddtaut exploits p <=> (q /\ r) as a shared definition
(check-true (ebddtaut '(imp (iff (atom p) (and (atom q) (atom r))) (imp (atom p) (atom q)))))

;; ===== Stalmarck agrees too =====
(check-true (stalmarck '(or (atom p) (not (atom p)))))
(check-true (stalmarck peirce))
;; stalmarck proves tautologies (returns #t) but raises on a formula it can't
;; refute within the easiness limit, rather than returning #f
(check-exn exn:fail? (λ () (stalmarck '(or (atom p) (atom q)))))
(check-true (stalmarck (mk-adder-test 2 1)))
