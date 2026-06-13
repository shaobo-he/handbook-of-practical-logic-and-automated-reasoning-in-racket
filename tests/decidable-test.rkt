#lang racket/base

(require rackunit)
(require "../decidable/decidable.rkt"
         "../decidable/qelim.rkt"
         "../decidable/cooper.rkt"
         "../decidable/complex.rkt"
         "../decidable/real.rkt"
         "../decidable/grobner.rkt")

;; ===== decidable: AE fragment, Wang, finite models, monadic =====
(check-true (aedecide '(imp (forall x (atom (rel P (var x)))) (forall y (atom (rel P (var y)))))))
(check-true (wang '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y))))))))
(check-true (decide-finite 2 '(imp (atom (rel P (var x))) (atom (rel P (var x))))))
;; monadic: drinker is in the monadic fragment and valid
(check-true (decide-monadic '(exists x
                                     (forall y (imp (atom (rel P (var x))) (atom (rel P (var y))))))))

;; ===== qelim: dense linear orders without endpoints =====
(check-equal? (quelim-dlo '(forall x (exists y (atom (rel < (var x) (var y)))))) #t)
(check-equal?
 (quelim-dlo '(exists x (and (atom (rel < (var a) (var x))) (atom (rel < (var x) (var b))))))
 '(atom (rel < (var a) (var b))))
;; not valid: there isn't always something between two points unless a<b
(check-equal?
 (quelim-dlo
  '(forall a
           (forall b (exists x (and (atom (rel < (var a) (var x))) (atom (rel < (var x) (var b))))))))
 #f)

;; ===== cooper: Presburger arithmetic =====
;; every integer is even or odd
(check-equal? (integer-qelim
               '(forall x
                        (exists y
                                (or (atom (rel = (var x) (fn * (fn |2|) (var y))))
                                    (atom (rel = (var x) (fn + (fn * (fn |2|) (var y)) (fn |1|))))))))
              #t)
;; nothing strictly between 0 and 1
(check-equal?
 (integer-qelim '(exists x (and (atom (rel < (fn |0|) (var x))) (atom (rel < (var x) (fn |1|))))))
 #f)
;; x < x + 1 for all x
(check-equal? (integer-qelim '(forall x (atom (rel < (var x) (fn + (var x) (fn |1|)))))) #t)
;; natural-number version: forall x. exists y. x = y (trivially true over naturals)
(check-equal? (natural-qelim '(forall x (exists y (atom (rel = (var x) (var y)))))) #t)

;; ===== complex: algebraically closed fields =====
(check-equal?
 (complex-qelim '(exists x (atom (rel = (fn + (fn ^ (var x) (fn |2|)) (fn |1|)) (fn |0|)))))
 #t)
(check-equal? (complex-qelim '(forall x
                                      (imp (atom (rel = (fn ^ (var x) (fn |2|)) (fn |0|)))
                                           (atom (rel = (var x) (fn |0|))))))
              #t)

;; ===== real: real closed fields =====
(check-equal? (real-qelim '(forall x (atom (rel >= (fn ^ (var x) (fn |2|)) (fn |0|))))) #t)
(check-equal? (real-qelim '(exists x (atom (rel = (fn + (fn ^ (var x) (fn |2|)) (fn |1|)) (fn |0|)))))
              #f)
(check-equal? (real-qelim '(exists x (atom (rel = (fn ^ (var x) (fn |2|)) (fn |2|))))) #t)
;; (x-1)^2 >= 0 for all x
(check-equal?
 (real-qelim
  '(forall
    x
    (atom (rel >= (fn + (fn - (fn ^ (var x) (fn |2|)) (fn * (fn |2|) (var x))) (fn |1|)) (fn |0|)))))
 #t)

;; ===== grobner: universal theory of algebraically closed fields =====
(check-equal? (grobner-decide '(imp (atom (rel = (var x) (var y)))
                                    (atom (rel = (fn ^ (var x) (fn |2|)) (fn ^ (var y) (fn |2|))))))
              #t)
(check-equal? (grobner-decide '(imp (atom (rel = (fn ^ (var x) (fn |2|)) (fn ^ (var y) (fn |2|))))
                                    (atom (rel = (var x) (var y)))))
              #f)
(check-equal?
 (grobner-decide '(imp (and (atom (rel = (fn ^ (var a) (fn |2|)) (fn |2|)))
                            (atom (rel = (fn ^ (var b) (fn |2|)) (fn |2|))))
                       (atom (rel = (fn * (fn - (var a) (var b)) (fn + (var a) (var b))) (fn |0|)))))
 #t)

;; ===== more decision-procedure coverage (incl. negative cases) =====
;; aedecide refutes a non-valid AE formula
(check-false (aedecide '(forall x (atom (rel P (var x))))))
;; decide-finite: P(x) is not valid; excluded middle is
(check-false (decide-finite 1 '(atom (rel P (var x)))))
(check-true (decide-finite 2 '(or (atom (rel P (var x))) (not (atom (rel P (var x)))))))
;; DLO trichotomy is valid
(check-equal? (quelim-dlo '(forall x
                                   (forall y
                                           (or (atom (rel < (var x) (var y)))
                                               (or (atom (rel = (var x) (var y)))
                                                   (atom (rel < (var y) (var x))))))))
              #t)
;; Presburger: no integer x with 2x = 1
(check-equal? (integer-qelim '(exists x (atom (rel = (fn * (fn |2|) (var x)) (fn |1|))))) #f)
;; complex: x^3 = 1 is solvable over C
(check-equal? (complex-qelim '(exists x (atom (rel = (fn ^ (var x) (fn |3|)) (fn |1|))))) #t)
;; real: x^2 > 0 does NOT hold for all x (x = 0 is a counterexample)
(check-equal? (real-qelim '(forall x (atom (rel > (fn ^ (var x) (fn |2|)) (fn |0|))))) #f)
;; grobner: x = y ==> x*z = y*z
(check-equal? (grobner-decide '(imp (atom (rel = (var x) (var y)))
                                    (atom (rel = (fn * (var x) (var z)) (fn * (var y) (var z))))))
              #t)
