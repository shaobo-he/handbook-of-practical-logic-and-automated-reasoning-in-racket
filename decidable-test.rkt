#lang racket/base

(require rackunit)
(require "decidable.rkt" "qelim.rkt" "cooper.rkt" "complex.rkt" "real.rkt" "grobner.rkt")

;; ===== decidable: AE fragment, Wang, finite models, monadic =====
(check-true (aedecide '(imp (forall x (atom (rel P (var x)))) (forall y (atom (rel P (var y)))))))
(check-true (wang '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y))))))))
(check-true (decide-finite 2 '(imp (atom (rel P (var x))) (atom (rel P (var x))))))
;; monadic: drinker is in the monadic fragment and valid
(check-true (decide-monadic
             '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y))))))))

;; ===== qelim: dense linear orders without endpoints =====
(check-equal? (quelim-dlo '(forall x (exists y (atom (rel < (var x) (var y)))))) #t)
(check-equal? (quelim-dlo '(exists x (and (atom (rel < (var a) (var x)))
                                          (atom (rel < (var x) (var b))))))
              '(atom (rel < (var a) (var b))))
;; not valid: there isn't always something between two points unless a<b
(check-equal? (quelim-dlo '(forall a (forall b (exists x (and (atom (rel < (var a) (var x)))
                                                              (atom (rel < (var x) (var b))))))))
              #f)

;; ===== cooper: Presburger arithmetic =====
;; every integer is even or odd
(check-equal? (integer-qelim
               '(forall x (exists y (or (atom (rel = (var x) (fn * (fn |2|) (var y))))
                                        (atom (rel = (var x) (fn + (fn * (fn |2|) (var y)) (fn |1|))))))))
              #t)
;; nothing strictly between 0 and 1
(check-equal? (integer-qelim '(exists x (and (atom (rel < (fn |0|) (var x)))
                                             (atom (rel < (var x) (fn |1|))))))
              #f)
;; x < x + 1 for all x
(check-equal? (integer-qelim '(forall x (atom (rel < (var x) (fn + (var x) (fn |1|)))))) #t)
;; natural-number version: forall x. exists y. x = y (trivially true over naturals)
(check-equal? (natural-qelim '(forall x (exists y (atom (rel = (var x) (var y)))))) #t)

;; ===== complex: algebraically closed fields =====
(check-equal? (complex-qelim '(exists x (atom (rel = (fn + (fn ^ (var x) (fn |2|)) (fn |1|)) (fn |0|))))) #t)
(check-equal? (complex-qelim '(forall x (imp (atom (rel = (fn ^ (var x) (fn |2|)) (fn |0|)))
                                             (atom (rel = (var x) (fn |0|)))))) #t)

;; ===== real: real closed fields =====
(check-equal? (real-qelim '(forall x (atom (rel >= (fn ^ (var x) (fn |2|)) (fn |0|))))) #t)
(check-equal? (real-qelim '(exists x (atom (rel = (fn + (fn ^ (var x) (fn |2|)) (fn |1|)) (fn |0|))))) #f)
(check-equal? (real-qelim '(exists x (atom (rel = (fn ^ (var x) (fn |2|)) (fn |2|))))) #t)
;; (x-1)^2 >= 0 for all x
(check-equal? (real-qelim '(forall x (atom (rel >= (fn + (fn - (fn ^ (var x) (fn |2|)) (fn * (fn |2|) (var x))) (fn |1|)) (fn |0|))))) #t)

;; ===== grobner: universal theory of algebraically closed fields =====
(check-equal? (grobner-decide '(imp (atom (rel = (var x) (var y)))
                                    (atom (rel = (fn ^ (var x) (fn |2|)) (fn ^ (var y) (fn |2|)))))) #t)
(check-equal? (grobner-decide '(imp (atom (rel = (fn ^ (var x) (fn |2|)) (fn ^ (var y) (fn |2|))))
                                    (atom (rel = (var x) (var y))))) #f)
(check-equal? (grobner-decide '(imp (and (atom (rel = (fn ^ (var a) (fn |2|)) (fn |2|)))
                                         (atom (rel = (fn ^ (var b) (fn |2|)) (fn |2|))))
                                    (atom (rel = (fn * (fn - (var a) (var b)) (fn + (var a) (var b))) (fn |0|))))) #t)
