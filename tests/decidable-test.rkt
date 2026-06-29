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

;; ===== decidable.rkt: finite-model enumeration cardinalities =====
;; |alltuples n L| = |L|^n; alltuples 0 is the single empty tuple.
(check-equal? (length (alltuples 2 '(a b c))) 9)
(check-equal? (length (alltuples 3 '(x y))) 8)
(check-equal? (alltuples 0 '(a b)) '(()))
(check-equal? (alltuples 2 '(a b)) '((a a) (a b) (b a) (b b)))
;; |allmappings Dom Ran| = |Ran|^|Dom|; functions/predicates of arity k over an
;; n-element domain are mappings out of the n^k tuples.
(check-equal? (length (allmappings '(1 2) '(a b c))) 9)
(check-equal? (length (allfunctions '(1 2) 1)) 4)
(check-equal? (length (allpredicates '(1 2) 1)) 4)

;; ===== decidable.rkt: Aristotelean syllogisms =====
;; 4^4 = 256 forms; 15 are unconditionally valid (Wang), and 24 once non-emptiness
;; of subject/middle/predicate is assumed (the classical count with existential import).
(check-equal? (length all-possible-syllogisms) 256)
(check-equal? (length all-possible-syllogisms-nonempty) 256)
(check-equal? (length (filter wang all-possible-syllogisms)) 15)
(check-equal? (length (filter aedecide all-possible-syllogisms-nonempty)) 24)

;; ===== decidable.rkt: miniscope pushes quantifiers to the leaves =====
(check-equal? (miniscope '(exists x (forall y (and (atom (rel P (var x))) (atom (rel Q (var y)))))))
              '(and (exists x (atom (rel P (var x)))) (forall y (atom (rel Q (var y))))))

;; ===== decidable.rkt: AE decision and its error case =====
;; "all P implies some P" is AE-valid; "all P implies some Q" is not.
(check-true (aedecide '(imp (forall x (atom (rel P (var x)))) (exists y (atom (rel P (var y)))))))
(check-false (aedecide '(imp (forall x (atom (rel P (var x)))) (exists y (atom (rel Q (var y)))))))
;; function symbols escape the AE fragment, so aedecide rejects them.
(check-exn exn:fail? (λ () (aedecide '(forall x (atom (rel P (fn f (var x))))))))
(check-true (wang '(imp (forall x (atom (rel P (var x)))) (forall x (atom (rel P (var x)))))))

;; ===== decidable.rkt: finite-model decision =====
(check-true (decide-finite 1 '(or (atom (rel P (var x))) (not (atom (rel P (var x)))))))
(check-false (decide-finite 2 '(and (atom (rel P (var x))) (not (atom (rel P (var x)))))))
(check-false (decide-finite 2 '(forall x (or (atom (rel P (var x))) (atom (rel Q (var x)))))))

;; ===== decidable.rkt: monadic fragment and its error cases =====
(check-true (decide-monadic '(forall x (imp (atom (rel P (var x))) (atom (rel P (var x)))))))
(check-exn exn:fail? (λ () (decide-monadic '(forall x (atom (rel P (fn f (var x))))))))
(check-exn exn:fail? (λ () (decide-monadic '(forall x (atom (rel P (var x) (var x)))))))

;; ===== decidable.rkt: finite-model property =====
;; decide-fmp accepts valid formulas and rejects ones with a finite countermodel.
(check-true (decide-fmp '(imp (forall x (atom (rel P (var x)))) (exists y (atom (rel P (var y)))))))
(check-true (decide-fmp '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y))))))))
(check-false (decide-fmp '(forall x (atom (rel P (var x))))))

;; ===== qelim.rkt: conjunct partition =====
;; conjuncts not mentioning x pass through untouched; bfn is applied only to the
;; x-mentioning part, then re-conjoined with the rest.
(check-equal? (qelim (λ (f) f) 'x '(atom (rel Q (var y)))) '(atom (rel Q (var y))))
(check-equal? (qelim (λ (f) #t) 'x '(and (atom (rel P (var x))) (atom (rel Q (var y)))))
              '(and (atom (rel Q (var y))) #t))

;; ===== qelim.rkt: afn-dlo normalises non-strict / reversed inequalities =====
(check-equal? (afn-dlo '(x y) '(atom (rel <= (var x) (var y)))) '(not (atom (rel < (var y) (var x)))))
(check-equal? (afn-dlo '(x y) '(atom (rel >= (var x) (var y)))) '(not (atom (rel < (var x) (var y)))))
(check-equal? (afn-dlo '(x y) '(atom (rel > (var x) (var y)))) '(atom (rel < (var y) (var x))))

;; ===== qelim.rkt: cnnf core NNF rewrites =====
(check-equal? ((cnnf (λ (x) x)) '(not (not (atom p)))) '(atom p))
(check-equal? ((cnnf (λ (x) x)) '(not (and (atom p) (atom q)))) '(or (not (atom p)) (not (atom q))))
(check-equal? ((cnnf (λ (x) x)) '(not (or (atom p) (atom q)))) '(and (not (atom p)) (not (atom q))))

;; ===== qelim.rkt: dlobasic existential elimination over a DLO =====
;; (1) an equality x=y lets us substitute y for x;
(check-equal? (dlobasic '(exists x
                                 (and (atom (rel = (var x) (var y))) (atom (rel < (var x) (var z))))))
              '(atom (rel < (var y) (var z))))
;; (2) x<x is contradictory;
(check-equal? (dlobasic '(exists x (atom (rel < (var x) (var x))))) #f)
;; (3) otherwise pair every lower bound with every upper bound.
(check-equal? (dlobasic '(exists x
                                 (and (atom (rel < (var a) (var x))) (atom (rel < (var x) (var b))))))
              '(atom (rel < (var a) (var b))))

;; ===== cooper.rkt: numerals are an integer isomorphism =====
(check-equal? (dest-numeral (mk-numeral 42)) 42)
(check-equal? (dest-numeral (mk-numeral -17)) -17)
(check-true (is-numeral (mk-numeral 0)))
(check-false (is-numeral '(var x)))
(check-false (is-numeral '(fn f (var x))))
(check-equal? (dest-numeral zero) 0)
(check-equal? (dest-numeral one) 1)
(check-equal? (numeral1 abs (mk-numeral -5)) (mk-numeral 5))
(check-equal? (numeral2 + (mk-numeral 3) (mk-numeral 4)) (mk-numeral 7))

;; ===== cooper.rkt: canonical linear-term arithmetic =====
(check-equal? (linear-neg (linear-neg (mk-numeral 5))) (mk-numeral 5))
(check-equal? (linear-cmul 0 (mk-numeral 5)) zero)
;; multiplying two genuine linear terms is non-linear and is rejected.
(check-exn exn:fail? (λ () (linear-mul (lint '(x y) '(var x)) (lint '(x y) '(var y)))))

;; ===== cooper.rkt: evalc on ground atoms =====
(check-eq? (evalc '(atom (rel = (fn |3|) (fn |3|)))) #t)
(check-eq? (evalc '(atom (rel < (fn |5|) (fn |3|)))) #f)
(check-eq? (evalc '(atom (rel divides (fn |2|) (fn |4|)))) #t)
(check-eq? (evalc '(atom (rel divides (fn |3|) (fn |4|)))) #f)

;; ===== cooper.rkt: relativize installs per-quantifier domain guards =====
(check-equal? (relativize (λ (x) `(atom (rel < (fn |0|) (var ,x))))
                          '(exists x (atom (rel = (var x) (fn |5|)))))
              '(exists x (and (atom (rel < (fn |0|) (var x))) (atom (rel = (var x) (fn |5|))))))
(check-equal? (relativize (λ (x) `(atom (rel < (fn |0|) (var ,x))))
                          '(forall x (atom (rel P (var x)))))
              '(forall x (imp (atom (rel < (fn |0|) (var x))) (atom (rel P (var x))))))

;; ===== cooper.rkt: more curated Presburger sentences =====
(check-equal? (integer-qelim '(exists x (atom (rel < (fn |5|) (var x))))) #t)
(check-equal? (integer-qelim '(forall x (exists y (atom (rel = (var x) (fn * (fn |2|) (var y)))))))
              #f)
(check-equal?
 (integer-qelim '(exists x (and (atom (rel < (fn |3|) (var x))) (atom (rel < (var x) (fn |4|))))))
 #f)

;; ===== complex.rkt: canonical polynomials and utilities =====
(check-equal? (poly-var 'x) '(fn + (fn |0|) (fn * (var x) (fn |1|))))
(check-equal? (poly-sub '(x)
                        (polynate '(x) '(fn + (fn |1|) (fn * (var x) (fn |2|))))
                        (polynate '(x) '(fn + (fn |1|) (fn * (var x) (fn |2|)))))
              zero)
(check-equal? (poly-pow '(x) (poly-var 'x) 0) one)
(check-equal? (poly-pow '(x) (poly-var 'x) 1) (poly-var 'x))
(check-equal? (coefficients '(x) (polynate '(x) '(fn + (fn ^ (var x) (fn |2|)) (fn |1|))))
              (list one zero one))
(check-equal? (degree '(x) (polynate '(x) '(fn + (fn ^ (var x) (fn |2|)) (fn |1|)))) 2)
(check-equal? (head '(x) (polynate '(x) '(fn + (fn * (fn |2|) (var x)) (fn |3|)))) (mk-numeral 2))
(check-equal? (behead '(x) (polynate '(x) '(fn + (fn ^ (var x) (fn |2|)) (fn |1|)))) one)
(check-true (is-constant '(x) '(fn |5|)))
(check-false (is-constant '(x) (poly-var 'x)))
(check-equal? (poly-cmul 2 (polynate '(x) '(fn + (var x) (fn |1|))))
              '(fn + (fn |2|) (fn * (var x) (fn |2|))))
(check-equal? (headconst '(fn |5|)) 5)
(check-equal? (headconst (polynate '(x) '(fn + (fn + (fn ^ (var x) (fn |2|)) (var x)) (fn |1|)))) 1)
(check-equal? (swap #t 'positive) 'negative)
(check-equal? (swap #f 'zero) 'zero)
(check-equal? (swap #t 'nonzero) 'nonzero)
;; monic normalises the leading coefficient to 1, recording whether the sign flipped.
(let-values ([(p* neg?) (monic (polynate '(x) '(fn * (fn |2|) (fn ^ (var x) (fn |2|)))))])
  (check-equal? (headconst p*) 1)
  (check-false neg?))
(let-values ([(p* neg?) (monic (polynate '(x) '(fn - (fn ^ (var x) (fn |2|)))))])
  (check-equal? (headconst p*) 1)
  (check-true neg?))
;; findsign retrieves a sign installed by assertsign (after monic canonicalisation).
(check-eq? (findsign (assertsign init-sgns (cons (poly-var 'x) 'positive)) (poly-var 'x)) 'positive)
;; complex QE with two existentials: the unit circle is nonempty over C.
(check-true
 (complex-qelim
  '(exists x
           (exists y
                   (atom (rel = (fn + (fn ^ (var x) (fn |2|)) (fn ^ (var y) (fn |2|))) (fn |1|)))))))

;; ===== real.rkt: formal derivative and QE entry points =====
(check-equal? (poly-diff '(x) '(fn |0|)) zero)
(check-equal? (poly-diff '(x y) '(fn |5|)) zero)
(check-equal? (poly-diff '(x) (poly-var 'x)) one) ; d/dx x = 1
(check-true (real-qelim* '(exists x (atom (rel = (fn ^ (var x) (fn |2|)) (fn |2|))))))
(check-true (real-qelim '(exists x (exists y (atom (rel < (var x) (var y)))))))

;; ===== grobner.rkt: monomial arithmetic =====
(check-equal? (mmul '(2 . (1 2)) '(3 . (0 1))) '(6 . (1 3)))
(check-equal? (mdiv (mmul '(2 . (1 1)) '(3 . (2 3))) '(3 . (2 3))) '(2 . (1 1)))
(check-exn exn:fail? (λ () (mdiv '(2 . (1 1)) '(3 . (2 3)))))
(check-equal? (mlcm '(5 . (1 2 3)) '(7 . (2 1 0))) '(1 . (2 2 3)))
;; graded order: equal total degree => the larger leading exponent ranks first;
;; otherwise the smaller total degree is "less".
(check-true (morder-lt '(1 0) '(0 1)))
(check-false (morder-lt '(0 1) '(1 0)))
(check-true (morder-lt '(0 0) '(1 0)))

;; ===== grobner.rkt: constructors, conversion, reduction =====
(check-equal? (mpoly-const '(x) 0) '())
(check-equal? (mpoly-const '(x) 5) '((5 . (0))))
(check-equal? (mpoly-var '(x y) 'x) '((1 . (1 0))))
(check-equal? (mpoly-var '(x y) 'y) '((1 . (0 1))))
(check-equal? (mpolynate '(x) '(fn |3|)) '((3 . (0))))
(check-equal? (mpolynate '(x) '(var x)) '((1 . (1))))
(check-equal? (mpolynate '(x) '(fn * (var x) (var x))) '((1 . (2))))
(check-equal? (mpolyatom '(x) '(atom (rel = (var x) (fn |0|)))) '((1 . (1))))
;; reduction by the empty basis is the identity.
(check-equal? (reduce '() (mpolynate '(x) '(fn + (var x) (fn |1|)))) '((1 . (1)) (1 . (0))))
;; reduce1 errors when the monomial is not divisible by the basis polynomial's lead.
(check-exn exn:fail? (λ () (reduce1 '(1 . (0 0)) (mpoly-var '(x y) 'x))))
;; the S-polynomial of p with itself is zero.
(check-equal? (spoly (mpolynate '(x y) '(fn + (fn * (var x) (var y)) (fn |1|)))
                     (mpolynate '(x y) '(fn + (fn * (var x) (var y)) (fn |1|))))
              '())
(check-equal? (term-of-monomial '(x y) '(3 . (0 0))) '(fn |3|))
(check-equal? (term-of-monomial '(x y) '(1 . (1 0))) '(var x))
(check-equal? (mpoly-pow '(x) (mpoly-var '(x) 'x) 0) '((1 . (0))))
(check-equal? (mpoly-pow '(x) (mpoly-var '(x) 'x) 2) '((1 . (2))))
(check-equal? (grobner-basis '(x) (list '(atom (rel = (fn * (var x) (var x)) (fn |1|)))))
              '((fn + (fn ^ (var x) (fn |2|)) (fn |-1|))))
