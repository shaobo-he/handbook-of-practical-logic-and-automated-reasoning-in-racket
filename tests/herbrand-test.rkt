#lang racket/base

(require rackunit)
(require "../fol/herbrand.rkt")

;; Drinker's principle: exists x. forall y. P(x) ==> P(y)   (valid)
(define drinker '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y)))))))

;; universal modus ponens (valid)
(define ump
  '(imp (and (forall x (imp (atom (rel P (var x))) (atom (rel Q (var x)))))
             (forall x (atom (rel P (var x)))))
        (forall x (atom (rel Q (var x))))))

;; each procedure terminates on a valid formula, returning the instance count
(check-pred exact-positive-integer? (gilmore drinker))
(check-pred exact-positive-integer? (davisputnam drinker))
(check-pred exact-positive-integer? (davisputnam002 drinker))

(check-pred exact-positive-integer? (gilmore ump))
(check-pred exact-positive-integer? (davisputnam ump))

;; the refinement keeps no more instances than the full run
(check-true (<= (davisputnam002 drinker) (davisputnam drinker)))
