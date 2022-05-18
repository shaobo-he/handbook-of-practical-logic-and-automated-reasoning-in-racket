#lang racket/base

(require rackunit)
(require "pl-untyped.rkt")

;; simplification tests
(check-equal?
 (psimplify '(imp (imp #t (iff x #f)) (not (or y (and #f z)))))
 '(imp (not x) (not y)))

(check-equal?
 (psimplify '(or (imp (imp x y) #t) (not #f)))
 #t)