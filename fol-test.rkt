#lang racket/base

(require rackunit)
(require racket/match)
(require "fol-untyped.rkt")

(define bool-domain '(#t #f))

(define (bool-func f args)
  (match f
    ['|0| #f]
    ['|1| #t]
    ['+ (not (apply equal? args))]
    ['* (apply (λ (x y) (and x y)) args)]))

(define (bool-pred p args)
  (match p
    ['= (apply equal? args)]))

(check-true (termval bool-func #f '(fn * (fn |1|) (fn |1|))))
(check-false (holds bool-domain bool-func bool-pred #f '(atom (rel = (fn |0|) (fn * (fn |1|) (fn |1|))))))
