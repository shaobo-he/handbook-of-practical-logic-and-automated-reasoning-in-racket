#lang racket/base

(require racket/set)

(provide (all-defined-out))

(define (unions sets)
  (set->list
   (foldl (compose set-union) (set) (map list->set sets))))

(define (union x y)
  (unions `(,x ,y)))

(define (subtract x y)
  (set->list
   (set-subtract
    (list->set x)
    (list->set y))))
