#lang racket/base

(require racket/set)

(provide unions)

(define (unions sets)
  (foldl set-union (set) sets))
