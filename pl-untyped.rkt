#lang racket/base

(require racket/match)

(provide (all-defined-out))

(define (psimplify1 fm)
  (define (v o v1 v2 v3)
    (match o
      ['and v1]
      ['or v2]
      ['iff v3]))
  (match fm
    ['(not #f) #t]
    ['(not #t) #f]
    [`(not (not ,p)) p]
    [(cons (and o (or 'and 'or 'iff)) (or (list p #f) (list #f p)))
     (v o #f p `(not ,p))]
    [(cons (and o (or 'and 'or 'iff)) (or (list p #t) (list #t p)))
     (v o p #t p)]
    [(cons 'imp (or (list #f p) (list p #t))) #t]
    [`(imp #t ,p) p]
    [`(imp ,p #f) `(not ,p)]
    [_ fm]))

(define (psimplify fm)
  (match fm
    [`(not ,p) (psimplify1 `(not ,(psimplify p)))]
    [(list (and o (or 'and 'or 'imp 'iff)) p q)
     (psimplify1 `(,o ,(psimplify p) ,(psimplify q)))]
    [_ fm]))
