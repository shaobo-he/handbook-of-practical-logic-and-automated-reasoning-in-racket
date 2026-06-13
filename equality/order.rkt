#lang racket/base

;; order.fs --- term orderings: term size and the lexicographic path order
;; (LPO), with a convenient precedence-from-a-list weighting.

(require racket/match)
(require (only-in "../core/lib.rkt" earlier))
(require (only-in "../fol/fol.rkt" fvt))

(provide (all-defined-out))

(define (termsize tm)
  (match tm
    [`(var ,x) 1]
    [`(fn ,f ,@args) (foldr (λ (t n) (+ (termsize t) n)) 1 args)]))

;; lexicographic extension of an order
(define (lexord ord l1 l2)
  (match* (l1 l2)
    [((cons h1 t1) (cons h2 t2))
     (if (ord h1 h2)
         (= (length t1) (length t2))
         (and (equal? h1 h2) (lexord ord t1 t2)))]
    [(_ _) #f]))

;; lexicographic path order; w compares (symbol . arity) pairs
(define (lpo-gt w s t)
  (match* (s t)
    [(_ `(var ,x)) (and (not (equal? s t)) (and (member x (fvt s)) #t))]
    [(`(fn ,f ,@fargs) `(fn ,g ,@gargs))
     (or (ormap (λ (si) (lpo-ge w si t)) fargs)
         (and (andmap (λ (ti) (lpo-gt w s ti)) gargs)
              (or (and (equal? f g) (lexord (λ (a b) (lpo-gt w a b)) fargs gargs))
                  (w (cons f (length fargs)) (cons g (length gargs))))))]
    [(_ _) #f]))

(define (lpo-ge w s t) (or (equal? s t) (lpo-gt w s t)))

;; precedence given by position in a list (earlier = smaller)
(define (weight lis fn1 fn2)
  (if (equal? (car fn1) (car fn2))
      (> (cdr fn1) (cdr fn2))
      (earlier lis (car fn2) (car fn1))))
