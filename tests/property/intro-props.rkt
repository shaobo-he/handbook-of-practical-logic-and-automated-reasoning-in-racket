#lang racket/base

;; Property tests for core/intro: the expression simplifier, parser, printer.

(require rackunit
         rackcheck
         racket/match
         "common.rkt")
(require (only-in "../../core/intro.rkt" [simplify intro-simplify] parse-exp string-of-exp))

(define (expr-gen n)
  (if (<= n 0)
      (gen:choice (gen:map (gen:integer-in 0 5) (λ (k) `(const ,k)))
                  (gen:one-of '((var "x") (var "y"))))
      (gen:bind (gen:one-of '(add mul))
                (λ (op)
                  (gen:map (gen:tuple (expr-gen (sub1 n)) (expr-gen (sub1 n)))
                           (λ (ab) `(,op ,(car ab) ,(cadr ab))))))))
(define (eval-expr e env)
  (match e
    [`(var ,s) (hash-ref env s)]
    [`(const ,k) k]
    [`(add ,a ,b) (+ (eval-expr a env) (eval-expr b env))]
    [`(mul ,a ,b) (* (eval-expr a env) (eval-expr b env))]))

;; simplification preserves value under every assignment, and is idempotent
(check-property big
                (property ([e (expr-gen 4)] [vx (gen:integer-in -3 3)] [vy (gen:integer-in -3 3)])
                          (= (eval-expr e (hash "x" vx "y" vy))
                             (eval-expr (intro-simplify e) (hash "x" vx "y" vy)))))
(check-property big
                (property ([e (expr-gen 4)])
                          (equal? (intro-simplify (intro-simplify e)) (intro-simplify e))))
;; parse . print round-trips up to value
(check-property big
                (property ([e (expr-gen 3)] [vx (gen:integer-in -3 3)] [vy (gen:integer-in -3 3)])
                          (= (eval-expr e (hash "x" vx "y" vy))
                             (eval-expr (parse-exp (string-of-exp 0 e)) (hash "x" vx "y" vy)))))
