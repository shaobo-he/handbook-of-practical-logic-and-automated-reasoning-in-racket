#lang racket/base

;; Property tests for core/intro: the expression simplifier, parser, printer.

(require rackunit
         rackcheck
         racket/match
         "common.rkt")
(require (only-in "../../core/intro.rkt"
                  [simplify intro-simplify]
                  simplify1
                  parse-exp
                  string-of-exp
                  lex))

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

;; simplify reaches a fixed point: one more simplify1 pass changes nothing.
(check-property big
                (property ([e (expr-gen 4)])
                          (equal? (simplify1 (intro-simplify e)) (intro-simplify e))))

;; ===== parser precedence / associativity / parentheses =====
;; atoms are single tokens (a variable or a non-negative numeral), each paired
;; with the AST parse-exp should yield for it.
(define gen:atom
  (gen:choice (gen:map (gen:one-of '("x" "y" "z")) (λ (s) (cons s `(var ,s))))
              (gen:map (gen:integer-in 0 9) (λ (n) (cons (number->string n) `(const ,n))))))

;; * binds tighter than +: "a+b*c" => (add a (mul b c))
(check-property big
                (property ([a gen:atom] [b gen:atom] [c gen:atom])
                          (equal? (parse-exp (string-append (car a) "+" (car b) "*" (car c)))
                                  `(add ,(cdr a) (mul ,(cdr b) ,(cdr c))))))
;; "a*b+c" => (add (mul a b) c)
(check-property big
                (property ([a gen:atom] [b gen:atom] [c gen:atom])
                          (equal? (parse-exp (string-append (car a) "*" (car b) "+" (car c)))
                                  `(add (mul ,(cdr a) ,(cdr b)) ,(cdr c)))))
;; parentheses override precedence: "(a+b)*c" => (mul (add a b) c)
(check-property big
                (property ([a gen:atom] [b gen:atom] [c gen:atom])
                          (equal? (parse-exp (string-append "(" (car a) "+" (car b) ")*" (car c)))
                                  `(mul (add ,(cdr a) ,(cdr b)) ,(cdr c)))))
;; both operators are right-associative: "a+b+c" => (add a (add b c))
(check-property big
                (property ([a gen:atom] [b gen:atom] [c gen:atom])
                          (equal? (parse-exp (string-append (car a) "+" (car b) "+" (car c)))
                                  `(add ,(cdr a) (add ,(cdr b) ,(cdr c))))))
(check-property big
                (property ([a gen:atom] [b gen:atom] [c gen:atom])
                          (equal? (parse-exp (string-append (car a) "*" (car b) "*" (car c)))
                                  `(mul ,(cdr a) (mul ,(cdr b) ,(cdr c))))))

;; ===== lexing soundness: printed expressions lex into non-empty tokens =====
(check-property big
                (property ([e (expr-gen 3)])
                          (andmap (λ (t) (> (string-length t) 0))
                                  (lex (string->list (string-of-exp 0 e))))))
