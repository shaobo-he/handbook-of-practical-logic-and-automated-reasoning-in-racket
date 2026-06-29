#lang racket/base

;; Unit tests for the intro chapter: the toy algebraic-expression language --
;; its simplifier (simplify1 / simplify), lexer (matches / lex), parser
;; (parse-exp: precedence, associativity, parentheses, errors), and the
;; minimal-bracketing printer (string-of-exp / sprint-exp).

(require rackunit)
(require "../core/intro.rkt")

;; ===== simplify1: each rewrite rule in isolation =====
(check-equal? (simplify1 '(mul (const 0) (var "x"))) '(const 0)) ; 0 * x
(check-equal? (simplify1 '(mul (var "x") (const 0))) '(const 0)) ; x * 0
(check-equal? (simplify1 '(add (const 0) (var "x"))) '(var "x")) ; 0 + x
(check-equal? (simplify1 '(add (var "x") (const 0))) '(var "x")) ; x + 0
(check-equal? (simplify1 '(mul (const 1) (var "x"))) '(var "x")) ; 1 * x
(check-equal? (simplify1 '(mul (var "x") (const 1))) '(var "x")) ; x * 1
(check-equal? (simplify1 '(add (const 2) (const 3))) '(const 5)) ; constant folding
(check-equal? (simplify1 '(mul (const 2) (const 3))) '(const 6)) ; constant folding
;; simplify1 is a single shallow rewrite: non-matching nodes pass through, and
;; it does NOT recurse (so a reducible child is left untouched).
(check-equal? (simplify1 '(var "x")) '(var "x"))
(check-equal? (simplify1 '(add (mul (const 0) (var "x")) (const 1)))
              '(add (mul (const 0) (var "x")) (const 1)))

;; ===== simplify: bottom-up, reaches a normal form =====
(check-equal? (simplify '(mul (const 2) (add (const 0) (const 3)))) '(const 6))
(check-equal? (simplify '(add (mul (const 0) (var "x")) (var "y"))) '(var "y"))
(check-equal? (simplify '(mul (add (const 1) (const 1)) (var "x"))) '(mul (const 2) (var "x")))
(check-equal? (simplify '(var "x")) '(var "x")) ; atom unchanged

;; ===== matches: character-class predicate =====
(check-true ((matches "abc") #\a))
(check-false ((matches "abc") #\x))
(check-true (boolean? ((matches "abc") #\a))) ; forced to a real boolean

;; ===== lex: tokenization =====
(check-equal? (lex (string->list "a+b")) '("a" "+" "b"))
(check-equal? (lex (string->list "a + b")) '("a" "+" "b")) ; whitespace skipped
(check-equal? (lex (string->list "(a+b)")) '("(" "a" "+" "b" ")")) ; brackets are single tokens
(check-equal? (lex (string->list "")) '()) ; empty input
(check-equal? (lex (string->list "a  \n  b")) '("a" "b")) ; consecutive whitespace
(check-equal? (lex (string->list "2*30")) '("2" "*" "30")) ; multi-digit number
(check-equal? (lex (string->list "==>")) '("==>")) ; a symbolic run is one token

;; ===== parse-exp: atoms =====
(check-equal? (parse-exp "42") '(const 42))
(check-equal? (parse-exp "x") '(var "x"))
(check-equal? (parse-exp "x'") '(var "x'")) ; apostrophe is alphanumeric
(check-equal? (parse-exp "x_y") '(var "x_y")) ; underscore is alphanumeric

;; ===== parse-exp: precedence (* binds tighter than +) =====
(check-equal? (parse-exp "2+3*4") '(add (const 2) (mul (const 3) (const 4))))
(check-equal? (parse-exp "2*3+4") '(add (mul (const 2) (const 3)) (const 4)))

;; ===== parse-exp: associativity (both operators are right-associative) =====
(check-equal? (parse-exp "1+2+3") '(add (const 1) (add (const 2) (const 3))))
(check-equal? (parse-exp "1*2*3") '(mul (const 1) (mul (const 2) (const 3))))

;; ===== parse-exp: parentheses override precedence =====
(check-equal? (parse-exp "(2+3)*4") '(mul (add (const 2) (const 3)) (const 4)))
(check-equal? (parse-exp "2*(3+4)") '(mul (const 2) (add (const 3) (const 4))))

;; ===== parse-exp: error cases =====
(check-exn exn:fail? (λ () (parse-exp ""))) ; expected an expression
(check-exn exn:fail? (λ () (parse-exp "(a b)"))) ; expected closing bracket
(check-exn exn:fail? (λ () (parse-exp "(a"))) ; unterminated group
(check-exn exn:fail? (λ () (parse-exp "a b"))) ; unparsed trailing input

;; ===== string-of-exp: minimal bracketing =====
(check-equal? (string-of-exp 0 '(const 42)) "42")
(check-equal? (string-of-exp 0 '(var "x")) "x")
(check-equal? (string-of-exp 0 '(add (const 2) (const 3))) "2 + 3") ; no parens
(check-equal? (string-of-exp 0 '(mul (const 2) (const 3))) "2 * 3") ; no parens
;; mul does not need parens around an add in its own context only when the add
;; is at top level; here the add is an operand of mul, so it is bracketed.
(check-equal? (string-of-exp 0 '(mul (const 2) (add (const 0) (const 3)))) "2 * (0 + 3)")
(check-equal? (string-of-exp 0 '(add (mul (const 2) (const 3)) (const 4))) "2 * 3 + 4")
;; a sufficiently high surrounding precedence forces parens around an add
(check-equal? (string-of-exp 5 '(add (const 2) (const 3))) "(2 + 3)")

;; ===== sprint-exp: << >> wrapping =====
(check-equal? (sprint-exp '(const 5)) "<<5>>")
(check-equal? (sprint-exp '(add (const 2) (const 3))) "<<2 + 3>>")
