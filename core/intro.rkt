#lang racket/base

;; intro --- the introductory chapter's toy algebraic-expression
;; language: a datatype, a simplifier, and a lexer/parser/printer.
;;
;; Expressions are s-expressions: (var s) | (const n) | (add a b) | (mul a b)

(require racket/match)

(provide (all-defined-out))

;; ===== simplification =====
(define (simplify1 e)
  (match e
    [`(mul (const 0) ,x) '(const 0)]
    [`(mul ,x (const 0)) '(const 0)]
    [`(add (const 0) ,x) x]
    [`(add ,x (const 0)) x]
    [`(mul (const 1) ,x) x]
    [`(mul ,x (const 1)) x]
    [`(add (const ,m) (const ,n)) `(const ,(+ m n))]
    [`(mul (const ,m) (const ,n)) `(const ,(* m n))]
    [_ e]))

(define (simplify e)
  (match e
    [`(add ,e1 ,e2) (simplify1 `(add ,(simplify e1) ,(simplify e2)))]
    [`(mul ,e1 ,e2) (simplify1 `(mul ,(simplify e1) ,(simplify e2)))]
    [_ (simplify1 e)]))

;; ===== lexical analysis =====
(define (matches s)
  (define chars (string->list s))
  (λ (c) (and (member c chars) #t)))

(define space (matches " \t\n\r"))
(define punctuation (matches "()[]{},"))
(define symbolic (matches "~`!@#$%^&*-+=|\\:;<>.?/"))
(define numeric (matches "0123456789"))
(define alphanumeric (matches "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"))

;; consume the longest prefix satisfying prop; returns (values prefix-chars rest)
(define (lexwhile prop inp)
  (match inp
    [`(,c . ,cs)
     #:when (prop c)
     (let-values ([(tok rest) (lexwhile prop cs)])
       (values (cons c tok) rest))]
    [_ (values '() inp)]))

;; turn a list of characters into a list of token strings
(define (lex inp)
  (let-values ([(_ rest) (lexwhile space inp)])
    (match rest
      ['() '()]
      [`(,c . ,cs)
       (define prop
         (cond
           [(alphanumeric c) alphanumeric]
           [(symbolic c) symbolic]
           [else (λ (c) #f)]))
       (let-values ([(toktl rest2) (lexwhile prop cs)])
         (cons (list->string (cons c toktl)) (lex rest2)))])))

;; ===== parsing =====
(define (parse-expression i)
  (let-values ([(e1 i1) (parse-product i)])
    (match i1
      [`("+" . ,i1b)
       (let-values ([(e2 i2) (parse-expression i1b)])
         (values `(add ,e1 ,e2) i2))]
      [_ (values e1 i1)])))

(define (parse-product i)
  (let-values ([(e1 i1) (parse-atom i)])
    (match i1
      [`("*" . ,i1b)
       (let-values ([(e2 i2) (parse-product i1b)])
         (values `(mul ,e1 ,e2) i2))]
      [_ (values e1 i1)])))

(define (parse-atom i)
  (match i
    ['() (error 'parse "Expected an expression at end of input")]
    [`("(" . ,i1)
     (let-values ([(e2 i2) (parse-expression i1)])
       (match i2
         [`(")" . ,i3) (values e2 i3)]
         [_ (error 'parse "Expected closing bracket")]))]
    [`(,tok . ,i1)
     (if (andmap numeric (string->list tok))
         (values `(const ,(string->number tok)) i1)
         (values `(var ,tok) i1))]))

(define (make-parser pfn s)
  (let-values ([(expr rest) (pfn (lex (string->list s)))])
    (if (null? rest)
        expr
        (error 'parse "Unparsed input"))))

(define (parse-exp s)
  (make-parser parse-expression s))

;; ===== printing (with minimal bracketing) =====
(define (string-of-exp pr e)
  (match e
    [`(var ,s) s]
    [`(const ,n) (number->string n)]
    [`(add ,e1 ,e2)
     (define s (string-append (string-of-exp 3 e1) " + " (string-of-exp 2 e2)))
     (if (< 2 pr)
         (string-append "(" s ")")
         s)]
    [`(mul ,e1 ,e2)
     (define s (string-append (string-of-exp 5 e1) " * " (string-of-exp 4 e2)))
     (if (< 4 pr)
         (string-append "(" s ")")
         s)]))

(define (sprint-exp e)
  (string-append "<<" (string-of-exp 0 e) ">>"))
