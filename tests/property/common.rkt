#lang racket/base

;; Shared rackcheck configs, generators, and oracles for the property suite.
;; Each tests/property/*-props.rkt file requires this module.

(require rackcheck
         racket/match)
(require (only-in "../../lcf/limitations.rkt" numeral))

(provide (all-defined-out))

;; ===== configs: high volume, scaled down only for expensive procedures =====
(define big (make-config #:tests 1500))
(define mid (make-config #:tests 400))
(define low (make-config #:tests 120))
(define tiny (make-config #:tests 30))
(define poly (make-config #:tests 250))

;; ===== generator helpers =====
(define (binop-gen ops sub n)
  (gen:bind (gen:one-of ops)
            (λ (op)
              (gen:map (gen:tuple (sub (quotient n 2)) (sub (quotient n 2)))
                       (λ (pq) `(,op ,(car pq) ,(cadr pq)))))))
(define (quant-gen quants vars sub n)
  (gen:bind (gen:one-of quants)
            (λ (q)
              (gen:bind (gen:one-of vars) (λ (v) (gen:map (sub (sub1 n)) (λ (p) `(,q ,v ,p))))))))

;; ===== propositional formulas over {p,q,r} =====
(define (prop-gen-over as n [consts? #t])
  (define base
    (if consts?
        (gen:choice (gen:one-of as) (gen:const #t) (gen:const #f))
        (gen:one-of as)))
  (let loop ([n n])
    (if (<= n 0)
        base
        (gen:frequency (list (cons 1 base)
                             (cons 2 (gen:map (loop (sub1 n)) (λ (p) `(not ,p))))
                             (cons 4 (binop-gen '(and or imp iff) loop n)))))))
(define gen:prop (prop-gen-over '((atom p) (atom q) (atom r)) 4))
(define gen:small-prop (prop-gen-over '((atom (rel p)) (atom (rel q))) 3))
;; constant-free formulas: lcftaut (the LCF kernel prover) targets formulas over
;; genuine atoms and does not handle the #t/#f constants
(define gen:prop-nc (prop-gen-over '((atom p) (atom q) (atom r)) 4 #f))

;; ===== first-order terms over vars {x,y,z} and funcs a/f/g =====
(define (term-gen n)
  (if (<= n 0)
      (gen:choice (gen:one-of '((var x) (var y) (var z))) (gen:const '(fn a)))
      (gen:frequency (list (cons 2 (gen:one-of '((var x) (var y) (var z))))
                           (cons 1 (gen:const '(fn a)))
                           (cons 2 (gen:map (term-gen (sub1 n)) (λ (t) `(fn f ,t))))
                           (cons 2
                                 (gen:map (gen:tuple (term-gen (sub1 n)) (term-gen (sub1 n)))
                                          (λ (st) `(fn g ,(car st) ,(cadr st)))))))))
(define gen:term (term-gen 3))

;; ===== naturals and arithmetic terms over 0/S/+/* (oracle: native arithmetic) =====
(define gen:nat (gen:integer-in 0 6))
(define gen:natlist (gen:list gen:nat #:max-length 6))
(define (nat-gen n)
  (if (<= n 0)
      (gen:map (gen:integer-in 0 3) numeral)
      (gen:bind (gen:one-of '(+ *))
                (λ (op)
                  (gen:map (gen:tuple (nat-gen (sub1 n)) (nat-gen (sub1 n)))
                           (λ (ab) `(fn ,op ,(car ab) ,(cadr ab))))))))
(define (nat-value t)
  (match t
    [`(fn |0|) 0]
    [`(fn S ,a) (add1 (nat-value a))]
    [`(fn + ,a ,b) (+ (nat-value a) (nat-value b))]
    [`(fn * ,a ,b) (* (nat-value a) (nat-value b))]))
