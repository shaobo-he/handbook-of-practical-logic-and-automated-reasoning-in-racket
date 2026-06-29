#lang racket/base

;; Property tests for prop/propexamples against arithmetic oracles: bitlength
;; and bit match Racket's native bit operations, the half/full-adder gates
;; compute XOR/AND/sum/carry, and the ripple-carry adder and naive multiplier
;; encode real binary addition and multiplication (checked with the DPLL solver).

(require rackunit
         rackcheck
         "common.rkt")
(require (only-in "../../prop/prop.rkt" eval))
(require (only-in "../../prop/dp.rkt" dplltaut dpllsat))
(require (only-in "../../prop/propexamples.rkt"
                  bitlength
                  bit
                  halfsum
                  halfcarry
                  carry
                  sum
                  mk-index
                  mk-index2
                  congruent-to
                  ripplecarry0
                  multiplier))

;; ===== bitlength matches integer-length; bit matches bitwise-bit-set? =====
(define gen:bignat (gen:integer-in 0 4095))
(check-property big (property ([n gen:bignat]) (= (bitlength n) (integer-length n))))
(check-property big
                (property ([n gen:bignat] [i (gen:integer-in 0 15)])
                          (eq? (bit i n) (bitwise-bit-set? n i))))

;; ===== half-adder gates: XOR and AND over all boolean inputs =====
(check-property big
                (property ([a gen:boolean] [b gen:boolean])
                          (define v
                            (λ (s)
                              (cond
                                [(eq? s 'a) a]
                                [(eq? s 'b) b]
                                [else #f])))
                          (and (eq? (eval (halfsum '(atom a) '(atom b)) v) (not (eq? a b)))
                               (eq? (eval (halfcarry '(atom a) '(atom b)) v) (and a b)))))

;; ===== full-adder gates: sum = (x+y+z) mod 2, carry = (x+y+z) div 2 =====
(define (b->n x)
  (if x 1 0))
(check-property
 big
 (property ([x gen:boolean] [y gen:boolean] [z gen:boolean])
           (define total (+ (b->n x) (b->n y) (b->n z)))
           (define v (λ (s) #f))
           (and (eq? (eval (sum (if x #t #f) (if y #t #f) (if z #t #f)) v) (= (modulo total 2) 1))
                (eq? (eval (carry (if x #t #f) (if y #t #f) (if z #t #f)) v) (>= total 2)))))

;; index function returning the constant bits of a fixed integer
(define ((const-bits k) i)
  (if (bit i k) #t #f))

;; ===== ripple-carry adder computes binary addition =====
;; with x,y pinned to the bits of a,b, the n output bits are forced to the low n
;; bits of a+b, and the adder is always satisfiable (it is a function)
(define gen:add
  (gen:bind (gen:integer-in 1 3)
            (λ (n)
              (gen:map (gen:tuple (gen:integer-in 0 (sub1 (expt 2 n)))
                                  (gen:integer-in 0 (sub1 (expt 2 n))))
                       (λ (ab) (list n (car ab) (cadr ab)))))))
(check-property
 low
 (property ([nab gen:add])
           (define n (car nab))
           (define a (cadr nab))
           (define b (caddr nab))
           (define F (ripplecarry0 (const-bits a) (const-bits b) (mk-index "c") (mk-index "out") n))
           (and (dpllsat F) (dplltaut `(imp ,F ,(congruent-to (mk-index "out") (+ a b) n))))))

;; ===== naive multiplier computes binary multiplication =====
(define gen:mul
  (gen:bind (gen:integer-in 1 2)
            (λ (ord)
              (gen:map (gen:tuple (gen:integer-in 0 (sub1 (expt 2 ord)))
                                  (gen:integer-in 0 (sub1 (expt 2 ord))))
                       (λ (ab) (list ord (car ab) (cadr ab)))))))
(check-property tiny
                (property ([oab gen:mul])
                          (define ord (car oab))
                          (define a (cadr oab))
                          (define b (caddr oab))
                          (define (m i)
                            (λ (j) `(and ,((const-bits a) i) ,((const-bits b) j))))
                          (define MUL
                            (multiplier m (mk-index2 "u") (mk-index2 "v") (mk-index "out") ord))
                          (define width (max (+ ord 1) (* 2 ord)))
                          (dplltaut `(imp ,MUL ,(congruent-to (mk-index "out") (* a b) width)))))
