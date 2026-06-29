#lang racket/base

;; Unit tests for prop/propexamples: the adder building blocks (halfsum,
;; halfcarry, carry, sum, fa), bit/bitlength helpers, congruent-to, and the
;; multiplier base case. Correctness of the full adders is checked by
;; evaluating against the arithmetic they are supposed to encode.

(require rackunit)
(require (only-in "../prop/prop.rkt" eval))
(require "../prop/propexamples.rkt")

;; ===== bitlength =====
(check-equal? (bitlength 0) 0)
(check-equal? (bitlength 1) 1)
(check-equal? (bitlength 2) 2)
(check-equal? (bitlength 3) 2)
(check-equal? (bitlength 4) 3)
(check-equal? (bitlength 7) 3)
(check-equal? (bitlength 8) 4)

;; ===== bit n x: the n-th bit of x (least significant first) =====
;; 5 = 101b
(check-true (bit 0 5))
(check-false (bit 1 5))
(check-true (bit 2 5))
;; 8 = 1000b
(check-false (bit 0 8))
(check-true (bit 3 8))

;; ===== half-adder building blocks =====
(check-equal? (halfsum '(atom a) '(atom b)) '(iff (atom a) (not (atom b))))
(check-equal? (halfcarry '(atom a) '(atom b)) '(and (atom a) (atom b)))
(check-equal? (ha '(atom x) '(atom y) '(atom s) '(atom c))
              '(and (iff (atom s) (iff (atom x) (not (atom y))))
                    (iff (atom c) (and (atom x) (atom y)))))

;; ===== full-adder components =====
(check-equal? (carry '(atom x) '(atom y) '(atom z))
              '(or (and (atom x) (atom y)) (and (or (atom x) (atom y)) (atom z))))
(check-equal? (sum '(atom x) '(atom y) '(atom z)) '(iff (iff (atom x) (not (atom y))) (not (atom z))))
(check-equal? (fa '(atom x) '(atom y) '(atom z) '(atom s) '(atom c))
              '(and (iff (atom s) (iff (iff (atom x) (not (atom y))) (not (atom z))))
                    (iff (atom c)
                         (or (and (atom x) (atom y)) (and (or (atom x) (atom y)) (atom z))))))

;; ===== halfsum is XOR, halfcarry is AND (exhaustively over the 4 rows) =====
(for* ([a (in-list '(#t #f))]
       [b (in-list '(#t #f))])
  (define v
    (λ (s)
      (cond
        [(eq? s 'a) a]
        [(eq? s 'b) b]
        [else #f])))
  (check-equal? (eval (halfsum '(atom a) '(atom b)) v) (not (eq? a b)))
  (check-equal? (eval (halfcarry '(atom a) '(atom b)) v) (and a b)))

;; ===== fa encodes s = (x+y+z) mod 2 and c = (x+y+z) div 2 =====
;; the constraint is satisfied exactly when s,c carry the true sum/carry bits
(define (b->n x)
  (if x 1 0))
(for* ([x (in-list '(#t #f))]
       [y (in-list '(#t #f))]
       [z (in-list '(#t #f))]
       [sv (in-list '(#t #f))]
       [cv (in-list '(#t #f))])
  (define total (+ (b->n x) (b->n y) (b->n z)))
  (define expected (and (eq? sv (= (modulo total 2) 1)) (eq? cv (>= total 2))))
  (define v
    (λ (q)
      (cond
        [(eq? q 's) sv]
        [(eq? q 'c) cv]
        [else #f])))
  (check-equal? (eval (fa (if x #t #f) (if y #t #f) (if z #t #f) '(atom s) '(atom c)) v) expected))

;; ===== carry/sum agree with fa's intended arithmetic too =====
(for* ([x (in-list '(#t #f))]
       [y (in-list '(#t #f))]
       [z (in-list '(#t #f))])
  (define total (+ (b->n x) (b->n y) (b->n z)))
  (define v (λ (q) #f))
  (check-equal? (eval (sum (if x #t #f) (if y #t #f) (if z #t #f)) v) (= (modulo total 2) 1))
  (check-equal? (eval (carry (if x #t #f) (if y #t #f) (if z #t #f)) v) (>= total 2)))

;; ===== congruent-to pins the index variables to the bits of a constant =====
;; 5 = 101b: x_0 asserted, x_1 negated, x_2 asserted
(check-equal? (congruent-to (mk-index "x") 5 3) '(and (atom x_0) (and (not (atom x_1)) (atom x_2))))
(let ([fm (congruent-to (mk-index "x") 5 3)])
  (check-true (eval fm
                    (λ (s)
                      (case s
                        [(x_0) #t]
                        [(x_1) #f]
                        [(x_2) #t]
                        [else #f]))))
  (check-false (eval fm
                     (λ (s)
                       (case s
                         [(x_0) #t]
                         [(x_1) #t]
                         [(x_2) #t]
                         [else #f])))))

;; ===== multiplier base case (n = 1): out_0 = x_0_0, and out_1 is forced false =====
(check-equal? (multiplier (mk-index2 "x") (mk-index2 "u") (mk-index2 "v") (mk-index "out") 1)
              '(and (iff (atom out_0) (atom x_0_0)) (not (atom out_1))))
