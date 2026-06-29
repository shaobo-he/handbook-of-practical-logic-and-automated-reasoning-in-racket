#lang racket/base

;; propexamples --- families of propositional formulas: Ramsey numbers,
;; ripple-carry / carry-select adders, multipliers, and primality.

(require racket/match)
(require (only-in racket/list range))
(require (only-in "../core/lib.rkt" allsets))
(require (only-in "../core/formulas.rkt" list-conj list-disj))
(require (only-in "prop.rkt" psimplify))

(provide (all-defined-out))

;; ===== Ramsey number assertion R(s,t) <= n =====
(define (ramsey s t n)
  (define vertices (range 1 (add1 n)))
  (define yesgrps (map (λ (g) (allsets 2 g)) (allsets s vertices)))
  (define nogrps (map (λ (g) (allsets 2 g)) (allsets t vertices)))
  (define (e pair)
    `(atom ,(string->symbol
             (string-append "p_" (number->string (car pair)) "_" (number->string (cadr pair))))))
  `(or ,(list-disj (map (λ (grp) (list-conj (map e grp))) yesgrps))
       ,(list-disj (map (λ (grp) (list-conj (map (λ (p) `(not ,(e p))) grp))) nogrps))))

;; ===== half / full adder building blocks =====
(define (halfsum x y)
  `(iff ,x (not ,y)))
(define (halfcarry x y)
  `(and ,x ,y))
(define (ha x y s c)
  `(and (iff ,s ,(halfsum x y)) (iff ,c ,(halfcarry x y))))

(define (carry x y z)
  `(or (and ,x ,y) (and (or ,x ,y) ,z)))
(define (sum x y z)
  (halfsum (halfsum x y) z))
(define (fa x y z s c)
  `(and (iff ,s ,(sum x y z)) (iff ,c ,(carry x y z))))

(define (conjoin f l)
  (list-conj (map f l)))

;; index functions are curried procedures over ints: (mk-index "x") is a unary
;; fn with (... i) = atom x_i, and (mk-index2 "u") is a binary fn with
;; ((... i) j) = atom u_i_j. The indexed atom symbols are built on demand.
(define ((mk-index x) i)
  `(atom ,(string->symbol (string-append x "_" (number->string i)))))
(define (((mk-index2 x) i) j)
  `(atom ,(string->symbol (string-append x "_" (number->string i) "_" (number->string j)))))

;; ===== ripple-carry adder =====
(define (ripplecarry x y c out n)
  (conjoin (λ (i) (fa (x i) (y i) (c i) (out i) (c (+ i 1)))) (range 0 n)))

;; ripplecarry0/1 wrap ripplecarry with a carry-in index function that overrides
;; bit 0 with the constant #f / #t (the lambda lets us plug a fixed carry-in
;; while still deferring to c for the internal carries); psimplify then folds
;; those constants away.
(define (ripplecarry0 x y c out n)
  (psimplify (ripplecarry x
                          y
                          (λ (i)
                            (if (= i 0)
                                #f
                                (c i)))
                          out
                          n)))

(define (ripplecarry1 x y c out n)
  (psimplify (ripplecarry x
                          y
                          (λ (i)
                            (if (= i 0)
                                #t
                                (c i)))
                          out
                          n)))

;; ===== carry-select adder =====
(define (mux sel in0 in1)
  `(or (and (not ,sel) ,in0) (and ,sel ,in1)))
(define ((offset n x) i)
  (x (+ n i)))

;; carry-select adder: process the inputs in blocks of k bits. Each block is
;; computed twice in parallel -- once assuming carry-in 0 (ripplecarry0) and once
;; assuming carry-in 1 (ripplecarry1) -- and a mux picks the right result from
;; the previous block's actual carry-out. k* = min n k handles a final short
;; block (k* < k), where the recursion stops; otherwise it recurses on the
;; remaining bits offset by k.
(define (carryselect x y c0 c1 s0 s1 c s n k)
  (define k* (min n k))
  (define fm
    `(and (and ,(ripplecarry0 x y c0 s0 k*) ,(ripplecarry1 x y c1 s1 k*))
          (and (iff ,(c k*) ,(mux (c 0) (c0 k*) (c1 k*)))
               ,(conjoin (λ (i) `(iff ,(s i) ,(mux (c 0) (s0 i) (s1 i)))) (range 0 k*)))))
  (if (< k* k)
      fm
      `(and ,fm
            ,(carryselect (offset k x)
                          (offset k y)
                          (offset k c0)
                          (offset k c1)
                          (offset k s0)
                          (offset k s1)
                          (offset k c)
                          (offset k s)
                          (- n k)
                          k))))

(define (mk-adder-test n k)
  (match-define `(,x ,y ,c ,s ,c0 ,s0 ,c1 ,s1 ,c2 ,s2)
    (map mk-index '("x" "y" "c" "s" "c0" "s0" "c1" "s1" "c2" "s2")))
  `(imp (and (and ,(carryselect x y c0 c1 s0 s1 c s n k) (not ,(c 0))) ,(ripplecarry0 x y c2 s2 n))
        (and (iff ,(c n) ,(c2 n)) ,(conjoin (λ (i) `(iff ,(s i) ,(s2 i))) (range 0 n)))))

;; ===== ripple-shift stage and naive multiplier =====
(define (rippleshift u v c z w n)
  (ripplecarry0 u
                v
                (λ (i)
                  (if (= i n)
                      (w (- n 1))
                      (c (+ i 1))))
                (λ (i)
                  (if (= i 0)
                      z
                      (w (- i 1))))
                n))

;; naive shift-and-add multiplier of two n-bit numbers whose partial-product
;; bits are supplied by x (x i j = bit i of operand 1 AND bit j of operand 2).
;; n=1: the product is the single AND bit (out 0), and out 1 is forced false.
;; n=2: two rippleshift-free output bits taken straight from u_2. n>=2: chain
;; rippleshift stages through the u_k carry/partial rows. psimplify removes the
;; constant-#f wires introduced at the row boundaries.
(define (multiplier x u v out n)
  (if (= n 1)
      `(and (iff ,(out 0) ,((x 0) 0)) (not ,(out 1)))
      (psimplify `(and (iff ,(out 0) ,((x 0) 0))
                       (and ,(rippleshift (λ (i)
                                            (if (= i (- n 1))
                                                #f
                                                ((x 0) (+ i 1))))
                                          (x 1)
                                          (v 2)
                                          (out 1)
                                          (u 2)
                                          n)
                            ,(if (= n 2)
                                 `(and (iff ,(out 2) ,((u 2) 0)) (iff ,(out 3) ,((u 2) 1)))
                                 (conjoin (λ (k)
                                            (rippleshift (u k)
                                                         (x k)
                                                         (v (+ k 1))
                                                         (out k)
                                                         (if (= k (- n 1))
                                                             (λ (i) (out (+ n i)))
                                                             (u (+ k 1)))
                                                         n))
                                          (range 2 n))))))))

;; ===== primality via propositional logic =====
(define (bitlength x)
  (if (= x 0)
      0
      (+ 1 (bitlength (quotient x 2)))))
(define (bit n x)
  (if (= n 0)
      (= (modulo x 2) 1)
      (bit (- n 1) (quotient x 2))))

;; assert that the n index variables x_0..x_{n-1} spell out the binary digits of
;; the constant m: x_i is asserted where bit i of m is 1, negated where it is 0.
;; Used by `prime` to pin the multiplier's output to the candidate p.
(define (congruent-to x m n)
  (conjoin (λ (i)
             (if (bit i m)
                 (x i)
                 `(not ,(x i))))
           (range 0 n)))

(define (prime p)
  (match-define `(,x ,y ,out) (map mk-index '("x" "y" "out")))
  (define (m i)
    (λ (j) `(and ,(x i) ,(y j))))
  (match-define `(,u ,v) (map mk-index2 '("u" "v")))
  (define n (bitlength p))
  `(not (and ,(multiplier m u v out (- n 1)) ,(congruent-to out p (max n (- (* 2 n) 2))))))
