#lang racket/base

;; Property tests for core/lib: set algebra, finite partial functions, union-find.

(require rackunit
         rackcheck
         "common.rkt")
(require (only-in racket/list remove-duplicates))
(require (only-in "../../core/lib.rkt"
                  setify
                  union
                  unions
                  intersect
                  subtract
                  subset
                  psubset
                  set-eq
                  image
                  allpairs
                  distinctpairs
                  allsubsets
                  allnonemptysubsets
                  allsets
                  non
                  funpow
                  repeat
                  valmod
                  chop-list
                  index
                  earlier
                  undefined
                  update
                  undefine
                  apply
                  tryapplyd
                  defined
                  fpf
                  dom
                  graph
                  mapf
                  unequal
                  canonize
                  equivalent
                  equate))

;; ===== set algebra =====
(check-property big (property ([a gen:natlist] [b gen:natlist]) (set-eq (union a b) (union b a))))
(check-property big
                (property ([a gen:natlist] [b gen:natlist] [c gen:natlist])
                          (set-eq (union (union a b) c) (union a (union b c)))))
(check-property big (property ([a gen:natlist]) (set-eq (union a a) a)))
(check-property big
                (property ([a gen:natlist] [b gen:natlist]) (set-eq (intersect a b) (intersect b a))))
(check-property big
                (property ([a gen:natlist] [b gen:natlist]) ; absorption
                          (set-eq (intersect a (union a b)) a)))
(check-property big
                (property ([a gen:natlist] [b gen:natlist]) ; de Morgan-ish decomposition
                          (set-eq (union (subtract a b) (intersect a b)) a)))
(check-property big
                (property ([a gen:natlist] [b gen:natlist])
                          (and (subset (subtract a b) a) (null? (intersect (subtract a b) b)))))
(check-property big (property ([a gen:natlist]) (subset a a)))
(check-property big
                (property ([a gen:natlist] [b gen:natlist] [c gen:natlist])
                          (or (not (subset a b)) (not (subset b c)) (subset a c))))
(check-property big
                (property ([a gen:natlist] [b gen:natlist]) ; agrees with native sets
                          (eq? (and (subset a b) #t) (andmap (λ (x) (and (member x b) #t)) a))))
(check-property big (property ([a gen:natlist]) (not (psubset a a))))
(check-property big
                (property ([a gen:natlist] [b gen:natlist]) (not (and (psubset a b) (psubset b a)))))
(check-property big (property ([a gen:natlist]) (set-eq (setify (append a a)) a)))
(check-property big
                (property ([a gen:natlist]) (= (length (setify a)) (length (remove-duplicates a)))))
(check-property big
                (property ([a gen:natlist] [b gen:natlist])
                          (= (length (allpairs cons a b)) (* (length a) (length b)))))
(check-property big
                (property ([a gen:natlist])
                          (= (length (distinctpairs a))
                             (quotient (* (length a) (sub1 (length a))) 2))))
(check-property big (property ([a gen:natlist]) (= (length (allsubsets a)) (expt 2 (length a)))))
(check-property big
                (property ([a gen:natlist] [k gen:nat])
                          (<= (length (image (λ (x) (modulo x 3)) a)) (length a))))
(check-property big
                (property ([k gen:nat] [m (gen:integer-in 0 5)]
                                       [n (gen:integer-in 0 5)]) ; funpow additivity
                          (= (funpow (+ m n) add1 k) (funpow m add1 (funpow n add1 k)))))

;; ===== finite partial functions =====
(check-property big
                (property ([k gen:nat] [v gen:nat] [f gen:natlist])
                          (= (apply (update k v (fpf f f)) k) v)))
(check-property big
                (property ([k gen:nat] [j gen:nat] [v gen:nat])
                          (or (= j k) (= (tryapplyd (update k v undefined) j 99) 99))))
(check-property big
                (property ([k gen:nat] [v gen:nat])
                          (not (defined (undefine k (update k v undefined)) k))))
(check-property big (property ([ks gen:natlist]) (let ([d (setify ks)]) (set-eq (dom (fpf d d)) d))))
(check-property big
                (property ([ks gen:natlist])
                          (let ([d (setify ks)])
                            (andmap (λ (kv) (= (apply (fpf d d) (car kv)) (cdr kv)))
                                    (graph (fpf d d))))))
(check-property big
                (property ([ks gen:natlist] [k gen:nat])
                          (let ([d (setify ks)])
                            (or (not (member k d)) (= (apply (mapf add1 (fpf d d)) k) (add1 k))))))

;; ===== union-find =====
(check-property big (property ([a gen:nat] [b gen:nat]) (equivalent (equate (cons a b) unequal) a b)))
(check-property big
                (property ([a gen:nat] [b gen:nat] [c gen:nat]) ; transitivity of merging
                          (equivalent (equate (cons b c) (equate (cons a b) unequal)) a c)))
(check-property big
                (property ([a gen:nat] [b gen:nat])
                          (let ([p (equate (cons a b) unequal)])
                            (equal? (canonize p (canonize p a)) (canonize p a)))))

;; ===== local generators and oracle helpers =====
(define gen:nonempty-natlist
  (gen:map (gen:tuple gen:nat gen:natlist) (λ (t) (cons (car t) (cadr t)))))
;; a list paired with a valid split point 0..length, for chop-list
(define gen:chop-input
  (gen:bind gen:natlist (λ (l) (gen:map (gen:integer-in 0 (length l)) (λ (n) (cons n l))))))
;; a non-empty list paired with a valid index 0..length-1, for index
(define gen:list+index
  (gen:bind gen:nonempty-natlist
            (λ (l) (gen:map (gen:integer-in 0 (sub1 (length l))) (λ (i) (cons i l))))))

(define (fact n)
  (if (<= n 1)
      1
      (* n (fact (sub1 n)))))
(define (binom n k)
  (if (or (< k 0) (> k n))
      0
      (quotient (fact n) (* (fact k) (fact (- n k))))))
;; consecutive pairs (a.b)(b.c)... used to chain equate over a whole list
(define (consec-pairs l)
  (if (or (null? l) (null? (cdr l)))
      '()
      (cons (cons (car l) (cadr l)) (consec-pairs (cdr l)))))

;; ===== valmod (closure-based finite functions) =====
;; valmod a y f maps a->y and delegates every other key to f.
(check-property big
                (property ([a gen:nat] [y gen:nat] [k gen:nat])
                          (define f (λ (x) (+ x 100)))
                          (and (= ((valmod a y f) a) y)
                               (or (= k a) (= ((valmod a y f) k) (+ k 100))))))

;; ===== allsets: exactly C(len,m) distinct m-element subsets of l =====
(check-property big
                (property ([raw gen:natlist] [m (gen:integer-in 0 6)])
                          (define l (setify raw))
                          (define ss (allsets m l))
                          (and (= (length ss) (binom (length l) m)) ; correct count
                               (andmap (λ (s) (= (length s) m)) ss) ; each has m elems
                               (andmap (λ (s) (subset s l)) ss) ; each a subset of l
                               (= (length ss) (length (setify ss)))))) ; all distinct

;; ===== allsubsets / allnonemptysubsets =====
(check-property big
                (property ([raw gen:natlist])
                          (define d (setify raw))
                          (and (andmap (λ (s) (subset s d)) (allsubsets d)) ; all subsets
                               (set-eq (unions (allsubsets d)) d)))) ; cover the whole set
(check-property big
                (property ([raw gen:natlist])
                          (define d (setify raw))
                          (and (= (length (allnonemptysubsets d)) (sub1 (expt 2 (length d))))
                               (andmap pair? (allnonemptysubsets d)))))

;; ===== chop-list: splitting preserves the list and the prefix length =====
(check-property big
                (property ([ni gen:chop-input])
                          (define n (car ni))
                          (define l (cdr ni))
                          (let-values ([(a b) (chop-list n l)])
                            (and (equal? (append a b) l) (= (length a) n)))))

;; ===== index: returns a position holding the searched element =====
(check-property big
                (property ([il gen:list+index])
                          (define i (car il))
                          (define l (cdr il))
                          (define x (list-ref l i))
                          (equal? (list-ref l (index x l)) x)))

;; ===== earlier: a strict order by first occurrence, hence transitive =====
(check-property big
                (property ([l gen:natlist] [x gen:nat] [y gen:nat] [z gen:nat])
                          (or (not (and (earlier l x y) (earlier l y z))) (earlier l x z))))

;; ===== image: applies f to every element (dedup => length over setify) =====
(check-property big
                (property ([l gen:natlist])
                          (define f (λ (x) (+ x 10))) ; injective
                          (and (andmap (λ (x) (and (member (f x) (image f l)) #t)) l)
                               (= (length (image f l)) (length (setify l))))))

;; ===== repeat: iterates f until it raises; result is the last good value =====
(check-property big
                (property ([x gen:nat] [bound (gen:integer-in 0 6)])
                          (define f
                            (λ (n)
                              (if (< n bound)
                                  (add1 n)
                                  (error "done"))))
                          (= (repeat f x) (max x bound))))

;; ===== union-find: chaining equate over a list merges it into one class =====
(check-property big
                (property ([raw gen:natlist])
                          (define d (setify raw))
                          (or (< (length d) 2)
                              (let ([p (foldl equate unequal (consec-pairs d))])
                                (andmap (λ (x) (equivalent p (car d) x)) d)))))
