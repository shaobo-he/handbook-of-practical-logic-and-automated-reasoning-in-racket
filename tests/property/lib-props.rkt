#lang racket/base

;; Property tests for core/lib: set algebra, finite partial functions, union-find.

(require rackunit
         rackcheck
         "common.rkt")
(require (only-in racket/list remove-duplicates))
(require (only-in "../../core/lib.rkt"
                  setify
                  union
                  intersect
                  subtract
                  subset
                  psubset
                  set-eq
                  image
                  allpairs
                  distinctpairs
                  allsubsets
                  non
                  funpow
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
