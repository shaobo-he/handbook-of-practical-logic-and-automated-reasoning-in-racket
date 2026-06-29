#lang racket/base

;; Unit tests for the lib utilities: sets, list helpers, finite partial
;; functions, and the union-find ("partition") structure.

(require rackunit)
(require "../core/lib.rkt")

;; ===== sets (duplicate-free lists; order-independent, so sort to compare) =====
(check-equal? (sort (setify '(3 1 2 1 3 2)) <) '(1 2 3))
(check-equal? (sort (unions '((1 2) (2 3) (3 4))) <) '(1 2 3 4))
(check-equal? (sort (union '(1 2 3) '(2 3 4)) <) '(1 2 3 4))
(check-equal? (sort (intersect '(1 2 3) '(2 3 4)) <) '(2 3))
(check-equal? (sort (subtract '(1 2 3 4) '(2 4)) <) '(1 3))
(check-true (subset '(1 2) '(1 2 3)))
(check-false (subset '(1 2 3) '(1 2)))
(check-true (psubset '(1 2) '(1 2 3)))
(check-false (psubset '(1 2) '(1 2)))
(check-true (set-eq '(1 2 3) '(3 2 1)))
(check-false (set-eq '(1 2) '(1 2 3)))
(check-equal? (sort (image (λ (x) (* x x)) '(1 2 3 2)) <) '(1 4 9))
(check-equal? (insert 5 '(1 2)) '(5 1 2))
(check-equal? (insert 1 '(1 2)) '(1 2))

;; ===== combinatorial helpers =====
(check-equal? (allpairs + '(1 2) '(10 20)) '(11 21 12 22))
(check-equal? (distinctpairs '(1 2 3)) '((1 . 2) (1 . 3) (2 . 3)))
(check-equal? (length (allsubsets '(1 2 3))) 8)
(check-equal? (length (allnonemptysubsets '(1 2 3))) 7)
(check-equal? (length (allsets 2 '(1 2 3))) 3)
(check-equal? (allsets 0 '(1 2)) '(()))
(check-equal? (allsets 2 '(1)) '())

;; ===== list helpers =====
(check-equal? (let-values ([(a b) (chop-list 2 '(1 2 3 4))])
                (list a b))
              '((1 2) (3 4)))
(check-equal? (index 'c '(a b c d)) 2)
(check-exn exn:fail? (λ () (index 'z '(a b))))
(check-equal? (butlast '(1 2 3)) '(1 2))
(check-equal? (insertat 1 'x '(a b c)) '(a x b c))
(check-equal? (insertat 0 'x '(a)) '(x a))
(check-true (earlier '(a b c) 'a 'b))
(check-false (earlier '(a b c) 'b 'a))
(check-equal? (funpow 3 add1 0) 3)
(check-equal? (funpow 0 add1 5) 5)
(check-equal? (first 0 (λ (n) (> n 3))) 4)
(check-equal? (minimize (λ (x) (* x x)) '(-2 1 3)) 1)
(check-equal? (maximize (λ (x) (* x x)) '(-2 1 3)) 3)
(check-true (can car '(1 2)))
(check-false (can car '()))
(check-true ((non even?) 3))
(check-false ((non even?) 4))
(check-equal? (tryfind (λ (x)
                         (if (even? x)
                             x
                             (error "odd")))
                       '(1 3 4 5))
              4)
(check-exn exn:fail?
           (λ ()
             (tryfind (λ (x)
                        (if (even? x)
                            x
                            (error "odd")))
                      '(1 3 5))))
(check-equal? (mapfilter (λ (x)
                           (if (even? x)
                               (* x 10)
                               (error "odd")))
                         '(1 2 3 4))
              '(20 40))
(check-equal? (repeat (λ (x)
                        (if (< x 5)
                            (add1 x)
                            (error "done")))
                      0)
              5)

;; ===== finite partial functions (hash-based) =====
(check-false (defined undefined 'a))
(check-equal? (apply (update 'a 1 undefined) 'a) 1)
(check-true (defined (update 'a 1 undefined) 'a))
(check-equal? (tryapplyd undefined 'a 99) 99)
(check-equal? (tryapplyd (update 'a 1 undefined) 'a 99) 1)
(check-equal? (tryapplyl undefined 'a) '())
(check-false (defined (undefine 'a (update 'a 1 undefined)) 'a))
(check-equal? (apply (fpf '(a b) '(1 2)) 'b) 2)
(check-equal? (sort (dom (fpf '(a b) '(1 2))) symbol<?) '(a b))
(check-equal? (length (graph (fpf '(a b) '(1 2)))) 2)
(check-equal? (apply (mapf add1 (fpf '(a) '(5))) 'a) 6)

;; ===== union-find =====
(check-false (equivalent unequal 'a 'b))
(check-equal? (canonize unequal 'a) 'a)
(let ([e (equate (cons 'a 'b) unequal)])
  (check-true (equivalent e 'a 'b))
  (check-false (equivalent e 'a 'c)))
(let ([e (equate (cons 'b 'c) (equate (cons 'a 'b) unequal))])
  (check-true (equivalent e 'a 'c)) ; transitive
  (check-true (subset '(a b c) (equated e))))

;; ===== valmod / undef (closure-based finite functions) =====
;; valmod overrides one key and delegates everything else to the base fn.
(check-equal? ((valmod 0 1 (λ (x) (+ x 100))) 0) 1) ; overridden key
(check-equal? ((valmod 0 1 (λ (x) (+ x 100))) 5) 105) ; delegates to base
(check-equal? ((valmod 'a 1 (λ (x) 'fallback)) 'a) 1)
(check-equal? ((valmod 'a 1 (λ (x) 'fallback)) 'b) 'fallback)
;; undef is the empty closure: it raises on every input.
(check-exn exn:fail? (λ () (undef 'anything)))
;; chained valmods: layered overrides, outermost wins; undef is the base.
(check-equal? ((valmod 'a 1 (valmod 'b 2 undef)) 'a) 1)
(check-equal? ((valmod 'a 1 (valmod 'b 2 undef)) 'b) 2)
(check-exn exn:fail? (λ () ((valmod 'a 1 (valmod 'b 2 undef)) 'c)))
;; order matters: the outer binding shadows an inner one for the same key.
(check-equal? ((valmod 'a 1 (valmod 'a 2 undef)) 'a) 1)

;; ===== allsets / allsubsets / allnonemptysubsets (combinatorial content) =====
;; allsets m l = the C(len,m) m-element subsets of l.
(check-equal? (length (allsets 2 '(a b c d))) 6) ; C(4,2) = 6 (not 3!)
(check-true (andmap (λ (s) (= (length s) 2)) (allsets 2 '(a b c d)))) ; each has m elems
(check-true (andmap (λ (s) (subset s '(a b c d))) (allsets 2 '(a b c d))))
(check-equal? (length (allsets 3 '(a b c d e))) 10) ; C(5,3) = 10
(check-equal? (allsets 3 '(a b)) '()) ; m > len => no subsets
;; every non-empty subset is genuinely non-empty and a subset of the input.
(check-true (andmap pair? (allnonemptysubsets '(a b c))))
(check-true (andmap (λ (s) (subset s '(a b c))) (allnonemptysubsets '(a b c))))

;; ===== image (correctness of element transformation) =====
(check-true (set-eq (image (λ (x) (* x 2)) '(1 2 3)) '(2 4 6)))

;; ===== chop-list edges =====
(check-equal? (let-values ([(a b) (chop-list 0 '(1 2 3))])
                (list a b))
              '(() (1 2 3))) ; n = 0
(check-equal? (let-values ([(a b) (chop-list 3 '(1 2 3))])
                (list a b))
              '((1 2 3) ())) ; n = length
;; splitting then appending reconstructs the original list.
(check-equal? (let-values ([(a b) (chop-list 2 '(1 2 3 4))])
                (append a b))
              '(1 2 3 4))

;; ===== insertat bounds =====
(check-equal? (insertat 3 'x '(a b c)) '(a b c x)) ; at the end
(check-exn exn:fail? (λ () (insertat 5 'x '(a b c)))) ; out of bounds

;; ===== repeat: function that raises immediately returns the seed =====
(check-equal? (repeat (λ (x) (error "fail")) 0) 0)

;; ===== union-find: longer chains and disjoint classes =====
;; chaining a-b-c-d-e merges all five into one class.
(let ([p (equate (cons 'd 'e)
                 (equate (cons 'c 'd) (equate (cons 'b 'c) (equate (cons 'a 'b) unequal))))])
  (check-true (equivalent p 'a 'b))
  (check-true (equivalent p 'a 'c))
  (check-true (equivalent p 'a 'd))
  (check-true (equivalent p 'a 'e))
  (check-true (subset '(a b c d e) (equated p))))
;; disjoint merges stay disjoint: {a,b} and {c,d,e} never connect.
(let ([p (equate (cons 'd 'e) (equate (cons 'c 'd) (equate (cons 'a 'b) unequal)))])
  (check-true (equivalent p 'a 'b))
  (check-true (equivalent p 'c 'e))
  (check-false (equivalent p 'a 'c)))
