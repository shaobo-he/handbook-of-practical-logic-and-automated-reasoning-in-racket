#lang racket/base

;; lib.fs --- general library: sets (as duplicate-free lists) and
;; finite partial functions.

(require racket/set)
(require racket/match)
(require (only-in racket/list argmin argmax filter-map))

(provide (all-defined-out))

;; ===== sets as duplicate-free lists =====
;; These keep the racket/set-based implementations so element ordering
;; is stable across the rest of the port.

(define (setify lst)
  (set->list (list->set lst)))

(define (unions sets)
  (set->list (foldl (compose set-union) (set) (map list->set sets))))

(define (union x y)
  (unions (list x y)))

(define (intersect x y)
  (set->list (set-intersect (list->set x) (list->set y))))

(define (subtract x y)
  (set->list (set-subtract (list->set x) (list->set y))))

(define (subset x y)
  (subset? (list->set x) (list->set y)))

(define (psubset x y)
  (let ([sx (list->set x)]
        [sy (list->set y)])
    (and (subset? sx sy) (not (set=? sx sy)))))

(define (set-eq x y)
  (set=? (list->set x) (list->set y)))

(define (image f s)
  (setify (map f s)))

;; allpairs f [x ...] [y ...] = list of (f x y) over all pairs
(define (allpairs f xs ys)
  (for*/list ([x (in-list xs)]
              [y (in-list ys)])
    (f x y)))

;; complement of a predicate
(define (non p)
  (λ (x) (not (p x))))

;; #t if (f x) doesn't raise
(define (can f x)
  (with-handlers ([exn:fail? (λ (e) #f)])
    (f x)
    #t))

;; apply f to x, n times
(define (funpow n f x)
  (if (<= n 0)
      x
      (funpow (- n 1) f (f x))))

;; smallest n >= start with (p n) true
(define (first n p)
  (if (p n)
      n
      (first (+ n 1) p)))

;; apply f repeatedly until it raises, returning the last good value
(define (repeat f x)
  (with-handlers ([exn:fail? (λ (e) x)])
    (repeat f (f x))))

;; closure-based finite functions (used for model interpretations)
(define (undef x)
  (error 'undef "undefined function"))
(define (valmod a y f)
  (λ (x)
    (if (equal? x a)
        y
        (f x))))

;; add an element to a set (no-op if already present)
(define (insert x s)
  (if (member x s)
      s
      (cons x s)))

;; element of l minimizing / maximizing f
(define (minimize f l)
  (argmin f l))
(define (maximize f l)
  (argmax f l))

;; first (f x) over l that doesn't raise; raises if none do (backtracking helper)
(define (tryfind f l)
  (cond
    [(null? l) (error 'tryfind "tryfind")]
    [else
     (with-handlers ([exn:fail? (λ (e) (tryfind f (cdr l)))])
       (f (car l)))]))

;; map f over l, dropping elements on which f raises
(define (mapfilter f l)
  (filter-map (λ (x)
                (with-handlers ([exn:fail? (λ (e) #f)])
                  (f x)))
              l))

;; all subsets / all non-empty subsets of a (duplicate-free) list
(define (allsubsets s)
  (if (null? s)
      (list '())
      (let ([res (allsubsets (cdr s))]) (append (map (λ (b) (cons (car s) b)) res) res))))

(define (allnonemptysubsets s)
  (filter pair? (allsubsets s)))

;; all ordered pairs (x . y) with x before y in l
(define (distinctpairs l)
  (match l
    [(cons x t) (append (map (λ (y) (cons x y)) t) (distinctpairs t))]
    ['() '()]))

;; all m-element subsets of l
(define (allsets m l)
  (cond
    [(= m 0) (list '())]
    [(null? l) '()]
    [else (union (image (λ (g) (cons (car l) g)) (allsets (- m 1) (cdr l))) (allsets m (cdr l)))]))

;; 0-based position of x in l (raises if absent)
(define (index x l)
  (let loop ([l l]
             [i 0])
    (cond
      [(null? l) (error 'index "not found")]
      [(equal? (car l) x) i]
      [else (loop (cdr l) (add1 i))])))

;; all but the last element
(define (butlast l)
  (if (null? (cdr l))
      '()
      (cons (car l) (butlast (cdr l)))))

;; insert x at position i
(define (insertat i x l)
  (cond
    [(= i 0) (cons x l)]
    [(null? l) (error 'insertat "list too short")]
    [else (cons (car l) (insertat (- i 1) x (cdr l)))]))

;; split l into its first n elements and the rest (two values)
(define (chop-list n l)
  (if (= n 0)
      (values '() l)
      (let-values ([(a b) (chop-list (sub1 n) (cdr l))])
        (values (cons (car l) a) b))))

;; ===== finite partial functions =====
;; Represented as immutable hash tables, so the domain is enumerable
;; (needed by unification, resolution, etc.). `undefined` is the empty
;; map; `update`/`undefine` return updated copies.

(define undefined (hash))

(define (update k v f)
  (hash-set f k v))
(define (undefine k f)
  (hash-remove f k))

(define (apply f k)
  (hash-ref f k (λ () (error 'apply "argument not in domain: ~s" k))))

(define (tryapplyd f k d)
  (hash-ref f k d))
(define (tryapplyl f k)
  (tryapplyd f k '()))
(define (defined f k)
  (hash-has-key? f k))

;; build a partial function from parallel key/value lists
(define (fpf keys vals)
  (make-immutable-hash (map cons keys vals)))

;; enumeration / transformation
(define (dom f)
  (hash-keys f))
(define (graph f)
  (hash->list f))
(define (mapf g f)
  (for/hash ([(k v) (in-hash f)])
    (values k (g v))))

;; does x occur before y in list l?
(define (earlier l x y)
  (match l
    ['() #f]
    [(cons h t) (and (not (equal? h y)) (or (equal? h x) (earlier t x y)))]))

;; ===== union-find ("partition") =====
;; A partition is a hash mapping each element to either
;;   (cons 'nonterminal b)   -- follow b
;;   (list 'terminal p size) -- p is the canonical representative
(define unequal (hash))

(define (terminus ptn a)
  (match (apply ptn a)
    [(cons 'nonterminal b) (terminus ptn b)]
    [(list 'terminal p q) (cons p q)]))

(define (tryterminus ptn a)
  (with-handlers ([exn:fail? (λ (e) (cons a 1))])
    (terminus ptn a)))

(define (canonize ptn a)
  (car (tryterminus ptn a)))

(define (equivalent eqv a b)
  (equal? (canonize eqv a) (canonize eqv b)))

(define (equate ab ptn)
  (define a (car ab))
  (define b (cdr ab))
  (define ta (tryterminus ptn a))
  (define tb (tryterminus ptn b))
  (define a* (car ta))
  (define na (cdr ta))
  (define b* (car tb))
  (define nb (cdr tb))
  (cond
    [(equal? a* b*) ptn]
    [(<= na nb) (update a* (cons 'nonterminal b*) (update b* (list 'terminal b* (+ na nb)) ptn))]
    [else (update b* (cons 'nonterminal a*) (update a* (list 'terminal a* (+ na nb)) ptn))]))

(define (equated ptn)
  (dom ptn))
