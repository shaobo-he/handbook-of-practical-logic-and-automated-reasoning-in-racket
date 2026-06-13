#lang racket/base

;; stal --- a simple implementation of Stalmarck's algorithm.
;; (NB the real method is patented for commercial use; this is a toy.)

(require racket/match)
(require (only-in "../core/lib.rkt"
                  undefined
                  update
                  tryapplyl
                  insert
                  allpairs
                  setify
                  union
                  subtract
                  intersect
                  apply
                  graph
                  unions
                  unequal
                  equate
                  canonize
                  equated
                  fpf))
(require (only-in "../core/formulas.rkt" overatoms))
(require (only-in "prop.rkt" nenf psimplify atoms tautology negative positive negate psubst))
(require (only-in "defcnf.rkt" maincnf var-index))

(provide (all-defined-out))

(define stal-verbose (make-parameter #f))

;; an arbitrary but total order on positive literals (#t or (atom sym))
(define (prop-atom<? a b)
  (cond
    [(equal? a b) #f]
    [(eq? a #t) #t]
    [(eq? b #t) #f]
    [else (symbol<? (cadr a) (cadr b))]))

;; ===== triplet transformation (reuse the definitional-CNF machinery) =====
(define (triplicate fm)
  (define fm* (nenf fm))
  (define counter (box (add1 (overatoms (λ (a acc) (max acc (var-index "p_" a))) fm* 0))))
  (define defs (make-hash))
  (define p (maincnf fm* defs counter))
  (values p (map cdr (hash-values defs))))

;; ===== trigger generation =====
(define (lit-atom lit)
  (if (negative lit)
      (negate lit)
      lit))

(define (align pq)
  (define p (car pq))
  (define q (cdr pq))
  (cond
    [(prop-atom<? (lit-atom p) (lit-atom q)) (align (cons q p))]
    [(negative p) (cons (negate p) (negate q))]
    [else (cons p q)]))

(define (equate2 pq eqv)
  (equate (cons (negate (car pq)) (negate (cdr pq))) (equate pq eqv)))

(define (irredundant rel eqs)
  (match eqs
    ['() '()]
    [`(,pq . ,oth)
     (if (equal? (canonize rel (car pq)) (canonize rel (cdr pq)))
         (irredundant rel oth)
         (insert pq (irredundant (equate2 pq rel) oth)))]))

(define (consequences peq fm eqs)
  (define p (car peq))
  (define q (cdr peq))
  (define (follows rs)
    (tautology `(imp (and (iff ,p ,q) ,fm) (iff ,(car rs) ,(cdr rs)))))
  (irredundant (equate2 peq unequal) (filter follows eqs)))

(define (triggers fm)
  (define poslits (insert #t (map (λ (p) `(atom ,p)) (atoms fm))))
  (define lits (union poslits (map negate poslits)))
  (define pairs (allpairs cons lits lits))
  (define npairs (filter (λ (pq) (not (equal? (lit-atom (car pq)) (lit-atom (cdr pq))))) pairs))
  (define eqs (setify (map align npairs)))
  (define raw (map (λ (p) (cons p (consequences p fm eqs))) eqs))
  (filter (λ (pc) (not (null? (cdr pc)))) raw))

;; ===== precomputed triggers for the four standard triplets =====
(define trig-and (triggers '(iff (atom p) (and (atom q) (atom r)))))
(define trig-or (triggers '(iff (atom p) (or (atom q) (atom r)))))
(define trig-imp (triggers '(iff (atom p) (imp (atom q) (atom r)))))
(define trig-iff (triggers '(iff (atom p) (iff (atom q) (atom r)))))

(define (ddnegate fm)
  (match fm
    [`(not (not ,p)) p]
    [_ fm]))

(define (inst-fn xyz)
  (define subfn (fpf '(p q r) xyz))
  (λ (fm) (ddnegate (psubst subfn fm))))

(define (inst2-fn i pq)
  (align (cons ((inst-fn i) (car pq)) ((inst-fn i) (cdr pq)))))
(define (instn-fn i ac)
  (cons (inst2-fn i (car ac)) (map (λ (c) (inst2-fn i c)) (cdr ac))))
(define (inst-trigger xyz trig)
  (map (λ (ac) (instn-fn xyz ac)) trig))

(define (trigger fm)
  (match fm
    [`(iff ,x (and ,y ,z)) (inst-trigger (list x y z) trig-and)]
    [`(iff ,x (or ,y ,z)) (inst-trigger (list x y z) trig-or)]
    [`(iff ,x (imp ,y ,z)) (inst-trigger (list x y z) trig-imp)]
    [`(iff ,x (iff ,y ,z)) (inst-trigger (list x y z) trig-iff)]
    [_ (error 'trigger "How did we get here?")]))

;; ===== relevance: literal -> triggers mentioning it =====
(define (relevance trigs)
  (define (insert-relevant p trg f)
    (update p (insert trg (tryapplyl f p)) f))
  (define (insert-relevant2 trg f)
    (define pq (car trg))
    (insert-relevant (car pq) trg (insert-relevant (cdr pq) trg f)))
  (foldr insert-relevant2 undefined trigs))

;; ===== merging equivalence classes + relevancies (erf = (eqv . rfn)) =====
(define (equatecons pq erf)
  (define p0 (car pq))
  (define q0 (cdr pq))
  (define eqv (car erf))
  (define rfn (cdr erf))
  (define p (canonize eqv p0))
  (define q (canonize eqv q0))
  (if (equal? p q)
      (cons '() erf)
      (let ()
        (define p* (canonize eqv (negate p0)))
        (define q* (canonize eqv (negate q0)))
        (define eqv* (equate2 (cons p q) eqv))
        (define sp-pos (tryapplyl rfn p))
        (define sp-neg (tryapplyl rfn p*))
        (define sq-pos (tryapplyl rfn q))
        (define sq-neg (tryapplyl rfn q*))
        (define rfn*
          (update (canonize eqv* p)
                  (union sp-pos sq-pos)
                  (update (canonize eqv* p*) (union sp-neg sq-neg) rfn)))
        (define nw (union (intersect sp-pos sq-pos) (intersect sp-neg sq-neg)))
        (cons (foldr (λ (x acc) (union (cdr x) acc)) '() nw) (cons eqv* rfn*)))))

(define (zero-saturate erf assigs)
  (match assigs
    ['() erf]
    [`(,pq . ,ts)
     (define ne (equatecons pq erf))
     (zero-saturate (cdr ne) (union ts (car ne)))]))

(define (zero-saturate-and-check erf trigs)
  (define erf* (zero-saturate erf trigs))
  (define eqv* (car erf*))
  (define vars (filter positive (equated eqv*)))
  (if (ormap (λ (x) (equal? (canonize eqv* x) (canonize eqv* `(not ,x)))) vars)
      (cdr (equatecons (cons #t '(not #t)) erf*))
      erf*))

(define (truefalse pfn)
  (equal? (canonize pfn '(not #t)) (canonize pfn #t)))

(define (equateset s0 eqfn)
  (match s0
    [`(,a . ,(and s1 (cons b s2))) (equateset s1 (cdr (equatecons (cons a b) eqfn)))]
    [_ eqfn]))

(define (inter els erf1 erf2 rev1 rev2 erf)
  (match els
    ['() erf]
    [`(,x . ,xs)
     (define b1 (canonize (car erf1) x))
     (define b2 (canonize (car erf2) x))
     (define s1 (apply rev1 b1))
     (define s2 (apply rev2 b2))
     (define s (intersect s1 s2))
     (inter (subtract xs s) erf1 erf2 rev1 rev2 (equateset s erf))]))

(define (reverseq domain eqv)
  (define al (map (λ (x) (cons x (canonize eqv x))) domain))
  (foldr (λ (yx f) (update (cdr yx) (insert (car yx) (tryapplyl f (cdr yx))) f)) undefined al))

(define (stal-intersect erf1 erf2 erf)
  (cond
    [(truefalse (car erf1)) erf2]
    [(truefalse (car erf2)) erf1]
    [else
     (define dom1 (equated (car erf1)))
     (define dom2 (equated (car erf2)))
     (define comdom (intersect dom1 dom2))
     (inter comdom erf1 erf2 (reverseq dom1 (car erf1)) (reverseq dom2 (car erf2)) erf)]))

;; ===== n-saturation =====
(define (saturate n erf assigs allvars)
  (define erf* (zero-saturate-and-check erf assigs))
  (define eqv* (car erf*))
  (if (or (= n 0) (truefalse eqv*))
      erf*
      (let ()
        (define erf** (splits n erf* allvars allvars))
        (if (equal? (car erf**) eqv*)
            erf**
            (saturate n erf** '() allvars)))))

(define (splits n erf allvars vars)
  (define eqv (car erf))
  (match vars
    ['() erf]
    [`(,p . ,ovars)
     (if (not (equal? (canonize eqv p) p))
         (splits n erf allvars ovars)
         (let ()
           (define erf0 (saturate (- n 1) erf (list (cons p '(not #t))) allvars))
           (define erf1 (saturate (- n 1) erf (list (cons p #t)) allvars))
           (define erf* (stal-intersect erf0 erf1 erf))
           (if (truefalse (car erf*))
               erf*
               (splits n erf* allvars ovars))))]))

(define (saturate-upto vars n m trigs assigs)
  (cond
    [(> n m) (error 'stalmarck "Not ~a-easy" m)]
    [else
     (let ()
       (when (stal-verbose)
         (printf "*** Starting ~a-saturation\n" n))
       (define eqv (car (saturate n (cons unequal (relevance trigs)) assigs vars)))
       (or (truefalse eqv) (saturate-upto vars (+ n 1) m trigs assigs)))]))

(define (stalmarck fm)
  (define (include-trig ec f)
    (update (car ec) (union (cdr ec) (tryapplyl f (car ec))) f))
  (define fm* (psimplify `(not ,fm)))
  (cond
    [(equal? fm* #f) #t]
    [(equal? fm* #t) #f]
    [else
     (define-values (p triplets) (triplicate fm*))
     (define trigfn (foldr (λ (trip f) (foldr include-trig f (trigger trip))) undefined triplets))
     (define vars (map (λ (p) `(atom ,p)) (unions (map atoms triplets))))
     (saturate-upto vars 0 2 (graph trigfn) (list (cons p #t)))]))
