#lang racket/base

;; bdd --- binary decision diagrams with complement edges, and BDD-based
;; tautology checking (plain and with shared definitions).
;;
;; A BDD bundles a unique table (node -> id), an expand table (id -> node),
;; the next free id, and a variable ordering. Nodes are (s l r); ids are
;; ints, with negation encoding complement edges and +/-1 the constants.

(require racket/match)
(require (only-in racket/list partition))
(require (only-in "../core/lib.rkt" undefined update apply tryapplyd subtract can))
(require (only-in "../core/formulas.rkt" conjuncts dest-imp))
(require (only-in "prop.rkt" atoms))

(provide (all-defined-out))

(struct bdd (unique expand n ord) #:transparent)

(define empty-prop (string->symbol ""))

(define (print-bdd b)
  (printf "<BDD with ~a nodes>" (bdd-n b)))

(define (expand-node b n)
  (if (>= n 0)
      (tryapplyd (bdd-expand b) n (list empty-prop 1 1))
      (match (tryapplyd (bdd-expand b) (- n) (list empty-prop 1 1))
        [`(,p ,l ,r) (list p (- l) (- r))])))

(define (lookup-unique b node)
  (with-handlers ([exn:fail? (λ (e)
                               (define m (bdd-n b))
                               (values (bdd (update node m (bdd-unique b))
                                            (update m node (bdd-expand b))
                                            (+ m 1)
                                            (bdd-ord b))
                                       m))])
    (values b (apply (bdd-unique b) node))))

(define (mk-node b slr)
  (match-define `(,s ,l ,r) slr)
  (cond
    [(= l r) (values b l)]
    [(>= l 0) (lookup-unique b (list s l r))]
    [else
     (let-values ([(b* m) (lookup-unique b (list s (- l) (- r)))])
       (values b* (- m)))]))

(define (mk-bdd ord)
  (bdd undefined undefined 2 ord))

(define (bdd-order b p1 p2)
  (or (and (equal? p2 empty-prop) (not (equal? p1 empty-prop))) ((bdd-ord b) p1 p2)))

;; thread state s through f1 then f2, then combine with g
;; f1x1 / f2x2 are (fn . arg); each fn takes (state arg) and returns (values state result)
(define (thread s g f1x1 f2x2)
  (let-values ([(s* y1) ((car f1x1) s (cdr f1x1))])
    (let-values ([(s** y2) ((car f2x2) s* (cdr f2x2))])
      (g s** (cons y1 y2)))))

;; bddcomp is (bdd . computed-table); m1m2 is (m1 . m2)
(define (bdd-and bddcomp m1m2)
  (define m1 (car m1m2))
  (define m2 (cdr m1m2))
  (define b (car bddcomp))
  (define comp (cdr bddcomp))
  (cond
    [(or (= m1 -1) (= m2 -1)) (values bddcomp -1)]
    [(= m1 1) (values bddcomp m2)]
    [(= m2 1) (values bddcomp m1)]
    [else
     (define cached (or (tryapplyd comp (cons m1 m2) #f) (tryapplyd comp (cons m2 m1) #f)))
     (if cached
         (values bddcomp cached)
         (let ()
           (match-define `(,p1 ,l1 ,r1) (expand-node b m1))
           (match-define `(,p2 ,l2 ,r2) (expand-node b m2))
           (define-values (p lpair rpair)
             (cond
               [(equal? p1 p2) (values p1 (cons l1 l2) (cons r1 r2))]
               [(bdd-order b p1 p2) (values p1 (cons l1 m2) (cons r1 m2))]
               [else (values p2 (cons m1 l2) (cons m1 r2))]))
           (define-values (bc* lr)
             (thread bddcomp (λ (s z) (values s z)) (cons bdd-and lpair) (cons bdd-and rpair)))
           (define b* (car bc*))
           (define comp* (cdr bc*))
           (let-values ([(b** m) (mk-node b* (list p (car lr) (cdr lr)))])
             (values (cons b** (update (cons m1 m2) m comp*)) m))))]))

(define (bdd-or bdc m1m2)
  (let-values ([(bdc1 m) (bdd-and bdc (cons (- (car m1m2)) (- (cdr m1m2))))])
    (values bdc1 (- m))))

(define (bdd-imp bdc m1m2)
  (bdd-or bdc (cons (- (car m1m2)) (cdr m1m2))))

(define (bdd-iff bdc m1m2)
  (thread bdc
          bdd-or
          (cons bdd-and (cons (car m1m2) (cdr m1m2)))
          (cons bdd-and (cons (- (car m1m2)) (- (cdr m1m2))))))

;; ===== formula -> BDD =====
(define (mkbdd bddcomp fm)
  (match fm
    [#f (values bddcomp -1)]
    [#t (values bddcomp 1)]
    [`(atom ,s)
     (let-values ([(b* m) (mk-node (car bddcomp) (list s 1 -1))])
       (values (cons b* (cdr bddcomp)) m))]
    [`(not ,p)
     (let-values ([(bc* m) (mkbdd bddcomp p)])
       (values bc* (- m)))]
    [`(and ,p ,q) (thread bddcomp bdd-and (cons mkbdd p) (cons mkbdd q))]
    [`(or ,p ,q) (thread bddcomp bdd-or (cons mkbdd p) (cons mkbdd q))]
    [`(imp ,p ,q) (thread bddcomp bdd-imp (cons mkbdd p) (cons mkbdd q))]
    [`(iff ,p ,q) (thread bddcomp bdd-iff (cons mkbdd p) (cons mkbdd q))]))

(define (bddtaut fm)
  (let-values ([(_ m) (mkbdd (cons (mk-bdd symbol<?) undefined) fm)])
    (= m 1)))

;; ===== exploiting shared definitions =====
(define (dest-nimp fm)
  (match fm
    [`(not ,p) (cons p #f)]
    [_ (dest-imp fm)]))

(define (dest-iffdef fm)
  (match fm
    [`(iff (atom ,x) ,r) (cons x r)]
    [`(iff ,r (atom ,x)) (cons x r)]
    [_ (error 'dest-iffdef "not a defining equivalence")]))

(define (restore-iffdef xe fm)
  `(imp (iff (atom ,(car xe)) ,(cdr xe)) ,fm))

(define (suitable-iffdef defs xq)
  (define fvs (atoms (cdr xq)))
  (not (ormap (λ (xe) (and (member (car xe) fvs) #t)) defs)))

(define (sort-defs acc defs fm)
  (with-handlers ([exn:fail? (λ (e) (values (reverse acc) (foldr restore-iffdef fm defs)))])
    (define xe (or (findf (λ (d) (suitable-iffdef defs d)) defs) (error 'sort-defs "find")))
    (define x (car xe))
    (define-values (ps nonps) (partition (λ (xe2) (equal? (car xe2) x)) defs))
    (define ps* (subtract ps (list xe)))
    (sort-defs (cons xe acc) nonps (foldr restore-iffdef fm ps*))))

(define (mkbdde sfn bddcomp fm)
  (match fm
    [#f (values bddcomp -1)]
    [#t (values bddcomp 1)]
    [`(atom ,s)
     (define cached (tryapplyd sfn s #f))
     (if cached
         (values bddcomp cached)
         (let-values ([(b* m) (mk-node (car bddcomp) (list s 1 -1))])
           (values (cons b* (cdr bddcomp)) m)))]
    [`(not ,p)
     (let-values ([(bc* m) (mkbdde sfn bddcomp p)])
       (values bc* (- m)))]
    [`(and ,p ,q)
     (thread bddcomp bdd-and (cons (λ (s x) (mkbdde sfn s x)) p) (cons (λ (s x) (mkbdde sfn s x)) q))]
    [`(or ,p ,q)
     (thread bddcomp bdd-or (cons (λ (s x) (mkbdde sfn s x)) p) (cons (λ (s x) (mkbdde sfn s x)) q))]
    [`(imp ,p ,q)
     (thread bddcomp bdd-imp (cons (λ (s x) (mkbdde sfn s x)) p) (cons (λ (s x) (mkbdde sfn s x)) q))]
    [`(iff ,p ,q)
     (thread bddcomp
             bdd-iff
             (cons (λ (s x) (mkbdde sfn s x)) p)
             (cons (λ (s x) (mkbdde sfn s x)) q))]))

(define (mkbdds sfn bddcomp defs fm)
  (match defs
    ['() (mkbdde sfn bddcomp fm)]
    [`(,pe . ,odefs)
     (let-values ([(bc* b) (mkbdde sfn bddcomp (cdr pe))])
       (mkbdds (update (car pe) b sfn) bc* odefs fm))]))

(define (ebddtaut fm)
  (define-values (l r)
    (with-handlers ([exn:fail? (λ (e) (values #t fm))])
      (let ([lr (dest-nimp fm)]) (values (car lr) (cdr lr)))))
  (define-values (eqs noneqs) (partition (λ (f) (can dest-iffdef f)) (conjuncts l)))
  (define-values (defs fm*)
    (sort-defs '() (map dest-iffdef eqs) (foldr (λ (n acc) `(imp ,n ,acc)) r noneqs)))
  (let-values ([(_ m) (mkbdds undefined (cons (mk-bdd symbol<?) undefined) defs fm*)])
    (= m 1)))
