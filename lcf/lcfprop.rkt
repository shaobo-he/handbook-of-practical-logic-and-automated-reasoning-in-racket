#lang racket/base

;; lcfprop.fs --- derived propositional inference rules on top of the LCF
;; kernel, culminating in an LCF-style tableau tautology prover (lcftaut).

(require racket/match)
(require (only-in "../core/lib.rkt" funpow chop-list index))
(require (only-in "../core/formulas.rkt" dest-imp dest-iff dest-and antecedent consequent mk-imp))
(require "lcf.rkt")

(provide (all-defined-out))

;; |- p ==> p
(define (imp-refl p)
  (modusponens (modusponens (axiom-distribimp p `(imp ,p ,p) p) (axiom-addimp p `(imp ,p ,p)))
               (axiom-addimp p p)))

(define (imp-unduplicate th)
  (match-define (cons p pq) (dest-imp (concl th)))
  (define q (consequent pq))
  (modusponens (modusponens (axiom-distribimp p p q) th) (imp-refl p)))

(define (negatef fm)
  (match fm
    [`(imp ,p #f) p]
    [p `(imp ,p #f)]))
(define (negativef fm)
  (match fm
    [`(imp ,p #f) #t]
    [_ #f]))

(define (add-assum p th)
  (modusponens (axiom-addimp (concl th) p) th))

(define (imp-add-assum p th)
  (match-define (cons q r) (dest-imp (concl th)))
  (modusponens (axiom-distribimp p q r) (add-assum p th)))

(define (imp-trans th1 th2)
  (modusponens (imp-add-assum (antecedent (concl th1)) th2) th1))

(define (imp-insert q th)
  (match-define (cons p r) (dest-imp (concl th)))
  (imp-trans th (axiom-addimp r q)))

(define (imp-swap th)
  (match-define (cons p qr) (dest-imp (concl th)))
  (match-define (cons q r) (dest-imp qr))
  (imp-trans (axiom-addimp q p) (modusponens (axiom-distribimp p q r) th)))

(define (imp-trans-th p q r)
  (imp-trans (axiom-addimp `(imp ,q ,r) p) (axiom-distribimp p q r)))

(define (imp-add-concl r th)
  (match-define (cons p q) (dest-imp (concl th)))
  (modusponens (imp-swap (imp-trans-th p q r)) th))

(define (imp-swap-th p q r)
  (imp-trans (axiom-distribimp p q r) (imp-add-concl `(imp ,p ,r) (axiom-addimp q p))))

(define (imp-swap2 th)
  (match (concl th)
    [`(imp (imp ,p (imp ,q ,r)) (imp ,s (imp ,t ,u)))
     (imp-trans (imp-swap-th q p r) (imp-trans th (imp-swap-th s t u)))]
    [_ (error 'imp-swap2 "imp_swap2")]))

(define (right-mp ith th)
  (imp-unduplicate (imp-trans th (imp-swap ith))))

(define (iff-imp1 th)
  (match-define (cons p q) (dest-iff (concl th)))
  (modusponens (axiom-iffimp1 p q) th))

(define (iff-imp2 th)
  (match-define (cons p q) (dest-iff (concl th)))
  (modusponens (axiom-iffimp2 p q) th))

(define (imp-antisym th1 th2)
  (match-define (cons p q) (dest-imp (concl th1)))
  (modusponens (modusponens (axiom-impiff p q) th1) th2))

(define (right-doubleneg th)
  (match (concl th)
    [`(imp ,_ (imp (imp ,p #f) #f)) (imp-trans th (axiom-doubleneg p))]
    [_ (error 'right-doubleneg "right_doubleneg")]))

(define (ex-falso p)
  (right-doubleneg (axiom-addimp #f `(imp ,p #f))))

(define (imp-trans2 th1 th2)
  (match-define `(imp ,p (imp ,q ,r)) (concl th1))
  (match-define `(imp ,r2 ,s) (concl th2))
  (modusponens (imp-add-assum p (modusponens (imp-trans-th q r s) th2)) th1))

(define (imp-trans-chain ths th)
  (foldr (λ (a b) (imp-unduplicate (imp-trans a (imp-swap b))))
         (imp-trans (car ths) th)
         (reverse (cdr ths))))

(define (imp-truefalse p q)
  (imp-trans (imp-trans-th p q #f) (imp-swap-th `(imp ,p ,q) p #f)))

(define (imp-mono-th p p2 q q2)
  (define th1 (imp-trans-th `(imp ,p ,q) `(imp ,p2 ,q) `(imp ,p2 ,q2)))
  (define th2 (imp-trans-th p2 q q2))
  (define th3 (imp-swap (imp-trans-th p2 p q)))
  (imp-trans th3 (imp-swap (imp-trans th2 th1))))

(define truth (modusponens (iff-imp2 axiom-true) (imp-refl #f)))

(define (contrapos th)
  (match-define (cons p q) (dest-imp (concl th)))
  (imp-trans (imp-trans (iff-imp1 (axiom-not q)) (imp-add-concl #f th)) (iff-imp2 (axiom-not p))))

(define (and-left p q)
  (define th1 (imp-add-assum p (axiom-addimp #f q)))
  (define th2 (right-doubleneg (imp-add-concl #f th1)))
  (imp-trans (iff-imp1 (axiom-and p q)) th2))

(define (and-right p q)
  (define th1 (axiom-addimp `(imp ,q #f) p))
  (define th2 (right-doubleneg (imp-add-concl #f th1)))
  (imp-trans (iff-imp1 (axiom-and p q)) th2))

(define (conjths fm)
  (with-handlers ([exn:fail? (λ (e) (list (imp-refl fm)))])
    (match-define (cons p q) (dest-and fm))
    (cons (and-left p q) (map (λ (t) (imp-trans (and-right p q) t)) (conjths q)))))

(define (and-pair p q)
  (define th1 (iff-imp2 (axiom-and p q)))
  (define th2 (imp-swap-th `(imp ,p (imp ,q #f)) q #f))
  (define th3 (imp-add-assum p (imp-trans2 th2 th1)))
  (modusponens th3 (imp-swap (imp-refl `(imp ,p (imp ,q #f))))))

(define (shunt th)
  (match-define (cons p q) (dest-and (antecedent (concl th))))
  (modusponens (foldr imp-add-assum th (list p q)) (and-pair p q)))

(define (unshunt th)
  (match-define (cons p qr) (dest-imp (concl th)))
  (match-define (cons q r) (dest-imp qr))
  (imp-trans-chain (list (and-left p q) (and-right p q)) th))

(define (iff-def p q)
  (define th (and-pair `(imp ,p ,q) `(imp ,q ,p)))
  (define thl (list (axiom-iffimp1 p q) (axiom-iffimp2 p q)))
  (imp-antisym (imp-trans-chain thl th) (unshunt (axiom-impiff p q))))

(define (expand-connective fm)
  (match fm
    [#t axiom-true]
    [`(not ,p) (axiom-not p)]
    [`(and ,p ,q) (axiom-and p q)]
    [`(or ,p ,q) (axiom-or p q)]
    [`(iff ,p ,q) (iff-def p q)]
    [`(exists ,x ,p) (axiom-exists x p)]
    [_ (error 'expand-connective "expand_connective")]))

(define (eliminate-connective fm)
  (if (negativef fm)
      (imp-add-concl #f (iff-imp2 (expand-connective (negatef fm))))
      (iff-imp1 (expand-connective fm))))

(define (imp-false-conseqs p q)
  (list (right-doubleneg (imp-add-concl #f (imp-add-assum p (ex-falso q))))
        (imp-add-concl #f (imp-insert p (imp-refl q)))))

(define (imp-false-rule th)
  (match-define (cons p r) (dest-imp (concl th)))
  (imp-trans-chain (imp-false-conseqs p (funpow 2 antecedent r)) th))

(define (imp-true-rule th1 th2)
  (define p (funpow 2 antecedent (concl th1)))
  (define q (antecedent (concl th2)))
  (define th3 (right-doubleneg (imp-add-concl #f th1)))
  (define th4 (imp-add-concl #f th2))
  (define th5 (imp-swap (imp-truefalse p q)))
  (define th6 (imp-add-concl #f (imp-trans-chain (list th3 th4) th5)))
  (define th7 (imp-swap (imp-refl `(imp (imp ,p ,q) #f))))
  (right-doubleneg (imp-trans th7 th6)))

(define (imp-contr p q)
  (if (negativef p)
      (imp-add-assum (negatef p) (ex-falso q))
      (imp-swap (imp-add-assum p (ex-falso q)))))

(define (imp-front-th n fm)
  (if (= n 0)
      (imp-refl fm)
      (let ()
        (match-define (cons p qr) (dest-imp fm))
        (define th1 (imp-add-assum p (imp-front-th (- n 1) qr)))
        (match-define (cons q2 r2) (dest-imp (funpow 2 consequent (concl th1))))
        (imp-trans th1 (imp-swap-th p q2 r2)))))

(define (imp-front n th)
  (modusponens (imp-front-th n (concl th)) th))

;; ===== propositional tableau prover =====
(define (literal? p)
  (match p
    [`(atom ,_) #t]
    [`(forall ,_ ,_) #t]
    [`(imp (atom ,_) #f) #t]
    [`(imp (forall ,_ ,_) #f) #t]
    [_ #f]))

(define (lcfptab fms lits)
  (match fms
    [(cons #f fl) (ex-falso (foldr mk-imp #f (append fl lits)))]
    [(cons (and fm `(imp ,p ,q)) fl)
     #:when (equal? p q)
     (add-assum fm (lcfptab fl lits))]
    [(cons `(imp (imp ,p ,q) #f) fl) (imp-false-rule (lcfptab (cons p (cons `(imp ,q #f) fl)) lits))]
    [(cons `(imp ,p ,q) fl)
     #:when (not (equal? q #f))
     (imp-true-rule (lcfptab (cons `(imp ,p #f) fl) lits) (lcfptab (cons q fl) lits))]
    [(cons p fl)
     #:when (literal? p)
     (if (member (negatef p) lits)
         (let ()
           (define-values (l1 l2) (chop-list (index (negatef p) lits) lits))
           (define th (imp-contr p (foldr mk-imp #f (cdr l2))))
           (foldr imp-insert th (append fl l1)))
         (imp-front (length fl) (lcfptab fl (cons p lits))))]
    [(cons fm fl)
     (define th (eliminate-connective fm))
     (imp-trans th (lcfptab (cons (consequent (concl th)) fl) lits))]
    ['() (error 'lcfptab "no contradiction")]))

(define (lcftaut p)
  (modusponens (axiom-doubleneg p) (lcfptab (list (negatef p)) '())))
