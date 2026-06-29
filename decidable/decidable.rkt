#lang racket/base

;; decidable --- decidable subsets of first-order logic: the AE fragment
;; (aedecide / Wang), finite-model decision, the finite-model property, and
;; the monadic fragment. Plus Aristotelean syllogisms.

(require racket/match)
(require (only-in racket/list partition range))
(require (only-in "../core/lib.rkt" fpf image unions subtract allpairs funpow undef valmod undefined))
(require (only-in "../core/formulas.rkt" list-conj list-disj mk-and mk-imp))
(require (only-in "../prop/prop.rkt" simpcnf simpdnf purednf))
(require (only-in "../fol/fol.rkt" fv functions generalize holds subst))
(require (only-in "../fol/skolem.rkt" skolemize askolemize simplify nnf specialize pnf))
(require (only-in "../fol/herbrand.rkt" groundtuples))
(require (only-in "../prop/dp.rkt" dpll))
(require (only-in "../equality/equal.rkt" predicates))
(require (only-in "../fol/meson.rkt" contrapositives mexpand002))

(provide (all-defined-out))

;; ===== AE-fragment decision by forming all ground instances =====
(define (aedecide fm)
  (define sfm (skolemize `(not ,fm)))
  (define fvs (fv sfm))
  (define-values (cnsts funcs) (partition (λ (fa) (= (cdr fa) 0)) (functions sfm)))
  ;; Genuine (arity > 0) function symbols take us outside the AE fragment: the
  ;; Herbrand universe is then infinite, so enumerating ground instances no
  ;; longer terminates as a decision procedure. Reject rather than loop.
  (if (not (null? funcs))
      (error 'aedecide "Not decidable")
      (let ()
        (define consts
          (if (null? cnsts)
              (list (cons 'c 0))
              cnsts))
        (define cntms (map (λ (c) `(fn ,(car c))) consts))
        (define alltups (groundtuples cntms '() 0 (length fvs)))
        (define cjs (simpcnf sfm))
        (define grounds
          (map (λ (tup) (image (λ (cl) (image (λ (lit) (subst (fpf fvs tup) lit)) cl)) cjs)) alltups))
        (not (dpll (unions grounds))))))

;; ===== miniscoping =====
(define (separate x cjs)
  (define-values (yes no) (partition (λ (c) (member x (fv c))) cjs))
  (cond
    [(null? yes) (list-conj no)]
    [(null? no) `(exists ,x ,(list-conj yes))]
    [else `(and (exists ,x ,(list-conj yes)) ,(list-conj no))]))

;; Push (exists x) inward as far as possible. Putting the body in DNF lets the
;; existential distribute over the disjuncts; `separate` then moves it past every
;; conjunct of a disjunct that does not mention x.
(define (pushquant x p)
  (if (not (member x (fv p)))
      p
      (list-disj (map (λ (djs) (separate x djs)) (purednf (nnf p))))))

(define (miniscope fm)
  (match fm
    [`(not ,p) `(not ,(miniscope p))]
    [`(and ,p ,q) `(and ,(miniscope p) ,(miniscope q))]
    [`(or ,p ,q) `(or ,(miniscope p) ,(miniscope q))]
    [`(forall ,x ,p) `(not ,(pushquant x `(not ,(miniscope p))))]
    [`(exists ,x ,p) (pushquant x (miniscope p))]
    [_ fm]))

(define (wang fm)
  (aedecide (miniscope (nnf (simplify fm)))))

;; ===== Aristotelean syllogisms =====
(define (mk-pred-atom p x)
  `(atom (rel ,p (var ,x))))
(define (premiss-A pq)
  `(forall x (imp ,(mk-pred-atom (car pq) 'x) ,(mk-pred-atom (cdr pq) 'x))))
(define (premiss-E pq)
  `(forall x (imp ,(mk-pred-atom (car pq) 'x) (not ,(mk-pred-atom (cdr pq) 'x)))))
(define (premiss-I pq)
  `(exists x (and ,(mk-pred-atom (car pq) 'x) ,(mk-pred-atom (cdr pq) 'x))))
(define (premiss-O pq)
  `(exists x (and ,(mk-pred-atom (car pq) 'x) (not ,(mk-pred-atom (cdr pq) 'x)))))

(define all-possible-syllogisms
  (let ()
    (define sylltypes (list premiss-A premiss-E premiss-I premiss-O))
    (define prems1 (allpairs (λ (f x) (f x)) sylltypes '((M . P) (P . M))))
    (define prems2 (allpairs (λ (f x) (f x)) sylltypes '((S . M) (M . S))))
    (define prems3 (allpairs (λ (f x) (f x)) sylltypes '((S . P))))
    (allpairs mk-imp (allpairs mk-and prems1 prems2) prems3)))

(define all-possible-syllogisms-nonempty
  (let ([p '(and (exists x (atom (rel P (var x))))
                 (and (exists x (atom (rel M (var x)))) (exists x (atom (rel S (var x))))))])
    (map (λ (t) `(imp ,p ,t)) all-possible-syllogisms)))

;; ===== finite-model decision =====
(define (alltuples n l)
  (if (= n 0)
      (list '())
      (allpairs cons l (alltuples (- n 1) l))))

(define (allmappings dom ran)
  (foldr (λ (p acc) (allpairs (λ (y f) (valmod p y f)) ran acc)) (list undef) dom))

(define (alldepmappings dom ran)
  (foldr (λ (pn acc) (allpairs (λ (y f) (valmod (car pn) y f)) (ran (cdr pn)) acc)) (list undef) dom))

(define (allfunctions dom n)
  (allmappings (alltuples n dom) dom))
(define (allpredicates dom n)
  (allmappings (alltuples n dom) '(#f #t)))

(define (decide-finite n fm)
  (define dom (range 1 (add1 n)))
  (define fints (alldepmappings (functions fm) (λ (k) (allfunctions dom k))))
  (define pints (alldepmappings (predicates fm) (λ (k) (allpredicates dom k))))
  (define interps (allpairs (λ (f p) (list dom f p)) fints pints))
  (define fm* (generalize fm))
  ;; An interpretation md is (domain fun-interp pred-interp). The interp maps a
  ;; symbol to its denotation (itself a function of the argument tuple), so we
  ;; apply twice: first the symbol, then its argument tuple.
  (andmap (λ (md)
            (holds (car md)
                   (λ (fsym args) (((cadr md) fsym) args))
                   (λ (psym args) (((caddr md) psym) args))
                   undefined
                   fm*))
          interps))

;; ===== finite-model property =====
(define (limmeson n fm)
  (define cls (simpcnf (specialize (pnf fm))))
  (define rules (foldr (λ (c acc) (append (contrapositives c) acc)) '() cls))
  (mexpand002 rules '() #f (λ (env n k) env) undefined n 0))

(define (limited-meson n fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (limmeson n (list-conj d))) (simpdnf fm1)))

(define (decide-fmp fm)
  (define (test n)
    (with-handlers ([exn:fail? (λ (e)
                                 (if (decide-finite n fm)
                                     (test (+ n 1))
                                     #f))])
      (limited-meson n fm)
      #t))
  (test 1))

;; ===== monadic fragment =====
(define (decide-monadic fm)
  (define funcs (functions fm))
  (define preds (predicates fm))
  (define-values (monadic other) (partition (λ (pa) (= (cdr pa) 1)) preds))
  (if (or (not (null? funcs)) (ormap (λ (pa) (> (cdr pa) 1)) other))
      (error 'decide-monadic "Not in the monadic subset")
      ;; A satisfiable monadic formula with k unary predicates has a model of
      ;; size <= 2^k (one element per truth-assignment to the k predicates), so
      ;; checking all models up to that size is complete. 2^k = (funpow k (*2) 1).
      (decide-finite (funpow (length monadic) (λ (x) (* 2 x)) 1) fm)))
