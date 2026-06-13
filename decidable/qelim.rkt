#lang racket/base

;; qelim.fs --- the generic quantifier-elimination framework (lift_qelim,
;; cnnf) and a worked instance for dense linear orders without endpoints.

(require racket/match)
(require (only-in racket/list partition))
(require (only-in "../core/lib.rkt" update undefined allpairs subtract))
(require (only-in "../core/formulas.rkt" conjuncts disjuncts list-conj list-disj mk-and))
(require (only-in "../prop/prop.rkt" dnf negate))
(require (only-in "../fol/fol.rkt" fv subst))
(require (only-in "../fol/skolem.rkt" simplify))
(require (only-in "decidable.rkt" miniscope))
(require (only-in "../equality/equal.rkt" is-eq dest-eq))

(provide (all-defined-out))

;; eliminate exists x over a conjunction, given a basic elim procedure bfn
(define (qelim bfn x p)
  (define cjs (conjuncts p))
  (define-values (ycjs ncjs) (partition (λ (c) (member x (fv c))) cjs))
  (if (null? ycjs)
      p
      (let ([q (bfn `(exists ,x ,(list-conj ycjs)))]) (foldr mk-and q ncjs))))

;; lift a basic existential procedure to all formulas
(define (lift-qelim afn nfn qfn)
  (define (qelift vars fm)
    (match fm
      [`(atom ,_) (afn vars fm)]
      [`(not ,p) `(not ,(qelift vars p))]
      [`(and ,p ,q) `(and ,(qelift vars p) ,(qelift vars q))]
      [`(or ,p ,q) `(or ,(qelift vars p) ,(qelift vars q))]
      [`(imp ,p ,q) `(imp ,(qelift vars p) ,(qelift vars q))]
      [`(iff ,p ,q) `(iff ,(qelift vars p) ,(qelift vars q))]
      [`(forall ,x ,p) `(not ,(qelift vars `(exists ,x (not ,p))))]
      [`(exists ,x ,p)
       (define djs (disjuncts (nfn (qelift (cons x vars) p))))
       (list-disj (map (λ (dj) (qelim (qfn vars) x dj)) djs))]
      [_ fm]))
  (λ (fm) (simplify (qelift (fv fm) (miniscope fm)))))

;; cleverer NNF with conditional/literal modification
(define (cnnf lfn)
  (define (rec fm)
    (match fm
      [`(and ,p ,q) `(and ,(rec p) ,(rec q))]
      [`(or ,p ,q) `(or ,(rec p) ,(rec q))]
      [`(imp ,p ,q) `(or ,(rec `(not ,p)) ,(rec q))]
      [`(iff ,p ,q) `(or (and ,(rec p) ,(rec q)) (and ,(rec `(not ,p)) ,(rec `(not ,q))))]
      [`(not (not ,p)) (rec p)]
      [`(not (and ,p ,q)) `(or ,(rec `(not ,p)) ,(rec `(not ,q)))]
      [`(not (or (and ,p ,q) (and ,p2 ,r)))
       #:when (equal? p2 (negate p))
       `(or ,(rec `(and ,p (not ,q))) ,(rec `(and ,p2 (not ,r))))]
      [`(not (or ,p ,q)) `(and ,(rec `(not ,p)) ,(rec `(not ,q)))]
      [`(not (imp ,p ,q)) `(and ,(rec p) ,(rec `(not ,q)))]
      [`(not (iff ,p ,q)) `(or (and ,(rec p) ,(rec `(not ,q))) (and ,(rec `(not ,p)) ,(rec q)))]
      [_ (lfn fm)]))
  (λ (fm) (simplify (rec (simplify fm)))))

;; ===== dense linear orders without endpoints =====
(define (lfn-dlo fm)
  (match fm
    [`(not (atom (rel < ,s ,t))) `(or (atom (rel = ,s ,t)) (atom (rel < ,t ,s)))]
    [`(not (atom (rel = ,s ,t))) `(or (atom (rel < ,s ,t)) (atom (rel < ,t ,s)))]
    [_ fm]))

(define (dlobasic fm)
  (match fm
    [`(exists ,x ,p)
     (define cjs (subtract (conjuncts p) (list `(atom (rel = (var ,x) (var ,x))))))
     (define eqn (findf is-eq cjs))
     (cond
       [eqn
        (define st (dest-eq eqn))
        (define y
          (if (equal? (car st) `(var ,x))
              (cdr st)
              (car st)))
        (list-conj (map (λ (c) (subst (update x y undefined) c)) (subtract cjs (list eqn))))]
       [(member `(atom (rel < (var ,x) (var ,x))) cjs) #f]
       [else
        (define-values (lefts rights)
          (partition (λ (a)
                       (match a
                         [`(atom (rel < ,s ,t)) (equal? t `(var ,x))]
                         [_ #f]))
                     cjs))
        (define ls
          (map (λ (a)
                 (match a
                   [`(atom (rel < ,l ,r)) l]))
               lefts))
        (define rs
          (map (λ (a)
                 (match a
                   [`(atom (rel < ,l ,r)) r]))
               rights))
        (list-conj (allpairs (λ (l r) `(atom (rel < ,l ,r))) ls rs))])]
    [_ (error 'dlobasic "dlobasic")]))

(define (afn-dlo vars fm)
  (match fm
    [`(atom (rel <= ,s ,t)) `(not (atom (rel < ,t ,s)))]
    [`(atom (rel >= ,s ,t)) `(not (atom (rel < ,s ,t)))]
    [`(atom (rel > ,s ,t)) `(atom (rel < ,t ,s))]
    [_ fm]))

(define quelim-dlo (lift-qelim afn-dlo (λ (fm) (dnf ((cnnf lfn-dlo) fm))) (λ (v) dlobasic)))
