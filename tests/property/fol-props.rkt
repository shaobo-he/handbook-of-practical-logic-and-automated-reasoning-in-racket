#lang racket/base

;; Property tests for first-order logic: free variables, truth-preserving
;; transformations over finite models, unification, and the provers (run only
;; on guaranteed-valid inputs, since they are semi-decidable).

(require rackunit
         rackcheck
         "common.rkt")
(require (only-in "../../core/lib.rkt" union set-eq))
(require (only-in "../../prop/prop.rkt" tautology))
(require (only-in "../../fol/fol.rkt" holds generalize tsubst fvt fv))
(require (only-in "../../fol/skolem.rkt" [nnf skolem-nnf] [simplify skolem-simplify] prenex pnf))
(require (only-in "../../fol/unif.rkt" fullunify unify-and-apply))
(require (only-in "../../fol/meson.rkt" meson))
(require (only-in "../../fol/tableaux.rkt" tab))

;; fvt distributes over function application
(check-property big
                (property ([a gen:term] [b gen:term])
                          (set-eq (fvt `(fn g ,a ,b)) (union (fvt a) (fvt b)))))

;; skolem's simplify/NNF/prenex/PNF preserve truth in every finite model
(define fmdom '(0 1))
(define (nofunc f args)
  (error "no function symbols"))
(define (mk-pred p0 p1 q0 q1)
  (λ (psym args)
    (define d (car args))
    (cond
      [(eq? psym 'P) (if (= d 0) p0 p1)]
      [(eq? psym 'Q) (if (= d 0) q0 q1)])))
(define (fol-gen n)
  (define as
    '((atom (rel P (var x))) (atom (rel P (var y))) (atom (rel Q (var x))) (atom (rel Q (var y)))))
  (if (<= n 0)
      (gen:one-of as)
      (gen:frequency (list (cons 1 (gen:one-of as))
                           (cons 2 (gen:map (fol-gen (sub1 n)) (λ (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or imp iff) fol-gen n))
                           (cons 2 (quant-gen '(forall exists) '(x y) fol-gen n))))))
(check-property
 mid
 (property ([fm0 (fol-gen 3)] [p0 gen:boolean] [p1 gen:boolean] [q0 gen:boolean] [q1 gen:boolean])
           (define fm (generalize fm0))
           (define pred (mk-pred p0 p1 q0 q1))
           (define h (holds fmdom nofunc pred (hash) fm))
           (and (null? (fv fm))
                (eq? h (holds fmdom nofunc pred (hash) (skolem-nnf fm)))
                (eq? h (holds fmdom nofunc pred (hash) (skolem-simplify fm)))
                (eq? h (holds fmdom nofunc pred (hash) (prenex fm)))
                (eq? h (holds fmdom nofunc pred (hash) (pnf fm))))))
;; holds and negation are complementary
(check-property
 mid
 (property ([fm0 (fol-gen 3)] [p0 gen:boolean] [p1 gen:boolean] [q0 gen:boolean] [q1 gen:boolean])
           (define fm (generalize fm0))
           (define pred (mk-pred p0 p1 q0 q1))
           (not (eq? (holds fmdom nofunc pred (hash) fm)
                     (holds fmdom nofunc pred (hash) `(not ,fm))))))

;; unification: soundness, symmetry, idempotence of the solved form
(define (unifiable? s t)
  (with-handlers ([exn:fail? (λ (e) #f)])
    (fullunify (list (cons s t)))
    #t))
(check-property mid
                (property ([s gen:term] [t gen:term])
                          (with-handlers ([exn:fail? (λ (e) #t)])
                            (andmap (λ (e) (equal? (car e) (cdr e)))
                                    (unify-and-apply (list (cons s t)))))))
(check-property mid (property ([s gen:term] [t gen:term]) (eq? (unifiable? s t) (unifiable? t s))))
(check-property mid
                (property ([s gen:term] [t gen:term])
                          (or (not (unifiable? s t))
                              (let ([sig (fullunify (list (cons s t)))])
                                (equal? (tsubst sig (tsubst sig s)) (tsubst sig s))))))

;; MESON and the tableau prover prove every (small) propositional tautology
(check-property low
                (property ([fm gen:small-prop])
                          (or (not (tautology fm))
                              (and (andmap exact-nonnegative-integer? (meson fm))
                                   (exact-nonnegative-integer? (tab fm))))))
