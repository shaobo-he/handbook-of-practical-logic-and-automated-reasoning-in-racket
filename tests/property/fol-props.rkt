#lang racket/base

;; Property tests for first-order logic: free variables, truth-preserving
;; transformations over finite models, unification, and the provers (run only
;; on guaranteed-valid inputs, since they are semi-decidable).

(require rackunit
         rackcheck
         "common.rkt")
(require (only-in "../../core/lib.rkt" union unions set-eq mapf))
(require (only-in "../../prop/prop.rkt" tautology))
(require (only-in "../../fol/fol.rkt" holds generalize tsubst fvt fv subst variant funcs onformula))
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

;; ===== fol.rkt term/formula algebra =====

;; onformula with the identity term function is the identity on formulas
(check-property big (property ([fm (fol-gen 3)]) (equal? (onformula (λ (t) t) fm) fm)))

;; variant always returns a name that is fresh w.r.t. the avoid-list, and the
;; result is idempotent once it is fresh
(define gen:sym (gen:one-of '(x y z w u v)))
(check-property big
                (property ([x gen:sym] [vs (gen:list gen:sym #:max-length 6)])
                          (define x^ (variant x vs))
                          (and (not (member x^ vs)) (eq? x^ (variant x^ vs)))))

;; substitution lemma / capture-avoidance: the free variables of (subst σ fm)
;; are exactly the free variables contributed by σ on fm's free variables. A
;; capture bug would make a free var of some σ(v) disappear (become bound).
(check-property mid
                (property ([fm (fol-gen 3)] [sx gen:term] [sy gen:term])
                          (define sigma (hash 'x sx 'y sy))
                          (define expected
                            (unions (map (λ (v) (fvt (hash-ref sigma v `(var ,v)))) (fv fm))))
                          (set-eq (fv (subst sigma fm)) expected)))

;; tsubst composition: applying σ2 then σ1 equals applying the single composed
;; substitution (σ1 pushed through σ2's range; domains coincide over {x,y,z})
(check-property
 big
 (property
  ([t gen:term] [a1 gen:term] [a2 gen:term] [a3 gen:term] [b1 gen:term] [b2 gen:term] [b3 gen:term])
  (define s2 (hash 'x a1 'y a2 'z a3))
  (define s1 (hash 'x b1 'y b2 'z b3))
  (equal? (tsubst s1 (tsubst s2 t)) (tsubst (mapf (λ (tm) (tsubst s1 tm)) s2) t))))

;; funcs reports the correct arity for every symbol it returns (gen:term uses
;; a/0, f/1, g/2 consistently, so a wrong count would escape this fixed set)
(check-property big
                (property ([t gen:term])
                          (andmap (λ (fa) (and (member fa '((a . 0) (f . 1) (g . 2))) #t))
                                  (funcs t))))

;; unification decomposes through matching function applications: if g(a,b) and
;; g(c,d) unify, the unifier makes a=c and b=d
(check-property mid
                (property ([a gen:term] [b gen:term] [c gen:term] [d gen:term])
                          (with-handlers ([exn:fail? (λ (e) #t)])
                            (define sig (fullunify (list (cons `(fn g ,a ,b) `(fn g ,c ,d)))))
                            (and (equal? (tsubst sig a) (tsubst sig c))
                                 (equal? (tsubst sig b) (tsubst sig d))))))
