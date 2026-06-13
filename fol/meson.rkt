#lang racket/base

;; meson.fs --- the MESON model-elimination procedure (Stickel's PTTP
;; style): contrapositives + Prolog-style extension with ancestor
;; resolution, then a version with repetition checking and
;; divide-and-conquer search.

(require racket/match)
(require (only-in "../core/lib.rkt" subtract tryfind chop-list undefined))
(require (only-in "../core/formulas.rkt" list-conj))
(require (only-in "../prop/prop.rkt" negate negative simpcnf simpdnf))
(require (only-in "fol.rkt" generalize))
(require (only-in "skolem.rkt" specialize pnf askolemize))
(require (only-in "tableaux.rkt" unify-literals deepen))
(require (only-in "prolog.rkt" renamerule))

(provide (all-defined-out))

;; ===== contrapositives of a clause =====
(define (contrapositives cls)
  (define base (map (λ (c) (cons (map negate (subtract cls (list c))) c)) cls))
  (if (andmap negative cls)
      (cons (cons (map negate cls) #f) base)
      base))

;; ===== core MESON (basic version) =====
(define (mexpand001 rules ancestors g cont env n k)
  (cond
    [(< n 0) (error 'meson "Too deep")]
    [else
     (with-handlers
       ([exn:fail?
         (λ (e)
           (tryfind (λ (rule)
                      (define-values (rc k*) (renamerule k rule))
                      (define asm (car rc))
                      (define c (cdr rc))
                      (define combined
                        (foldr (λ (subgoal nextcont)
                                 (λ (env n k)
                                   (mexpand001 rules (cons g ancestors) subgoal nextcont env n k)))
                               cont asm))
                      (combined (unify-literals env (cons g c)) (- n (length asm)) k*))
                    rules))])
       (tryfind (λ (a) (cont (unify-literals env (cons g (negate a))) n k)) ancestors))]))

(define (puremeson001 fm)
  (define cls (simpcnf (specialize (pnf fm))))
  (define rules (foldr (λ (c acc) (append (contrapositives c) acc)) '() cls))
  (deepen (λ (n) (mexpand001 rules '() #f (λ (env n k) env) undefined n 0) n) 0))

(define (meson001 fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (puremeson001 (list-conj d))) (simpdnf fm1)))

;; ===== MESON with repetition checking and divide-and-conquer =====
(define (meson-equal? env fm1 fm2)
  (with-handlers ([exn:fail? (λ (e) #f)])
    (equal? (unify-literals env (cons fm1 fm2)) env)))

(define (expand2 expfn goals1 n1 goals2 n2 n3 cont env k)
  (expfn goals1
         (λ (e1 r1 k1)
           (expfn goals2
                  (λ (e2 r2 k2)
                    (if (<= (+ n2 r1) (+ n3 r2)) (error 'meson "pair") (cont e2 r2 k2)))
                  e1 (+ n2 r1) k1))
         env n1 k))

(define (mexpands002 rules ancestors gs cont env n k)
  (cond
    [(< n 0) (error 'meson "Too deep")]
    [else
     (define m (length gs))
     (if (<= m 1)
         ((foldr (λ (subgoal nextcont)
                   (λ (env n k) (mexpand002 rules ancestors subgoal nextcont env n k)))
                 cont gs)
          env n k)
         (let ()
           (define n1 (quotient n 2))
           (define n2 (- n n1))
           (define-values (goals1 goals2) (chop-list (quotient m 2) gs))
           (define (expfn gs cont env n k) (mexpands002 rules ancestors gs cont env n k))
           (with-handlers ([exn:fail? (λ (e) (expand2 expfn goals2 n1 goals1 n2 n1 cont env k))])
             (expand2 expfn goals1 n1 goals2 n2 -1 cont env k))))]))

(define (mexpand002 rules ancestors g cont env n k)
  (cond
    [(< n 0) (error 'meson "Too deep")]
    [(ormap (λ (a) (meson-equal? env g a)) ancestors) (error 'meson "repetition")]
    [else
     (with-handlers
       ([exn:fail?
         (λ (e)
           (tryfind (λ (r)
                      (define-values (rc k*) (renamerule k r))
                      (mexpands002 rules (cons g ancestors) (car rc) cont
                                   (unify-literals env (cons g (cdr rc)))
                                   (- n (length (car rc))) k*))
                    rules))])
       (tryfind (λ (a) (cont (unify-literals env (cons g (negate a))) n k)) ancestors))]))

(define (puremeson002 fm)
  (define cls (simpcnf (specialize (pnf fm))))
  (define rules (foldr (λ (c acc) (append (contrapositives c) acc)) '() cls))
  (deepen (λ (n) (mexpand002 rules '() #f (λ (env n k) env) undefined n 0) n) 0))

(define (meson002 fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (puremeson002 (list-conj d))) (simpdnf fm1)))

(define meson meson002)
