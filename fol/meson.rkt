#lang racket/base

;; meson --- the MESON model-elimination procedure (Stickel's PTTP
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

;; ===== contrapositives of a clause (the PTTP rule form) =====
;; A clause l1∨...∨ln becomes n Horn-style rules (body . head): pick each literal
;; in turn as the head and take the negations of the rest as the body. An
;; all-negative clause additionally yields a rule with head #f (false), the only
;; way such a clause can ever be used to close a branch.
(define (contrapositives cls)
  (define base (map (λ (c) (cons (map negate (subtract cls (list c))) c)) cls))
  (if (andmap negative cls)
      (cons (cons (map negate cls) #f) base)
      base))

;; ===== core MESON (basic version) =====
;; Two ways to discharge goal g, via exceptions for backtracking: the body first
;; tries the REDUCTION rule (close g by unifying it with the negation of an
;; ancestor); if that raises, the handler tries EXTENSION (pick a contrapositive
;; rule, unify its head with g, and recurse on its body as new subgoals). n is the
;; remaining inference budget; k threads fresh variables.
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
                                 cont
                                 asm))
                        (combined (unify-literals env (cons g c)) (- n (length asm)) k*))
                      rules))])
       (tryfind (λ (a) (cont (unify-literals env (cons g (negate a))) n k)) ancestors))]))

(define (puremeson001 fm)
  (define cls (simpcnf (specialize (pnf fm))))
  (define rules (foldr (λ (c acc) (append (contrapositives c) acc)) '() cls))
  (deepen (λ (n)
            (mexpand001 rules '() #f (λ (env n k) env) undefined n 0)
            n)
          0))

(define (meson001 fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (puremeson001 (list-conj d))) (simpdnf fm1)))

;; ===== MESON with repetition checking and divide-and-conquer =====
;; #t iff fm1 and fm2 are already identical under env — i.e. unifying them adds no
;; new bindings. Used to spot when a goal recurs unchanged in its ancestor chain.
(define (meson-equal? env fm1 fm2)
  (with-handlers ([exn:fail? (λ (e) #f)])
    (equal? (unify-literals env (cons fm1 fm2)) env)))

;; Solve goals1 (budget n1) then goals2, where r1/r2 are the inferences each had
;; left over. The (<= (+ n2 r1) (+ n3 r2)) guard raises unless this ordering used
;; strictly fewer inferences than the alternative (n3 is set to -1 for the first
;; attempt and to the first attempt's cost for the retry), so the two orderings
;; race and the cheaper one wins — the divide-and-conquer search heuristic.
(define (expand2 expfn goals1 n1 goals2 n2 n3 cont env k)
  (expfn goals1
         (λ (e1 r1 k1)
           (expfn goals2
                  (λ (e2 r2 k2)
                    (if (<= (+ n2 r1) (+ n3 r2))
                        (error 'meson "pair")
                        (cont e2 r2 k2)))
                  e1
                  (+ n2 r1)
                  k1))
         env
         n1
         k))

;; solve a list of goals, splitting the work and the depth budget in half
;; (divide-and-conquer); expand2 tries one half-order, and on failure the handler
;; retries with the halves swapped, so effort is spent on whichever half is harder.
(define (mexpands002 rules ancestors gs cont env n k)
  (cond
    [(< n 0) (error 'meson "Too deep")]
    [else
     (define m (length gs))
     (if (<= m 1)
         ((foldr (λ (subgoal nextcont)
                   (λ (env n k) (mexpand002 rules ancestors subgoal nextcont env n k)))
                 cont
                 gs)
          env
          n
          k)
         (let ()
           (define n1 (quotient n 2))
           (define n2 (- n n1))
           (define-values (goals1 goals2) (chop-list (quotient m 2) gs))
           (define (expfn gs cont env n k)
             (mexpands002 rules ancestors gs cont env n k))
           (with-handlers ([exn:fail? (λ (e) (expand2 expfn goals2 n1 goals1 n2 n1 cont env k))])
             (expand2 expfn goals1 n1 goals2 n2 -1 cont env k))))]))

(define (mexpand002 rules ancestors g cont env n k)
  (cond
    [(< n 0) (error 'meson "Too deep")]
    ;; cut off looping branches: fail if g already appears (unifies unchanged) in
    ;; its own ancestor chain — the key efficiency gain of this version over 001
    [(ormap (λ (a) (meson-equal? env g a)) ancestors) (error 'meson "repetition")]
    [else
     (with-handlers ([exn:fail? (λ (e)
                                  (tryfind (λ (r)
                                             (define-values (rc k*) (renamerule k r))
                                             (mexpands002 rules
                                                          (cons g ancestors)
                                                          (car rc)
                                                          cont
                                                          (unify-literals env (cons g (cdr rc)))
                                                          (- n (length (car rc)))
                                                          k*))
                                           rules))])
       (tryfind (λ (a) (cont (unify-literals env (cons g (negate a))) n k)) ancestors))]))

(define (puremeson002 fm)
  (define cls (simpcnf (specialize (pnf fm))))
  (define rules (foldr (λ (c acc) (append (contrapositives c) acc)) '() cls))
  (deepen (λ (n)
            (mexpand002 rules '() #f (λ (env n k) env) undefined n 0)
            n)
          0))

(define (meson002 fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (puremeson002 (list-conj d))) (simpdnf fm1)))

(define meson meson002)
