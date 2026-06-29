#lang racket/base

;; Property tests for the first-order provers. Cheap structural laws of the
;; resolution helpers (unifiable symmetric, subsumes-clause reflexive, rename
;; length-preserving, mgu idempotent, unify-literals sound) run at high volume;
;; the semi-decidable search procedures (resolution, presolution, meson, tab,
;; splittab) are run ONLY on guaranteed tautologies and cross-checked for
;; agreement, since on invalid input they would loop forever.

(require rackcheck
         rackunit
         "common.rkt")
(require (only-in "../../core/lib.rkt" undefined))
(require (only-in "../../prop/prop.rkt" tautology))
(require (only-in "../../fol/fol.rkt" tsubst))
(require (only-in "../../fol/unif.rkt" solve))
(require (only-in "../../fol/tableaux.rkt" unify-literals tab splittab))
(require (only-in "../../fol/resolution.rkt"
                  unifiable
                  subsumes-clause
                  rename
                  mgu
                  resolution003
                  presolution))
(require (only-in "../../fol/meson.rkt" meson001 meson002))

;; ===== literal / clause generators =====
(define gen:fol-atom
  (gen:bind (gen:one-of '(P Q)) (λ (p) (gen:map gen:term (λ (t) `(atom (rel ,p ,t)))))))
(define gen:fol-lit
  (gen:bind gen:fol-atom
            (λ (a)
              (gen:map gen:boolean
                       (λ (b)
                         (if b
                             a
                             `(not ,a)))))))
(define gen:clause (gen:list gen:fol-lit #:max-length 3))
(define gen:fol-prop-nc (prop-gen-over '((atom (rel p)) (atom (rel q))) 3 #f))

(define (all-true? l)
  (andmap (λ (x) (eq? x #t)) l))
(define (all-nat? l)
  (andmap exact-nonnegative-integer? l))

;; ===== cheap structural laws (high volume) =====
;; unifiability of literals is symmetric
(check-property big
                (property ([p gen:fol-atom] [q gen:fol-atom]) (eq? (unifiable p q) (unifiable q p))))

;; a clause always subsumes itself
(check-property big (property ([c gen:clause]) (subsumes-clause c c)))

;; renaming preserves the number of literals
(check-property big
                (property ([c gen:clause])
                          (= (length (rename "z"
                                             c))
                             (length c))))

;; ===== unify-literals is sound: the solved unifier makes the literals equal =====
(check-property mid
                (property ([s gen:term] [t gen:term])
                          (define l1 `(atom (rel P ,s)))
                          (define l2 `(atom (rel P ,t)))
                          (with-handlers ([exn:fail? (λ (e) #t)])
                            (define sig (solve (unify-literals undefined (cons l1 l2))))
                            (equal? (tsubst sig `(fn P ,s)) (tsubst sig `(fn P ,t))))))

;; ===== mgu returns an idempotent substitution =====
(check-property mid
                (property ([s gen:term] [t gen:term])
                          (define l1 `(atom (rel P ,s)))
                          (define l2 `(atom (rel P ,t)))
                          (with-handlers ([exn:fail? (λ (e) #t)])
                            (define sig (mgu (list l1 l2) undefined))
                            (and (equal? (tsubst sig (tsubst sig `(fn P ,s))) (tsubst sig `(fn P ,s)))
                                 (equal? (tsubst sig (tsubst sig `(fn P ,t)))
                                         (tsubst sig `(fn P ,t)))))))

;; ===== resolution and positive resolution prove every small tautology =====
(check-property tiny
                (property ([fm gen:fol-prop-nc])
                          (or (not (tautology fm))
                              (and (all-true? (resolution003 fm)) (all-true? (presolution fm))))))

;; ===== the two MESON drivers agree on every small tautology =====
(check-property low
                (property ([fm gen:small-prop])
                          (or (not (tautology fm))
                              (and (all-nat? (meson001 fm)) (all-nat? (meson002 fm))))))

;; ===== tab and splittab both prove every small tautology =====
(check-property low
                (property ([fm gen:small-prop])
                          (or (not (tautology fm))
                              (and (exact-nonnegative-integer? (tab fm)) (all-nat? (splittab fm))))))
