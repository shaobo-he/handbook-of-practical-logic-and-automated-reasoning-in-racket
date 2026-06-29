#lang racket/base

(require rackunit)
(require "../fol/herbrand.rkt")
(require (only-in "../fol/fol.rkt" fvt))

;; ===== pholds: purely propositional evaluation of first-order atoms =====
;; The valuation d is keyed by the WHOLE atom (atom (rel ...)); quantifiers and
;; the domain are ignored -- atoms are treated as opaque propositional letters.
(define (mk-d truths)
  (λ (a) (and (member a truths) #t)))
(check-true (pholds (mk-d '((atom (rel p)))) '(atom (rel p))))
(check-false (pholds (mk-d '()) '(atom (rel p))))
(check-true (pholds (mk-d '((atom (rel p)) (atom (rel q)))) '(and (atom (rel p)) (atom (rel q)))))
(check-false (pholds (mk-d '((atom (rel p)))) '(and (atom (rel p)) (atom (rel q)))))
(check-true (pholds (mk-d '()) '(not (atom (rel p)))))
(check-true (pholds (mk-d '((atom (rel q)))) '(or (atom (rel p)) (atom (rel q)))))
(check-true (pholds (mk-d '()) '(imp (atom (rel p)) (atom (rel q))))) ; antecedent false
(check-false (pholds (mk-d '((atom (rel p)))) '(imp (atom (rel p)) (atom (rel q)))))
(check-true (pholds (mk-d '((atom (rel p)) (atom (rel q)))) '(iff (atom (rel p)) (atom (rel q)))))
(check-false (pholds (mk-d '((atom (rel p)))) '(iff (atom (rel p)) (atom (rel q)))))

;; ===== herbfuns: split the function symbols into constants and proper funcs =====
;; a formula with no constant: a default constant (c . 0) is supplied so the
;; Herbrand universe is non-empty
(let-values ([(consts funcs) (herbfuns '(forall x (atom (rel P (fn f (var x))))))])
  (check-equal? consts '((c . 0)))
  (check-equal? funcs '((f . 1))))
;; mixed arities are partitioned correctly
(let-values ([(consts funcs) (herbfuns '(atom (rel P (fn a) (fn g (fn b) (fn a)))))])
  (check-equal? (sort consts (λ (x y) (symbol<? (car x) (car y)))) '((a . 0) (b . 0)))
  (check-equal? funcs '((g . 2))))

;; ===== groundterms / groundtuples: enumerate the Herbrand universe =====
;; n = 0 gives just the constants
(check-equal? (groundterms '((fn c)) '((f . 1)) 0) '((fn c)))
;; n = 1 applies each function once to level-0 terms
(check-equal? (groundterms '((fn c)) '((f . 1)) 1) '((fn f (fn c))))
;; m-tuples drawn from two constants at level 0: all four 2-tuples, each length 2
(check-equal? (groundtuples '((fn a) (fn b)) '() 0 2)
              '(((fn a) (fn a)) ((fn a) (fn b)) ((fn b) (fn a)) ((fn b) (fn b))))
;; the empty tuple is the sole 0-tuple at level 0
(check-equal? (groundtuples '((fn a) (fn b)) '() 0 0) '(()))
;; every generated ground term really is ground (no free variables)
(check-true (andmap (λ (t) (null? (fvt t))) (groundterms '((fn c)) '((f . 1) (g . 2)) 2)))

;; ===== the three procedures agree on propositional tautologies lifted to FOL =====
;; (or P (not P)) and modus ponens are valid, so each procedure returns a count
(define lem '(or (atom (rel p)) (not (atom (rel p)))))
(define mp '(imp (and (atom (rel p)) (imp (atom (rel p)) (atom (rel q)))) (atom (rel q))))
(check-pred exact-positive-integer? (gilmore lem))
(check-pred exact-positive-integer? (davisputnam lem))
(check-pred exact-positive-integer? (davisputnam002 lem))
(check-pred exact-positive-integer? (gilmore mp))
(check-pred exact-positive-integer? (davisputnam mp))
(check-true (<= (davisputnam002 mp) (davisputnam mp)))

;; Drinker's principle: exists x. forall y. P(x) ==> P(y)   (valid)
(define drinker '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y)))))))

;; universal modus ponens (valid)
(define ump
  '(imp (and (forall x (imp (atom (rel P (var x))) (atom (rel Q (var x)))))
             (forall x (atom (rel P (var x)))))
        (forall x (atom (rel Q (var x))))))

;; each procedure terminates on a valid formula, returning the instance count
(check-pred exact-positive-integer? (gilmore drinker))
(check-pred exact-positive-integer? (davisputnam drinker))
(check-pred exact-positive-integer? (davisputnam002 drinker))

(check-pred exact-positive-integer? (gilmore ump))
(check-pred exact-positive-integer? (davisputnam ump))

;; the refinement keeps no more instances than the full run
(check-true (<= (davisputnam002 drinker) (davisputnam drinker)))
