#lang racket/base

(require rackunit)
(require "tableaux.rkt" "resolution.rkt" "prolog.rkt" "meson.rkt")

(define peirce
  '(imp (imp (imp (atom (rel P)) (atom (rel Q))) (atom (rel P))) (atom (rel P))))
(define drinker
  '(exists x (forall y (imp (atom (rel P (var x))) (atom (rel P (var y)))))))
(define horn
  '(imp (and (and (imp (atom (rel P)) (atom (rel Q)))
                  (imp (atom (rel Q)) (atom (rel R))))
             (atom (rel P)))
        (atom (rel R))))

;; These provers map over the DNF disjuncts of the negated goal and raise if
;; any disjunct can't be refuted; returning normally means "proved". An empty
;; list is a valid proof (every disjunct was trivially unsatisfiable).
;; resolution marks each refuted disjunct with #t; MESON with its proof depth.
(define (all-true? l) (andmap (λ (x) (eq? x #t)) l))
(define (all-nat? l) (andmap exact-nonnegative-integer? l))

;; ===== tableaux / Prawitz =====
(check-pred exact-nonnegative-integer? (tab peirce))
(check-pred exact-nonnegative-integer? (tab drinker))
(check-pred all-nat? (splittab drinker))
(check-pred exact-nonnegative-integer? (prawitz drinker))

;; ===== resolution (all refinements) =====
(check-true (all-true? (resolution001 peirce)))
(check-true (all-true? (resolution002 drinker)))
(check-true (all-true? (resolution003 drinker)))
(check-true (all-true? (presolution drinker)))

;; ===== MESON (each disjunct returns its proof depth) =====
(check-pred all-nat? (meson001 peirce))
(check-pred all-nat? (meson002 drinker))
(check-pred all-nat? (meson horn))
(check-pred pair? (meson002 drinker))   ; drinker really needs a refutation

;; ===== Horn backchaining =====
(check-pred pair? (hornprove horn))

;; ===== toy Prolog: 0 <= x ; S(x) <= S(y) :- x <= y =====
(define le-rules
  (list (cons '() '(atom (rel <= (fn |0|) (var x))))
        (cons (list '(atom (rel <= (var x) (var y))))
              '(atom (rel <= (fn S (var x)) (fn S (var y)))))))
;; ground query succeeds (returns a substitution)
(check-pred hash?
            (simpleprolog le-rules '(atom (rel <= (fn S (fn |0|)) (fn S (fn S (fn |0|)))))))
;; query with a variable yields one binding for z
(check-equal? (length (prolog le-rules '(atom (rel <= (fn S (fn |0|)) (var z))))) 1)
