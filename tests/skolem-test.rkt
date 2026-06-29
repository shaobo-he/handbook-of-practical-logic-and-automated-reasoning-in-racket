#lang racket/base

;; Unit tests for skolem.rkt: first-order simplification (simplify1/simplify),
;; prenexing (pullquants/prenex), universal stripping (specialize) and the
;; Skolemization core (skolem/askolemize). The big PNF/Skolemize examples live
;; in fol-test.rkt; here we pin down the individual building blocks.

(require rackunit)
(require "../fol/skolem.rkt")

;; ===== simplify1: one-step first-order simplification =====
;; a quantifier whose variable is unused in the body is dropped...
(check-equal? (simplify1 '(forall x (atom (rel P)))) '(atom (rel P)))
(check-equal? (simplify1 '(exists x (atom (rel P)))) '(atom (rel P)))
;; ...but kept when the variable actually occurs
(check-equal? (simplify1 '(forall x (atom (rel P (var x))))) '(forall x (atom (rel P (var x)))))
;; non-quantifier cases fall through to the propositional psimplify1
(check-equal? (simplify1 '(not (not (atom (rel P))))) '(atom (rel P)))
(check-equal? (simplify1 '(and (atom (rel P)) #t)) '(atom (rel P)))

;; ===== simplify: recursive simplification =====
(check-equal? (simplify '(forall x (and (atom (rel P (var y))) #t))) '(atom (rel P (var y))))
(check-equal? (simplify '(exists x (forall y (atom (rel P))))) '(atom (rel P)))

;; ===== specialize: strip leading universal quantifiers =====
(check-equal? (specialize '(forall x (atom (rel P (var x))))) '(atom (rel P (var x))))
(check-equal? (specialize '(forall x (forall y (atom (rel R (var x) (var y))))))
              '(atom (rel R (var x) (var y))))
;; no leading universal -> unchanged (an inner forall is left in place)
(check-equal? (specialize '(atom (rel P))) '(atom (rel P)))
(check-equal? (specialize '(exists x (atom (rel P (var x))))) '(exists x (atom (rel P (var x)))))

;; ===== pullquants / prenex: float quantifiers to the front =====
;; pullquants merges two like quantifiers, renaming both bound vars to a fresh z
(check-equal? (pullquants '(and (forall x (atom (rel P (var x)))) (forall y (atom (rel Q (var y))))))
              '(forall x (and (atom (rel P (var x))) (atom (rel Q (var x))))))
;; prenex pulls a leading universal out through a conjunction
(check-equal? (prenex '(and (forall x (atom (rel P (var x)))) (forall y (atom (rel Q (var y))))))
              '(forall x (and (atom (rel P (var x))) (atom (rel Q (var x))))))
(check-equal? (prenex '(forall x (and (atom (rel P (var x))) (atom (rel Q)))))
              '(forall x (and (atom (rel P (var x))) (atom (rel Q)))))

;; ===== skolem: existentials become Skolem constants/functions =====
;; closed existential (no free vars) -> Skolem CONSTANT c_y
(let-values ([(fm fns) (skolem '(exists y (atom (rel P (var y)))) '())])
  (check-equal? fm '(atom (rel P (fn c_y))))
  (check-equal? fns '(c_y)))
;; existential with a free var x -> Skolem FUNCTION f_y applied to x
(let-values ([(fm fns) (skolem '(exists y (atom (rel P (var x) (var y)))) '())])
  (check-equal? fm '(atom (rel P (var x) (fn f_y (var x)))))
  (check-equal? fns '(f_y)))
;; a universal is preserved, its body Skolemized
(let-values ([(fm fns) (skolem '(forall x (exists y (atom (rel P (var x) (var y))))) '())])
  (check-equal? fm '(forall x (atom (rel P (var x) (fn f_y (var x))))))
  (check-equal? fns '(f_y)))
;; an already-used Skolem name is avoided via variant (^)
(let-values ([(fm fns) (skolem '(exists y (atom (rel P (var y)))) '(c_y))])
  (check-equal? fm '(atom (rel P (fn c_y^))))
  (check-equal? fns '(c_y^ c_y)))

;; ===== askolemize: simplify + nnf, then Skolemize (no prenex/specialize) =====
(check-equal? (askolemize '(exists x (atom (rel P (var x))))) '(atom (rel P (fn c_x))))
