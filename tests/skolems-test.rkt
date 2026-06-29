#lang racket/base

;; Unit tests for skolems.rkt: renaming function symbols apart (rename-term /
;; rename-form) and Skolemizing a *set* of formulas while keeping the Skolem
;; function names globally distinct (skolems / skolemizes).

(require rackunit)
(require "../fol/skolems.rkt")

;; ===== rename-term: prefix every function symbol with old_ =====
(check-equal? (rename-term '(var x)) '(var x)) ; variables untouched
(check-equal? (rename-term '(fn f (var x))) '(fn old_f (var x)))
(check-equal? (rename-term '(fn f (fn g (var x)))) '(fn old_f (fn old_g (var x)))) ; recurses

;; ===== rename-form: apply rename-term inside every atom, keep the structure =====
(check-equal? (rename-form '(atom (rel P (fn f (var x))))) '(atom (rel P (fn old_f (var x)))))
(check-equal? (rename-form '(and (atom (rel P (fn f (var x)))) (atom (rel Q (var y)))))
              '(and (atom (rel P (fn old_f (var x)))) (atom (rel Q (var y)))))
(check-equal? (rename-form '(forall x (atom (rel P (fn f (var x))))))
              '(forall x (atom (rel P (fn old_f (var x))))))

;; ===== skolems: Skolemize a list, threading the used-names correspondence =====
(check-equal? (let-values ([(r corr) (skolems '() '())])
                (list r corr))
              '(() ()))
;; list length is preserved
(let-values ([(r corr) (skolems '((exists x (atom (rel P (var x)))) (exists x (atom (rel Q (var x)))))
                                '())])
  (check-equal? (length r) 2))

;; ===== skolemizes: the public wrapper (just the formula list) =====
(check-equal? (skolemizes '((exists x (atom (rel P (var x)))))) '((atom (rel P (fn c_x)))))
;; two existentials over the same variable get DISTINCT Skolem constants
(check-equal? (skolemizes '((exists x (atom (rel P (var x)))) (exists x (atom (rel Q (var x))))))
              '((atom (rel P (fn c_x))) (atom (rel Q (fn c_x^)))))
;; no existential -> only the old_ function renaming happens
(check-equal? (skolemizes '((atom (rel P (fn f (var x)))))) '((atom (rel P (fn old_f (var x))))))
