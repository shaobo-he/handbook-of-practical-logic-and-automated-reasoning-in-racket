#lang racket/base

;; Unit tests for the generic formula operations and the pretty printer.

(require rackunit)
(require "../core/formulas.rkt")

;; ===== constructors / destructors =====
(check-equal? (mk-and 'a 'b) '(and a b))
(check-equal? (mk-imp 'a 'b) '(imp a b))
(check-equal? (dest-imp '(imp a b)) '(a . b))
(check-equal? (antecedent '(imp a b)) 'a)
(check-equal? (consequent '(imp a b)) 'b)
(check-equal? (dest-iff '(iff a b)) '(a . b))
(check-equal? (dest-and '(and a b)) '(a . b))
(check-equal? (dest-or '(or a b)) '(a . b))
(check-exn exn:fail? (lambda () (dest-imp '(and a b))))

;; ===== conjuncts / disjuncts / list-conj / list-disj / end-itlist =====
(check-equal? (conjuncts '(and a (and b c))) '(a b c))
(check-equal? (conjuncts 'x) '(x))
(check-equal? (disjuncts '(or a (or b c))) '(a b c))
(check-equal? (list-conj '(a b c)) '(and a (and b c)))
(check-equal? (list-conj '(a)) 'a)
(check-equal? (list-conj '()) #t)
(check-equal? (list-disj '()) #f)
(check-equal? (list-disj '(a b)) '(or a b))
(check-equal? (end-itlist + '(1 2 3)) 6)
(check-equal? (end-itlist - '(1 2 3)) 2) ; 1 - (2 - 3)

;; ===== atom traversal =====
(check-equal? (onatoms (lambda (a) `(atom (renamed ,a))) '(and (atom p) (not (atom q))))
              '(and (atom (renamed p)) (not (atom (renamed q)))))
(check-equal? (overatoms (lambda (a acc) (cons a acc)) '(and (atom p) (atom q)) '()) '(p q))
(check-equal? (sort (atom-union (lambda (a) (list a)) '(and (atom p) (or (atom q) (atom p))))
                    symbol<?)
              '(p q))

;; ===== printer (custom atom printer; exercises precedence + strip-quant) =====
(define (pv prec a)
  (symbol->string a))
(check-equal? (formula->string pv '(imp (atom p) (and (atom q) (atom r)))) "p ==> q /\\ r")
(check-equal? (formula->string pv '(and (or (atom p) (atom q)) (atom r))) "(p \\/ q) /\\ r")
(check-equal? (formula->string pv '(forall x (forall y (atom p)))) "forall x y. p")
(check-equal? (formula->string pv '(not (not (atom p)))) "~(~p)")
(check-equal? (formula->string pv #t) "true")
(check-equal? (formula->string pv '(iff (atom p) (atom q))) "p <=> q")

;; strip-quant collects a run of like quantifiers
(check-equal? (let-values ([(vs body) (strip-quant '(forall x (forall y (atom p))))])
                (list vs body))
              '((x y) (atom p)))
