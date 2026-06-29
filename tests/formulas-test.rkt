#lang racket/base

;; Unit tests for the generic formula operations and the pretty printer.

(require rackunit)
(require racket/port)
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
(check-exn exn:fail? (λ () (dest-imp '(and a b))))

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
(check-equal? (onatoms (λ (a) `(atom (renamed ,a))) '(and (atom p) (not (atom q))))
              '(and (atom (renamed p)) (not (atom (renamed q)))))
(check-equal? (overatoms (λ (a acc) (cons a acc)) '(and (atom p) (atom q)) '()) '(p q))
(check-equal? (sort (atom-union (λ (a) (list a)) '(and (atom p) (or (atom q) (atom p)))) symbol<?)
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

;; ===== remaining constructors =====
(check-equal? (mk-or 'p 'q) '(or p q))
(check-equal? (mk-iff 'p 'q) '(iff p q))
(check-equal? (mk-forall 'x '(atom p)) '(forall x (atom p)))
(check-equal? (mk-exists 'x '(atom q)) '(exists x (atom q)))

;; ===== destructor error cases (each rejects the wrong connective) =====
(check-exn exn:fail? (λ () (dest-and '(or p q))))
(check-exn exn:fail? (λ () (dest-or '(and p q))))
(check-exn exn:fail? (λ () (dest-iff '(imp p q))))
(check-exn exn:fail? (λ () (dest-imp '(iff p q))))

;; ===== conjuncts / disjuncts: deeply nested binary trees flatten fully =====
(check-equal? (conjuncts '(and (and a b) (and c d))) '(a b c d))
(check-equal? (conjuncts '(and a (and b (and c d)))) '(a b c d))
(check-equal? (disjuncts '(or (or a b) (or c d))) '(a b c d))
;; a non-and node under an or is a single conjunct (mixing stops at the head)
(check-equal? (conjuncts '(and (or a b) c)) '((or a b) c))

;; ===== onatoms: structure preserved across every formula shape =====
(define (tag a)
  `(atom (t ,a)))
(check-equal? (onatoms tag '(not (atom p))) '(not (atom (t p))))
(check-equal? (onatoms tag '(or (atom p) (atom q))) '(or (atom (t p)) (atom (t q))))
(check-equal? (onatoms tag '(imp (atom p) (atom q))) '(imp (atom (t p)) (atom (t q))))
(check-equal? (onatoms tag '(iff (atom p) (atom q))) '(iff (atom (t p)) (atom (t q))))
(check-equal? (onatoms tag '(forall x (atom p))) '(forall x (atom (t p))))
(check-equal? (onatoms tag '(exists x (atom q))) '(exists x (atom (t q))))
(check-equal? (onatoms tag #t) #t) ; constants pass through unchanged

;; ===== printer: constants, quantifiers, and a custom atom printer =====
(check-equal? (formula->string pv #f) "false")
(check-equal? (formula->string pv '(exists x (atom p))) "exists x. p")
;; mixed quantifiers are NOT merged into one run
(check-equal? (formula->string pv '(forall x (exists y (atom p)))) "forall x. exists y. p")

;; ===== print-formula / print-qformula write to current output =====
(check-equal? (with-output-to-string (λ () (print-formula pv '(atom p)))) "p")
(check-equal? (with-output-to-string (λ () (print-formula pv '(and (atom p) (atom q))))) "p /\\ q")
(check-equal? (with-output-to-string (λ () (print-qformula pv '(atom p)))) "<<p>>")
