#lang racket/base

(require rackunit)
(require "../prop/prop.rkt")

;; ===== evaluation =====
(define (v->fn alist)
  (λ (x) (cdr (assoc x alist))))
(check-true (eval '(and (atom p) (atom q)) (v->fn '((p . #t) (q . #t)))))
(check-false (eval '(and (atom p) (atom q)) (v->fn '((p . #t) (q . #f)))))
(check-true (eval '(imp (atom p) (atom q)) (v->fn '((p . #f) (q . #f)))))

;; ===== atoms =====
(check-equal? (sort (atoms '(imp (atom p) (or (atom q) (atom p)))) symbol<?) '(p q))

;; ===== tautology / satisfiability =====
(check-true (tautology '(or (atom p) (not (atom p)))))
(check-false (tautology '(or (atom p) (atom q))))
;; hypothetical syllogism
(check-true (tautology '(imp (and (imp (atom p) (atom q)) (imp (atom q) (atom r)))
                             (imp (atom p) (atom r)))))
;; De Morgan
(check-true (tautology '(iff (not (and (atom p) (atom q))) (or (not (atom p)) (not (atom q))))))
(check-false (satisfiable '(and (atom p) (not (atom p)))))
(check-true (unsatisfiable '(and (atom p) (not (atom p)))))
(check-true (satisfiable '(or (atom p) (atom q))))

;; ===== simplification =====
(check-equal? (psimplify '(imp (imp #t (iff (atom x) #f)) (not (or (atom y) (and #f (atom z))))))
              '(imp (not (atom x)) (not (atom y))))
(check-equal? (psimplify '(or (imp (imp (atom x) (atom y)) #t) (not #f))) #t)

;; ===== duality =====
(check-equal? (dual '(and (atom p) (or (atom q) #f))) '(or (atom p) (and (atom q) #t)))

;; ===== NNF preserves meaning and removes ==>, <=> =====
(define f1 '(imp (atom p) (iff (atom q) (atom r))))
(check-true (tautology `(iff ,f1 ,(nnf f1))))

;; ===== DNF / CNF preserve meaning =====
(define f2 '(iff (atom p) (and (atom q) (or (atom r) (not (atom p))))))
(check-true (tautology `(iff ,f2 ,(dnf f2))))
(check-true (tautology `(iff ,f2 ,(cnf f2))))

;; ===== set-of-sets normal forms: edge cases =====
(check-equal? (simpcnf #t) '())
(check-equal? (simpcnf #f) (list '()))
(check-equal? (simpdnf #t) (list '()))
(check-equal? (simpdnf #f) '())

;; ===== printer =====
(check-equal? (prop-formula->string '(imp (atom p) (and (atom q) (atom r)))) "p ==> q /\\ r")
(check-equal? (prop-formula->string '(and (or (atom p) (atom q)) (atom r))) "(p \\/ q) /\\ r")
;; prefix operands print at precedence 11, so nested ~ brackets
(check-equal? (prop-formula->string '(not (not (atom p)))) "~(~p)")

;; ===== more evaluation =====
(check-true (eval '(iff (atom p) (atom q)) (v->fn '((p . #t) (q . #t)))))
(check-false (eval '(or (atom p) (atom q)) (v->fn '((p . #f) (q . #f)))))
(check-false (eval '(not (atom p)) (v->fn '((p . #t)))))

;; ===== NNF / NENF shape =====
(check-equal? (nnf '(imp (atom p) (atom q))) '(or (not (atom p)) (atom q)))
(check-equal? (nenf '(not (imp (atom p) (atom q)))) '(and (atom p) (not (atom q))))
(check-equal? (nenf '(not (iff (atom p) (atom q)))) '(iff (atom p) (not (atom q)))) ; NENF keeps <=>

;; ===== psubst (subfn is a partial function atom -> formula) =====
(check-equal? (psubst (hash 'p '(atom q)) '(and (atom p) (atom r))) '(and (atom q) (atom r)))

;; ===== more tautology / satisfiability =====
(check-true (tautology '(imp (atom p) (or (atom p) (atom q)))))
(check-true (satisfiable '(iff (atom p) (atom q))))
(check-false (tautology '(imp (or (atom p) (atom q)) (and (atom p) (atom q)))))

;; ===== onallvaluations (the meta-operator behind tautology) =====
;; a constant-true subfn holds over every valuation, regardless of atoms
(check-true (onallvaluations (λ (v) #t) (λ (s) #f) '(a b)))
(check-false (onallvaluations (λ (v) #f) (λ (s) #f) '(a b)))
;; folding (eval fm) over all valuations is exactly tautology
(define oav-fm '(or (atom p) (not (atom p))))
(check-equal? (onallvaluations (λ (v) (eval oav-fm v)) (λ (s) #f) (atoms oav-fm)) (tautology oav-fm))
(check-equal? (onallvaluations (λ (v) (eval '(or (atom p) (atom q)) v)) (λ (s) #f) '(p q))
              (tautology '(or (atom p) (atom q))))

;; ===== allsatvaluations (enumerate the satisfying rows) =====
;; p \/ q is false only when both are false: 3 of the 4 rows satisfy it
(check-equal? (length (allsatvaluations (λ (v) (eval '(or (atom p) (atom q)) v)) (λ (s) #f) '(p q)))
              3)
;; a tautology over two atoms satisfies all four rows; a contradiction none
(check-equal?
 (length (allsatvaluations (λ (v) (eval '(or (atom p) (not (atom p))) v)) (λ (s) #f) '(p)))
 2)
(check-equal?
 (length (allsatvaluations (λ (v) (eval '(and (atom p) (not (atom p))) v)) (λ (s) #f) '(p)))
 0)
;; the returned valuations really do satisfy the formula
(check-true (andmap (λ (v) (eval '(iff (atom p) (atom q)) v))
                    (allsatvaluations (λ (v) (eval '(iff (atom p) (atom q)) v)) (λ (s) #f) '(p q))))

;; ===== mk-lits (build the literal conjunction picked out by a valuation) =====
(check-equal? (mk-lits '((atom p) (atom q)) (λ (x) #t)) '(and (atom p) (atom q)))
(check-equal? (mk-lits '((atom p) (atom q)) (λ (x) (eq? x 'p))) '(and (atom p) (not (atom q))))

;; ===== literal predicates: negative / positive / negate =====
(check-true (negative '(not (atom p))))
(check-false (negative '(atom p)))
(check-true (positive '(atom p)))
(check-false (positive '(not (atom p))))
(check-equal? (negate '(atom p)) '(not (atom p)))
(check-equal? (negate '(not (atom p))) '(atom p))
;; negate is an involution on literals
(check-equal? (negate (negate '(atom p))) '(atom p))
(check-equal? (negate (negate '(not (atom p)))) '(not (atom p)))

;; ===== trivial (a clause holding a literal and its negation) =====
(check-true (trivial (list '(atom p) '(not (atom p)))))
(check-false (trivial (list '(atom p) '(atom q))))
(check-false (trivial '()))
(check-true (trivial (list '(atom q) '(atom p) '(not (atom p)))))

;; ===== psubst (compound replacements, single simultaneous pass) =====
(check-equal? (psubst (hash 'p '(atom r)) '(and (atom p) (atom q))) '(and (atom r) (atom q)))
(check-equal? (psubst (hash 'p '(or (atom a) (atom b))) '(and (atom p) (atom q)))
              '(and (or (atom a) (atom b)) (atom q)))
;; atoms outside the substitution's domain are left untouched
(check-equal? (psubst (hash 'z '(atom w)) '(imp (atom p) (atom q))) '(imp (atom p) (atom q)))

;; ===== dual rejects ==> and <=> =====
(check-exn exn:fail? (λ () (dual '(imp (atom p) (atom q)))))
(check-exn exn:fail? (λ () (dual '(iff (atom p) (atom q)))))

;; ===== rawdnf preserves meaning (distribution is equivalence-preserving) =====
(define rd '(and (or (atom p) (atom q)) (or (atom r) (atom p))))
(check-true (tautology `(iff ,rd ,(rawdnf rd))))
