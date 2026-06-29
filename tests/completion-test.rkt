#lang racket/base

(require rackunit)
(require "../equality/completion.rkt"
         "../equality/eqelim.rkt"
         "../equality/paramodulation.rkt"
         "../fol/skolems.rkt")
(require (only-in "../equality/rewrite.rkt" rewrite))
(require (only-in "../equality/equal.rkt" mk-eq is-eq))
(require (only-in "../equality/order.rkt" lpo-ge weight))
(require (only-in "../fol/fol.rkt" fv))
(require (only-in "../core/lib.rkt" intersect))

(define (all-true? l)
  (andmap (λ (x) (eq? x #t)) l))
(define (all-nat? l)
  (andmap exact-nonnegative-integer? l))

;; ===== Knuth-Bendix completion of group theory =====
(define group-eqs
  (list '(atom (rel = (fn * (fn * (var x) (var y)) (var z)) (fn * (var x) (fn * (var y) (var z)))))
        '(atom (rel = (fn * (fn |1|) (var x)) (var x)))
        '(atom (rel = (fn * (fn i (var x)) (var x)) (fn |1|)))))
(define group-rules (complete-and-simplify '(|1| * i) group-eqs))
(check-pred list? group-rules)
(check-true (>= (length group-rules) 3))
;; the completed system proves standard group identities by rewriting
(check-equal? (rewrite group-rules '(fn i (fn |1|))) '(fn |1|)) ; i(1) = 1
(check-equal? (rewrite group-rules '(fn i (fn i (var x)))) '(var x)) ; i(i(x)) = x

;; ===== equality reasoning: symmetry a = b ==> b = a =====
(define sym '(imp (atom (rel = (var a) (var b))) (atom (rel = (var b) (var a)))))
(check-true (all-true? (paramodulation sym)))
(check-pred all-nat? (bmeson sym))
(check-pred all-nat? (emeson sym))

;; ===== Skolemizing a set of formulas at once =====
(define sk (skolemizes (list '(exists x (atom (rel P (var x)))) '(exists y (atom (rel Q (var y)))))))
(check-equal? (length sk) 2)

;; ===== completion: renamepair makes the two equations variable-disjoint =====
(let-values ([(a b) (renamepair '(atom (rel = (var x) (var y))) '(atom (rel = (var x) (var z))))])
  (check-true (null? (intersect (fv a) (fv b))))
  (check-equal? (length (fv a)) 2)
  (check-equal? (length (fv b)) 2))

;; ===== completion: normalize-and-orient orients an equation by the ordering =====
(define ord (λ (s t) (lpo-ge (λ (p q) (weight '(c f g x y) p q)) s t)))
(let-values ([(l r) (normalize-and-orient ord '() '(atom (rel = (fn f (var x)) (var x))))])
  (check-equal? l '(fn f (var x)))
  (check-equal? r '(var x))
  (check-true (ord l r))) ; the result always respects the ordering
;; f(x) = g(y) is orientable in neither direction (disjoint variables) -> error
(check-exn #rx"normalize-and-orient"
           (λ () (normalize-and-orient ord '() '(atom (rel = (fn f (var x)) (fn g (var y)))))))

;; ===== completion: critical-pairs returns a list of equations =====
(let ([cps (critical-pairs '(atom (rel = (fn f (var x)) (var x)))
                           '(atom (rel = (fn f (var x)) (var x))))])
  (check-pred list? cps)
  (check-true (andmap is-eq cps)))

;; ===== completion: interreduce never grows the equation set =====
(define ir-eqs (list (mk-eq '(fn f (fn f (var x))) '(fn f (var x))) (mk-eq '(fn f (var x)) '(var x))))
(check-true (<= (length (interreduce '() ir-eqs)) (length ir-eqs)))

;; ===== completion: complete with no pending critical pairs is a no-op =====
(check-equal? (complete ord (list (list (mk-eq '(fn f (fn f (var x))) '(fn f (var x)))) '() '()))
              (list (mk-eq '(fn f (fn f (var x))) '(fn f (var x)))))

;; ===== eqelim: list-find returns the first match, or raises =====
(check-equal? (list-find (λ (x) (= x 3)) '(1 2 3 4)) 3)
(check-exn #rx"list-find" (λ () (list-find (λ (x) (= x 5)) '(1 2 3))))

;; ===== eqelim: Brand's S modification symmetrizes equations =====
;; one equation s=t yields two clauses, {s=t} and {t=s}
(check-equal? (modify-S (list (mk-eq '(var x) '(var y))))
              (list (list (mk-eq '(var x) '(var y))) (list (mk-eq '(var y) '(var x)))))
;; a clause with no equation passes through unchanged (wrapped as a single clause)
(check-equal? (modify-S (list '(atom (rel P (var x))))) (list (list '(atom (rel P (var x))))))

;; ===== eqelim: Brand's T modification flattens equation right-hand sides =====
;; x = f(y)  becomes  (not f(y)=w), x=w   with a fresh variable w
(check-equal? (modify-T (list '(atom (rel = (var x) (fn f (var y))))))
              (list '(not (atom (rel = (fn f (var y)) (var w)))) '(atom (rel = (var x) (var w)))))
;; a non-equation literal is untouched
(check-equal? (modify-T (list '(atom (rel P (var x))))) (list '(atom (rel P (var x)))))

;; ===== eqelim: E modification abstracts non-variable subterms =====
;; P(f(x)) abstracts f(x) into a fresh w, recording the side condition (not f(x)=w)
(check-equal? (modify-E (list '(atom (rel P (fn f (var x))))))
              (list '(not (atom (rel = (fn f (var x)) (var w)))) '(atom (rel P (var w)))))

;; ===== eqelim: the Brand transformation always prepends a reflexivity clause =====
(check-equal? (car (brand (list (list (mk-eq '(var x) '(var y)))))) (list (mk-eq '(var x) '(var x))))

;; ===== eqelim: bmeson/emeson prove transitivity and congruence of equality =====
(define trans
  '(imp (and (atom (rel = (var x) (var y))) (atom (rel = (var y) (var z))))
        (atom (rel = (var x) (var z)))))
(define cong-thm '(imp (atom (rel = (var x) (var y))) (atom (rel = (fn f (var x)) (fn f (var y))))))
(check-pred all-nat? (bmeson trans))
(check-pred all-nat? (bmeson cong-thm))
(check-pred all-nat? (emeson trans))
(check-pred all-nat? (emeson cong-thm))

;; ===== paramodulation: overlapl rewrites inside a (possibly negated) literal =====
;; a = b applied to (not P(a)) yields (not P(b)); rfn receives (subst . rebuilt-literal)
(check-equal? (overlapl (cons '(fn a) '(fn b)) '(not (atom (rel P (fn a)))) (λ (i p) p))
              (list '(not (atom (rel P (fn b))))))
;; a non-literal is rejected
(check-exn #rx"overlapl" (λ () (overlapl (cons '(fn a) '(fn b)) '(and #t #f) (λ (i p) p))))

;; ===== paramodulation: paramodulate rewrites a clause using another's equations =====
(check-equal? (paramodulate (list (mk-eq '(fn a) '(fn b))) (list '(atom (rel P (fn a)))))
              (list (list '(atom (rel P (fn b))))))
;; a clause with no equation produces no paramodulants
(check-equal? (paramodulate (list '(atom (rel P (var x)))) (list '(atom (rel Q (var x))))) '())
;; para-clauses applies paramodulation in both directions, so it yields results
(check-true (pair? (para-clauses (list (mk-eq '(fn a) '(fn b))) (list '(atom (rel P (fn a)))))))

;; ===== paramodulation: pure-paramodulation refutes a negated tautology =====
;; the always-present reflexivity clause x=x lets it refute (not c=c)
(check-true (pure-paramodulation '(not (atom (rel = (fn c) (fn c))))))

;; ===== paramodulation proves the equality axioms (refl/trans/congruence) =====
(check-true (all-true? (paramodulation '(forall x (atom (rel = (var x) (var x)))))))
(check-true (all-true? (paramodulation trans)))
(check-true (all-true? (paramodulation cong-thm)))
