#lang racket/base

;; Unit tests for the LCF kernel (lcf.rkt), the derived propositional rules
;; (lcfprop.rkt), and the derived first-order rules (folderived.rkt): the
;; soundness side-conditions of the axiom schemes, the shape of every primitive
;; and derived theorem, and the printers.

(require rackunit)
(require "../lcf/lcf.rkt"
         "../lcf/lcfprop.rkt"
         "../lcf/folderived.rkt")
(require (only-in "../core/formulas.rkt" consequent antecedent))
(require (only-in "../prop/prop.rkt" tautology))

;; ===== occurs-in =====
(check-true (occurs-in '(var x) '(var x)))
(check-false (occurs-in '(var x) '(var y)))
(check-true (occurs-in '(var x) '(fn f (var x))))
(check-true (occurs-in '(var x) '(fn f (fn g (var x)))))
(check-false (occurs-in '(var x) '(fn f (var y) (var z))))
;; a whole subterm (not just a variable) can be tested for occurrence
(check-true (occurs-in '(fn g (var x)) '(fn f (fn g (var x)))))

;; ===== free-in (incl. the binding law) =====
(check-false (free-in '(var x) #t))
(check-false (free-in '(var x) #f))
(check-true (free-in '(var x) '(atom (rel P (var x)))))
(check-false (free-in '(var x) '(atom (rel P (var y)))))
;; quantifier binding the variable makes it not free
(check-false (free-in '(var x) '(forall x (atom (rel P (var x))))))
;; a quantifier over a different variable does not bind x
(check-true (free-in '(var x) '(exists y (atom (rel P (var x))))))
(check-true (free-in '(var x) '(and (atom (rel P (var x))) (atom (rel Q (var y))))))
(check-false (free-in '(var x) '(and (atom (rel P (var y))) (atom (rel Q (var z))))))

;; ===== modusponens =====
(check-equal? (modusponens '(imp (atom p) (atom q)) '(atom p)) '(atom q))
(check-equal? (modusponens '(imp (atom p) (imp (atom q) (atom r))) '(atom p))
              '(imp (atom q) (atom r)))
;; the supplied premise must equal the antecedent
(check-exn exn:fail? (λ () (modusponens '(imp (atom p) (atom q)) '(atom r))))
;; the major premise must itself be an implication
(check-exn exn:fail? (λ () (modusponens '(atom p) '(atom p))))

;; ===== gen =====
(check-equal? (gen 'x '(atom (rel P (var x)))) '(forall x (atom (rel P (var x)))))

;; ===== axiom schemes =====
(check-equal? (axiom-addimp '(atom p) '(atom q)) '(imp (atom p) (imp (atom q) (atom p))))
(check-equal? (axiom-distribimp '(atom p) '(atom q) '(atom r))
              '(imp (imp (atom p) (imp (atom q) (atom r)))
                    (imp (imp (atom p) (atom q)) (imp (atom p) (atom r)))))
(check-equal? (axiom-doubleneg '(atom p)) '(imp (imp (imp (atom p) #f) #f) (atom p)))
;; axiom-impall: valid only when x is not free in p
(check-equal? (axiom-impall 'x '(atom (rel P (var y))))
              '(imp (atom (rel P (var y))) (forall x (atom (rel P (var y))))))
(check-exn exn:fail? (λ () (axiom-impall 'x '(atom (rel P (var x))))))
;; axiom-existseq: valid only when x does not occur in the term
(check-equal? (axiom-existseq 'x '(fn c)) '(exists x (atom (rel = (var x) (fn c)))))
(check-exn exn:fail? (λ () (axiom-existseq 'x '(var x))))
(check-equal? (axiom-eqrefl '(var x)) '(atom (rel = (var x) (var x))))
(check-equal? (axiom-eqrefl '(fn f (var x))) '(atom (rel = (fn f (var x)) (fn f (var x)))))
;; funcong: a 0-ary function needs no hypotheses (just c = c)
(check-equal? (axiom-funcong 'f '() '()) '(atom (rel = (fn f) (fn f))))
(check-equal? (axiom-funcong 'f '((var x)) '((var y)))
              '(imp (atom (rel = (var x) (var y))) (atom (rel = (fn f (var x)) (fn f (var y))))))
;; two arguments produce a right-nested chain of two equality hypotheses
(check-equal? (axiom-funcong 'f '((var x) (var y)) '((var u) (var v)))
              '(imp (atom (rel = (var x) (var u)))
                    (imp (atom (rel = (var y) (var v)))
                         (atom (rel = (fn f (var x) (var y)) (fn f (var u) (var v)))))))
(check-equal? (axiom-predcong 'P '((var x)) '((var y)))
              '(imp (atom (rel = (var x) (var y)))
                    (imp (atom (rel P (var x))) (atom (rel P (var y))))))
(check-equal? (axiom-iffimp1 '(atom p) '(atom q))
              '(imp (iff (atom p) (atom q)) (imp (atom p) (atom q))))
(check-equal? (axiom-iffimp2 '(atom p) '(atom q))
              '(imp (iff (atom p) (atom q)) (imp (atom q) (atom p))))
(check-equal? (axiom-impiff '(atom p) '(atom q))
              '(imp (imp (atom p) (atom q)) (imp (imp (atom q) (atom p)) (iff (atom p) (atom q)))))

;; ===== printers =====
(check-equal? (term->string '(var x)) "x")
(check-equal? (term->string '(fn f)) "f")
(check-equal? (term->string '(fn f (var x) (var y))) "f(x,y)")
;; equality prints infix, ordinary predicates print prefix
(check-equal? (fol-atom->string 0 '(rel = (var x) (fn c))) "x = c")
(check-equal? (fol-atom->string 0 '(rel P (var x))) "P(x)")
(check-equal? (fol-atom->string 0 '(rel p)) "p")
(check-equal? (thm->string '(imp (atom (rel P (var x))) (atom (rel Q (var x))))) "|- P(x) ==> Q(x)")

;; ============================================================
;; lcfprop.rkt --- derived propositional rules
;; ============================================================

;; ===== literal? =====
(check-true (literal? '(atom (rel p))))
(check-true (literal? '(forall x (atom (rel P (var x))))))
(check-true (literal? '(imp (atom (rel p)) #f))) ; negated atom
(check-true (literal? '(imp (forall x (atom (rel P (var x)))) #f))) ; negated forall
(check-false (literal? '(and (atom (rel p)) (atom (rel q)))))
(check-false (literal? '(or (atom (rel p)) (atom (rel q)))))
(check-false (literal? '(exists x (atom (rel P (var x))))))
(check-false (literal? '(imp (atom (rel p)) (atom (rel q))))) ; not negation

;; ===== negatef / negativef =====
(check-equal? (negatef '(atom (rel p))) '(imp (atom (rel p)) #f))
(check-equal? (negatef '(imp (atom (rel p)) #f)) '(atom (rel p)))
(check-true (negativef '(imp (atom (rel p)) #f)))
(check-false (negativef '(atom (rel p))))

;; ===== imp-trans / imp-swap =====
;; from |- p->p and |- p->(q->p) we get |- p->(q->p)
(check-equal? (concl (imp-trans (imp-refl '(atom (rel p)))
                                (axiom-addimp '(atom (rel p)) '(atom (rel q)))))
              '(imp (atom (rel p)) (imp (atom (rel q)) (atom (rel p)))))
;; imp-swap exchanges the first two antecedents of a nested implication theorem
(check-equal? (concl (imp-swap (imp-refl '(imp (atom (rel p)) (imp (atom (rel q)) (atom (rel r)))))))
              '(imp (atom (rel p))
                    (imp (imp (atom (rel p)) (imp (atom (rel q)) (atom (rel r))))
                         (imp (atom (rel q)) (atom (rel r))))))

;; ===== and-left / and-right =====
(check-equal? (concl (and-left '(atom (rel p)) '(atom (rel q))))
              '(imp (and (atom (rel p)) (atom (rel q))) (atom (rel p))))
(check-equal? (concl (and-right '(atom (rel p)) '(atom (rel q))))
              '(imp (and (atom (rel p)) (atom (rel q))) (atom (rel q))))

;; ===== ex-falso (explosion) =====
(check-equal? (concl (ex-falso '(atom (rel p)))) '(imp #f (atom (rel p))))

;; ===== right-doubleneg =====
;; |- p -> ~~p  (built by swapping |- (p->#f) -> (p->#f))  yields  |- p -> p
(check-equal? (concl (right-doubleneg (imp-swap (imp-refl '(imp (atom (rel p)) #f)))))
              '(imp (atom (rel p)) (atom (rel p))))
(check-exn exn:fail? (λ () (right-doubleneg (imp-refl '(atom (rel p))))))

;; ===== contrapos =====
;; |- p->p  contraposes to  |- ~p -> ~p
(check-equal? (concl (contrapos (imp-refl '(atom (rel p)))))
              '(imp (not (atom (rel p))) (not (atom (rel p)))))

;; ===== expand-connective: each expansion is a propositional tautology =====
;; (the iff between a connective and its definition holds by truth tables)
(check-true (tautology (concl (expand-connective #t))))
(check-true (tautology (concl (expand-connective '(not (atom p))))))
(check-true (tautology (concl (expand-connective '(and (atom p) (atom q))))))
(check-true (tautology (concl (expand-connective '(or (atom p) (atom q))))))
(check-true (tautology (concl (expand-connective '(iff (atom p) (atom q))))))
(check-exn exn:fail? (λ () (expand-connective '(atom p)))) ; not a connective

;; ============================================================
;; folderived.rkt --- derived first-order rules
;; ============================================================

;; ===== eq-sym / eq-trans =====
(check-equal? (concl (eq-sym '(fn a) '(fn b)))
              '(imp (atom (rel = (fn a) (fn b))) (atom (rel = (fn b) (fn a)))))
(check-equal? (concl (eq-trans '(fn a) '(fn b) '(fn c)))
              '(imp (atom (rel = (fn a) (fn b)))
                    (imp (atom (rel = (fn b) (fn c))) (atom (rel = (fn a) (fn c))))))

;; ===== ispec / spec =====
(check-equal? (concl (ispec '(fn c) '(forall x (atom (rel P (var x))))))
              '(imp (forall x (atom (rel P (var x)))) (atom (rel P (fn c)))))
(check-exn exn:fail? (λ () (ispec '(fn c) '(atom (rel P (var x)))))) ; non-universal
;; spec specialises a *universal theorem* (gen gives a genuine forall conclusion)
(check-equal? (concl (spec '(fn c) (gen 'x (imp-refl '(atom (rel P (var x)))))))
              '(imp (atom (rel P (fn c))) (atom (rel P (fn c)))))

;; ===== alpha =====
(check-equal? (concl (alpha 'y '(forall x (atom (rel P (var x))))))
              '(imp (forall x (atom (rel P (var x)))) (forall y (atom (rel P (var y))))))

;; ===== icongruence =====
;; identical subterms: only the trivial equality hypothesis is added
(check-equal? (concl (icongruence '(fn a) '(fn b) '(fn a) '(fn b)))
              '(imp (atom (rel = (fn a) (fn b))) (atom (rel = (fn a) (fn b)))))
;; congruence propagates through a function symbol
(check-equal? (concl (icongruence '(fn a) '(fn b) '(fn f (fn a)) '(fn f (fn b))))
              '(imp (atom (rel = (fn a) (fn b))) (atom (rel = (fn f (fn a)) (fn f (fn b))))))

;; ===== genimp =====
;; |- p->q  generalises to  |- (forall x. p) -> (forall x. q)
(check-equal? (concl (genimp 'x (imp-refl '(atom (rel P (var x))))))
              '(imp (forall x (atom (rel P (var x)))) (forall x (atom (rel P (var x))))))

;; ===== isubst =====
;; substituting s=t inside an atom uses predicate congruence
(check-equal? (concl (isubst '(fn a) '(fn b) '(atom (rel P (fn a))) '(atom (rel P (fn b)))))
              '(imp (atom (rel = (fn a) (fn b))) (imp (atom (rel P (fn a))) (atom (rel P (fn b))))))
;; identical formulas: only the equality assumption is added (no structural work)
(check-equal? (concl (isubst '(fn a) '(fn b) '(atom (rel P (var z))) '(atom (rel P (var z)))))
              '(imp (atom (rel = (fn a) (fn b))) (imp (atom (rel P (var z))) (atom (rel P (var z))))))
