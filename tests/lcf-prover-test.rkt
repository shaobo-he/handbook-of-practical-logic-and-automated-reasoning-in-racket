#lang racket/base

;; Unit tests for the LCF first-order prover (lcffol.rkt) and the goal/tactic
;; layer (tactics.rkt): parity-aware quantifier extraction, Skolem-function
;; generation, complementary-literal unification, alpha-aware matching, and the
;; sub-goal behaviour of the structural tactics plus end-to-end tactic proofs.

(require rackunit)
(require "../lcf/lcf.rkt"
         "../lcf/lcfprop.rkt"
         "../lcf/folderived.rkt"
         "../lcf/lcffol.rkt"
         "../lcf/tactics.rkt")
(require (only-in "../core/formulas.rkt" consequent))

;; ===== quantforms: parity-aware quantifier extraction =====
;; positive (e = #f means "negative polarity"): a top-level forall is collected
;; when reached at negative polarity (e = #f)
(check-equal? (quantforms #f '(forall x (atom (rel P (var x))))) '((forall x (atom (rel P (var x))))))
(check-equal? (quantforms #t '(forall x (atom (rel P (var x))))) '())
;; negation flips polarity: a forall under not is positive (seen by e = #t)
(check-equal? (quantforms #t '(not (forall x (atom (rel P (var x))))))
              '((forall x (atom (rel P (var x))))))
(check-equal? (quantforms #f '(not (forall x (atom (rel P (var x)))))) '())
;; exists is collected at positive polarity
(check-equal? (quantforms #t '(exists x (atom (rel P (var x))))) '((exists x (atom (rel P (var x))))))
(check-false (and (member '(forall x (atom (rel P (var x))))
                          (quantforms #t '(forall x (atom (rel P (var x))))))
                  #t))
;; imp p q is treated as (or (not p) q): the antecedent's polarity flips
(let ([qs (quantforms #t '(imp (forall x (atom (rel P (var x)))) (exists y (atom (rel Q (var y))))))])
  (check-equal? (length qs) 2)
  (check-true (and (member '(forall x (atom (rel P (var x)))) qs) #t))
  (check-true (and (member '(exists y (atom (rel Q (var y)))) qs) #t)))

;; ===== skolemfuns =====
;; one existential -> one Skolem entry; the key is the negated universal form and
;; the value is a constant Skolem term f_1 (the existential body is closed)
(check-equal? (skolemfuns '(exists x (atom (rel P (var x)))))
              '(((forall x (not (atom (rel P (var x))))) fn f_1)))
;; two existentials -> two entries with distinct function names
(let ([sk (skolemfuns '(exists x (and (atom (rel P (var x))) (exists y (atom (rel Q (var y)))))))])
  (check-equal? (length sk) 2)
  ;; the Skolem function symbols are distinct
  (define names (map (λ (e) (cadr (cdr e))) sk))
  (check-equal? names '(f_1 f_2)))

;; ===== unify-complementsf =====
;; an atom against its negation with a unifiable argument binds the variable
(let ([env (unify-complementsf (hash)
                               (cons '(atom (rel P (var x))) '(imp (atom (rel P (fn a))) #f)))])
  (check-equal? (hash-ref env 'x) '(fn a)))
;; identical complementary literals need no binding
(check-equal? (unify-complementsf (hash)
                                  (cons '(atom (rel P (fn a))) '(imp (atom (rel P (fn a))) #f)))
              (hash))
;; different predicates are not complementary -> error
(check-exn
 exn:fail?
 (λ () (unify-complementsf (hash) (cons '(atom (rel P (fn a))) '(imp (atom (rel Q (fn b))) #f)))))
;; two positive literals are not complementary -> error
(check-exn exn:fail?
           (λ () (unify-complementsf (hash) (cons '(atom (rel P (fn a))) '(atom (rel P (fn a)))))))

;; ===== form-match (one-directional, alpha-safe under same bound name) =====
;; a free pattern variable is bound while the bound variable is matched modulo
;; a fresh renaming
(let ([env (form-match (cons '(forall x (atom (rel P (var x) (var w))))
                             '(forall x (atom (rel P (var x) (fn a)))))
                       (hash))])
  (check-equal? (hash-ref env 'w) '(fn a)))
;; identical formulas match and leave the environment unchanged
(check-equal? (form-match (cons '(atom (rel P (fn a))) '(atom (rel P (fn a)))) (hash)) (hash))
;; structural mismatch -> error
(check-exn exn:fail? (λ () (form-match (cons '(atom (rel P (fn a))) '(atom (rel Q (fn b)))) (hash))))

;; ===== lcffol on valid formulas (concl equals the goal) =====
;; only run on KNOWN-VALID inputs: lcffol loops on non-theorems (semi-decidable)
(check-equal? (concl (lcffol '(imp (atom (rel p)) (atom (rel p)))))
              '(imp (atom (rel p)) (atom (rel p))))
(define peirce '(imp (imp (imp (atom (rel p)) (atom (rel q))) (atom (rel p))) (atom (rel p))))
(check-equal? (concl (lcffol peirce)) peirce)
;; universal instantiation is first-order valid
(check-equal? (concl (lcffol '(imp (forall x (atom (rel P (var x)))) (atom (rel P (fn c))))))
              '(imp (forall x (atom (rel P (var x)))) (atom (rel P (fn c)))))

;; ============================================================
;; tactics.rkt --- structural tactics and end-to-end proofs
;; ============================================================

;; ===== conj-intro-tac: (and p q) -> two subgoals p and q, same assumptions =====
(let ([g (conj-intro-tac (set-goal '(and (atom (rel p)) (atom (rel q)))))])
  (check-equal? (length (goals-gls g)) 2)
  (check-equal? (map cdr (goals-gls g)) '((atom (rel p)) (atom (rel q))))
  (check-equal? (map car (goals-gls g)) '(() ())))

;; ===== imp-intro-tac: (imp p q) -> assume p (labelled), goal becomes q =====
(let ([g (imp-intro-tac "h" (set-goal '(imp (atom (rel p)) (atom (rel q)))))])
  (check-equal? (length (goals-gls g)) 1)
  (check-equal? (cdr (car (goals-gls g))) '(atom (rel q)))
  (check-equal? (car (car (goals-gls g))) '(("h" atom (rel p)))))

;; ===== exists-intro-tac: (exists x p) with witness t -> goal p[x:=t] =====
(let ([g (exists-intro-tac '(fn a) (set-goal '(exists x (atom (rel P (var x))))))])
  (check-equal? (length (goals-gls g)) 1)
  (check-equal? (cdr (car (goals-gls g))) '(atom (rel P (fn a)))))

;; ===== forall-intro-tac error: chosen variable already free in the goal =====
(check-exn exn:fail?
           (λ () (forall-intro-tac 'y (set-goal '(forall x (atom (rel P (var x) (var y))))))))

;; ===== disj-elim-tac: an assumed disjunction splits into two case subgoals =====
(let* ([g0 (imp-intro-tac "h" (set-goal '(imp (or (atom (rel p)) (atom (rel q))) (atom (rel r)))))]
       [g1 (disj-elim-tac "c" '(or (atom (rel p)) (atom (rel q))) by '("h") g0)])
  (check-equal? (length (goals-gls g1)) 2)
  ;; both branches keep the original conclusion r ...
  (check-equal? (map cdr (goals-gls g1)) '((atom (rel r)) (atom (rel r))))
  ;; ... and each gains the disjunct under label "c"
  (check-equal? (car (car (car (goals-gls g1)))) '("c" atom (rel p)))
  (check-equal? (car (car (cadr (goals-gls g1)))) '("c" atom (rel q))))

;; ===== exists-elim-tac: introduce a witness variable into the assumptions =====
(let* ([g0 (imp-intro-tac "h" (set-goal '(imp (exists x (atom (rel P (var x)))) (atom (rel Q)))))]
       [g1 (exists-elim-tac "h1" '(exists x (atom (rel P (var x)))) by '("h") g0)])
  (check-equal? (length (goals-gls g1)) 1)
  (check-equal? (cdr (car (goals-gls g1))) '(atom (rel Q)))
  (check-true (and (member '("h1" atom (rel P (var x))) (car (car (goals-gls g1)))) #t)))

;; ===== end-to-end tactic proofs (prove returns a theorem of the goal) =====
;; disjunction commutativity via disj-elim
(define disj-goal '(imp (or (atom (rel p)) (atom (rel q))) (or (atom (rel q)) (atom (rel p)))))
(check-equal?
 (concl (prove disj-goal
               (list (λ (g) (imp-intro-tac "h" g))
                     (λ (g) (disj-elim-tac "c" '(or (atom (rel p)) (atom (rel q))) by '("h") g))
                     (λ (g) (auto-tac by '("c") g))
                     (λ (g) (auto-tac by '("c") g)))))
 disj-goal)

;; lemma introduction via lemma-tac
(define lem-goal '(imp (atom (rel p)) (atom (rel p))))
(check-equal? (concl (prove lem-goal
                            (list (λ (g) (imp-intro-tac "h" g))
                                  (λ (g) (lemma-tac "lem" '(atom (rel p)) by '("h") g))
                                  (λ (g) (auto-tac by '("lem") g)))))
              lem-goal)
