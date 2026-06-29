#lang racket/base

;; Property tests for the LCF kernel and derived rules: occurs-in/free-in agree
;; with an independent structural oracle, the axiom-scheme side-conditions hold
;; exactly when their variable conditions do, modusponens is faithful, the
;; negation encoding is involutive, and connective expansions are tautologies.

(require rackunit
         rackcheck
         racket/match
         (only-in racket/list append-map)
         "common.rkt")
(require (only-in "../../prop/prop.rkt" tautology))
(require (only-in "../../lcf/lcf.rkt"
                  concl
                  occurs-in
                  free-in
                  modusponens
                  axiom-impall
                  axiom-existseq))
(require (only-in "../../lcf/lcfprop.rkt" negatef negativef literal? expand-connective imp-refl))
(require (only-in "../../lcf/folderived.rkt" eq-trans isubst genimp))

;; ===== local generators: genuine first-order formulas over rel-atoms =====
(define fo-atom-gen
  (gen:map (gen:tuple (gen:one-of '(P Q)) (term-gen 1) (term-gen 1))
           (λ (t) `(atom (rel ,(car t) ,(cadr t) ,(caddr t))))))
(define (fo-prop-gen n)
  (if (<= n 0)
      fo-atom-gen
      (gen:frequency (list (cons 2 fo-atom-gen)
                           (cons 1 (gen:map (fo-prop-gen (sub1 n)) (λ (p) `(not ,p))))
                           (cons 2 (binop-gen '(and or imp iff) fo-prop-gen n))
                           (cons 2 (quant-gen '(forall exists) '(x y z) fo-prop-gen n))))))

;; ===== occurs-in: agrees with an independent subterm collector =====
(define (subterms t)
  (cons t
        (match t
          [`(var ,_) '()]
          [`(fn ,_ ,@args) (append-map subterms args)])))
(check-property big
                (property ([s gen:term] [t gen:term])
                          (eq? (occurs-in s t) (and (member s (subterms t)) #t))))

;; ===== free-in over an atom = some argument contains the variable =====
(check-property big
                (property ([x (gen:one-of '(x y z))] [a gen:term] [b gen:term])
                          (eq? (free-in `(var ,x) `(atom (rel P ,a ,b)))
                               (or (occurs-in `(var ,x) a) (occurs-in `(var ,x) b)))))

;; ===== binding law: a variable bound by its own quantifier is never free =====
(check-property big
                (property ([p (fo-prop-gen 3)] [x (gen:one-of '(x y z))])
                          (and (not (free-in `(var ,x) `(forall ,x ,p)))
                               (not (free-in `(var ,x) `(exists ,x ,p))))))

;; ===== no shadowing: a quantifier over y /= x does not affect free-in of x =====
(check-property
 big
 (property ([p (fo-prop-gen 3)] [xy (gen:one-of '((x y) (y z) (x z) (y x) (z x) (z y)))])
           (equal? (free-in `(var ,(car xy)) `(forall ,(cadr xy) ,p)) (free-in `(var ,(car xy)) p))))

;; ===== modusponens: returns the consequent exactly when the premise matches =====
(check-property big (property ([p gen:prop] [q gen:prop]) (equal? (modusponens `(imp ,p ,q) p) q)))
(check-property big
                (property ([p gen:prop] [q gen:prop] [r gen:prop])
                          (or (equal? r p)
                              (with-handlers ([exn:fail? (λ (e) #t)])
                                (modusponens `(imp ,p ,q) r)
                                #f))))

;; ===== axiom-impall succeeds iff x is not free in p =====
(check-property big
                (property ([p (fo-prop-gen 3)] [x (gen:one-of '(x y z))])
                          (define free (and (free-in `(var ,x) p) #t))
                          (define ok
                            (with-handlers ([exn:fail? (λ (e) #f)])
                              (axiom-impall x p)
                              #t))
                          (eq? ok (not free))))

;; ===== axiom-existseq succeeds iff x does not occur in the term =====
(check-property big
                (property ([t gen:term] [x (gen:one-of '(x y z))])
                          (define occ (and (occurs-in `(var ,x) t) #t))
                          (define ok
                            (with-handlers ([exn:fail? (λ (e) #f)])
                              (axiom-existseq x t)
                              #t))
                          (eq? ok (not occ))))

;; ===== negatef negates; negating a non-negative formula is negative =====
;; negatef is involutive only up to logical equivalence, not structurally: on a
;; double negation (imp (imp r #f) #f) it strips BOTH layers to r rather than
;; rebuilding ¬¬r, so we check the meaning is preserved, not the syntax.
(check-property big (property ([fm gen:prop]) (tautology `(iff ,(negatef (negatef fm)) ,fm))))
(check-property big
                (property ([fm gen:prop])
                          (if (negativef fm)
                              #t
                              (negativef (negatef fm)))))

;; ===== literal? = atom/forall, possibly under a single negation =====
(define (atom-or-forall? p)
  (match p
    [`(atom ,_) #t]
    [`(forall ,_ ,_) #t]
    [_ #f]))
(check-property big
                (property ([fm gen:prop])
                          (eq? (literal? fm)
                               (or (atom-or-forall? fm)
                                   (and (negativef fm) (atom-or-forall? (negatef fm)))))))

;; ===== expand-connective yields a propositional tautology =====
(define conn-gen
  (gen:choice (gen:const #t)
              (gen:map gen:small-prop (λ (p) `(not ,p)))
              (gen:map (gen:tuple gen:small-prop gen:small-prop) (λ (pq) `(and ,(car pq) ,(cadr pq))))
              (gen:map (gen:tuple gen:small-prop gen:small-prop) (λ (pq) `(or ,(car pq) ,(cadr pq))))
              (gen:map (gen:tuple gen:small-prop gen:small-prop)
                       (λ (pq) `(iff ,(car pq) ,(cadr pq))))))
(check-property mid (property ([fm conn-gen]) (tautology (concl (expand-connective fm)))))

;; ===== derived first-order rule shapes =====
(check-property big
                (property ([s gen:term] [t gen:term] [u gen:term])
                          (equal? (concl (eq-trans s t u))
                                  `(imp (atom (rel = ,s ,t))
                                        (imp (atom (rel = ,t ,u)) (atom (rel = ,s ,u)))))))
;; isubst on identical formulas adds only the equality hypothesis
(check-property big
                (property ([s gen:term] [t gen:term] [fm gen:prop])
                          (equal? (concl (isubst s t fm fm))
                                  `(imp (atom (rel = ,s ,t)) (imp ,fm ,fm)))))
;; genimp turns |- p->p into |- (forall x.p)->(forall x.p)
(check-property big
                (property ([p gen:prop] [x (gen:one-of '(x y z))])
                          (equal? (concl (genimp x (imp-refl p)))
                                  `(imp (forall ,x ,p) (forall ,x ,p)))))
