#lang racket/base

;; tactics --- a goal/tactic interactive proof system on the LCF kernel,
;; plus a small declarative-proof (Mizar-style) layer.
;;
;; A goal bundles a list of subgoals (each (assumptions . conclusion)) with a
;; justification turning subgoal theorems into the overall theorem.

(require racket/match)
(require (only-in "../core/lib.rkt" funpow update undefined))
(require (only-in "../core/formulas.rkt"
                  dest-imp
                  dest-and
                  antecedent
                  consequent
                  mk-imp
                  mk-and
                  list-conj
                  end-itlist))
(require (only-in "../fol/fol.rkt" subst fv))
(require "lcf.rkt")
(require "lcfprop.rkt")
(require "folderived.rkt")
(require "lcffol.rkt")

(provide (all-defined-out))

(struct goals (gls jfn) #:transparent)

;; ===== setting up and finishing goals =====
(define (set-goal p)
  (define (chk th)
    (if (equal? (concl th) p)
        th
        (error 'set-goal "wrong theorem")))
  (goals (list (cons '() p)) (λ (ths) (chk (modusponens (car ths) truth)))))

(define (extract-thm gls)
  (match gls
    [(goals '() jfn) (jfn '())]
    [_ (error 'extract-thm "unsolved goals")]))

(define (tac-proof g prf)
  (extract-thm (foldl (λ (t acc) (t acc)) g prf)))
(define (prove p prf)
  (tac-proof (set-goal p) prf))

;; ===== structural tactics =====
(define (conj-intro-tac g)
  (match-define (goals (cons (cons asl `(and ,p ,q)) gls) jfn) g)
  (define (jfn* ths)
    (match-define `(,thp ,thq . ,rest) ths)
    (jfn (cons (imp-trans-chain (list thp thq) (and-pair p q)) rest)))
  (goals (cons (cons asl p) (cons (cons asl q) gls)) jfn*))

(define (jmodify jfn tfn)
  (λ (ths)
    (match-define `(,th . ,oths) ths)
    (jfn (cons (tfn th) oths))))

(define (gen-right-alpha y x th)
  (define th1 (gen-right y th))
  (imp-trans th1 (alpha x (consequent (concl th1)))))

(define (forall-intro-tac y g)
  (match-define (goals (cons (cons asl (and fm `(forall ,x ,p))) gls) jfn) g)
  (if (or (member y (fv fm)) (ormap (λ (lp) (member y (fv (cdr lp)))) asl))
      (error 'forall-intro-tac "variable already free in goal")
      (goals (cons (cons asl (subst (update x `(var ,y) undefined) p)) gls)
             (jmodify jfn (λ (th) (gen-right-alpha y x th))))))

(define (right-exists x t p)
  (define th (contrapos (ispec t `(forall ,x (not ,p)))))
  (define p*
    (match (antecedent (concl th))
      [`(not (not ,p2)) p2]))
  (end-itlist imp-trans
              (list (imp-contr p* #f)
                    (imp-add-concl #f (iff-imp1 (axiom-not p*)))
                    (iff-imp2 (axiom-not `(not ,p*)))
                    th
                    (iff-imp2 (axiom-exists x p)))))

(define (exists-intro-tac t g)
  (match-define (goals (cons (cons asl `(exists ,x ,p)) gls) jfn) g)
  (goals (cons (cons asl (subst (update x t undefined) p)) gls)
         (jmodify jfn (λ (th) (imp-trans th (right-exists x t p))))))

(define (imp-intro-tac s g)
  (match-define (goals (cons (cons asl `(imp ,p ,q)) gls) jfn) g)
  (define jmod
    (if (null? asl)
        (λ (th) (add-assum #t th))
        (λ (th) (imp-swap (shunt th)))))
  (goals (cons (cons (cons (cons s p) asl) q) gls) (jmodify jfn jmod)))

;; ===== assumptions and justification =====
(define (assumptate g th)
  (match-define (goals (cons (cons asl w) gls) jfn) g)
  (add-assum (list-conj (map cdr asl)) th))

(define (firstassum asl)
  (define p (cdr (car asl)))
  (if (null? (cdr asl))
      (imp-refl p)
      (and-left p (list-conj (map cdr (cdr asl))))))

(define (using ths p g)
  (map (λ (th) (assumptate g (foldr (λ (v acc) (gen v acc)) th (fv (concl th))))) ths))

(define (assumps asl)
  (match asl
    ['() '()]
    [`((,l . ,p)) (list (cons l (imp-refl p)))]
    [`((,l . ,p) . ,lps)
     (define ths (assumps lps))
     (define q (antecedent (concl (cdr (car ths)))))
     (define rth (and-right p q))
     (cons (cons l (and-left p q)) (map (λ (lth) (cons (car lth) (imp-trans rth (cdr lth)))) ths))]))

(define (by hyps p g)
  (match-define (goals (cons (cons asl w) gls) jfn) g)
  (define ths (assumps asl))
  (map (λ (s) (cdr (assoc s ths))) hyps))

(define (justify byfn hyps p g)
  (define ths (byfn hyps p g))
  (cond
    [(and (= (length ths) 1) (equal? (consequent (concl (car ths))) p)) (car ths)]
    [else
     (define th (lcffol (foldr (λ (t acc) (mk-imp (consequent (concl t)) acc)) p ths)))
     (if (null? ths)
         (assumptate g th)
         (imp-trans-chain ths th))]))

(define (proof tacs p g)
  (match-define (goals (cons (cons asl w) gls) jfn) g)
  (list (tac-proof (goals (list (cons asl p)) (λ (ths) (car ths))) tacs)))

;; the empty justification ("at once")
(define once '())
(define (at hyps p g)
  '())

(define (auto-tac byfn hyps g)
  (match-define (goals (cons (cons asl w) gls) jfn) g)
  (define th (justify byfn hyps w g))
  (goals gls (λ (ths) (jfn (cons th ths)))))

(define (lemma-tac s p byfn hyps g)
  (match-define (goals (cons (cons asl w) gls) jfn) g)
  (define (tr th)
    (imp-trans (justify byfn hyps p g) th))
  (define mfn
    (if (null? asl)
        tr
        (λ (th) (imp-unduplicate (tr (shunt th))))))
  (goals (cons (cons (cons (cons s p) asl) w) gls) (jmodify jfn mfn)))

(define (exists-elim-tac l fm byfn hyps g)
  (match-define (goals (cons (cons asl w) gls) jfn) g)
  (match-define `(exists ,x ,p) fm)
  (if (ormap (λ (f) (member x (fv f))) (cons w (map cdr asl)))
      (error 'exists-elim-tac "variable free in assumptions")
      (let ()
        (define th (justify byfn hyps fm g))
        (define (jfn* pth)
          (imp-unduplicate (imp-trans th (exists-left x (shunt pth)))))
        (goals (cons (cons (cons (cons l p) asl) w) gls) (jmodify jfn jfn*)))))

(define (ante-disj th1 th2)
  (match-define `(,p . ,r) (dest-imp (concl th1)))
  (match-define `(,q . ,s) (dest-imp (concl th2)))
  (define th3 (imp-trans-chain (map contrapos (list th1 th2)) (and-pair `(not ,p) `(not ,q))))
  (define th4 (contrapos (imp-trans (iff-imp2 (axiom-not r)) th3)))
  (define th5 (imp-trans (iff-imp1 (axiom-or p q)) th4))
  (right-doubleneg (imp-trans th5 (iff-imp1 (axiom-not `(imp ,r #f))))))

(define (disj-elim-tac l fm byfn hyps g)
  (match-define (goals (cons (cons asl w) gls) jfn) g)
  (define th (justify byfn hyps fm g))
  (match-define `(or ,p ,q) fm)
  (define (jfn* ths)
    (match-define `(,pth ,qth . ,rest) ths)
    (jfn (cons (imp-unduplicate (imp-trans th (ante-disj (shunt pth) (shunt qth)))) rest)))
  (goals (cons (cons (cons (cons l p) asl) w) (cons (cons (cons (cons l q) asl) w) gls)) jfn*))

;; ===== declarative layer =====
(define (multishunt i th)
  (define th1 (imp-swap (funpow i (λ (t) (imp-swap (shunt t))) th)))
  (imp-swap (funpow (- i 1) (λ (t) (unshunt (imp-front 2 t))) th1)))

(define (assume lps g)
  (match-define (goals (cons (cons asl `(imp ,p ,q)) gls) jfn) g)
  (if (not (equal? (end-itlist mk-and (map cdr lps)) p))
      (error 'assume "assume")
      (goals (cons (cons (append lps asl) q) gls)
             (jmodify jfn
                      (λ (th)
                        (if (null? asl)
                            (add-assum #t th)
                            (multishunt (length lps) th)))))))

(define (note lp)
  (lemma-tac (car lp) (cdr lp)))
(define (have p)
  (note (cons "" p)))
(define (so tac arg byfn)
  (tac arg
       (λ (hyps p g)
         (match-define (goals (cons (cons asl w) _) _) g)
         (cons (firstassum asl) (byfn hyps p g)))))
(define fix forall-intro-tac)
(define (consider xp)
  (exists-elim-tac "" `(exists ,(car xp) ,(cdr xp))))
(define take exists-intro-tac)
(define (cases fm byfn hyps g)
  (disj-elim-tac "" fm byfn hyps g))

(define (conclude p byfn hyps g)
  (match-define (goals (cons (cons asl w) gls) jfn) g)
  (define th (justify byfn hyps p g))
  (if (equal? p w)
      (goals (cons (cons asl #t) gls) (jmodify jfn (λ (_) th)))
      (let ()
        (match-define `(,p* . ,q) (dest-and w))
        (if (not (equal? p* p))
            (error 'conclude "bad conclusion")
            (goals (cons (cons asl q) gls)
                   (jmodify jfn (λ (th2) (imp-trans-chain (list th th2) (and-pair p q)))))))))

(define (our thesis byfn hyps g)
  (match-define (goals (cons (cons asl w) gls) jfn) g)
  (conclude w byfn hyps g))
(define thesis "")

(define (qed g)
  (match-define (goals (cons (cons asl w) gls) jfn) g)
  (if (equal? w #t)
      (goals gls (λ (ths) (jfn (cons (assumptate g truth) ths))))
      (error 'qed "non-trivial goal")))
