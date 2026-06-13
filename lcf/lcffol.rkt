#lang racket/base

;; lcffol.fs --- an LCF-style first-order prover: a tableau refutation that
;; builds an actual kernel proof, with Skolemization handled by deferred
;; (CPS) proof construction and later de-Skolemization.

(require racket/match)
(require (only-in racket/list range))
(require (only-in "../core/lib.rkt"
                  chop-list
                  index
                  union
                  unions
                  subtract
                  setify
                  update
                  undefine
                  undefined
                  funpow
                  repeat))
(require (only-in "../core/formulas.rkt" consequent antecedent mk-imp))
(require (only-in "../fol/fol.rkt" subst tsubst fv fvt var variant onformula functions))
(require (only-in "../fol/unif.rkt" unify solve))
(require (only-in "../fol/resolution.rkt" term-match))
(require (only-in "../equality/eqelim.rkt" replacet))
(require (only-in "../equality/order.rkt" termsize))
(require (only-in "../fol/tableaux.rkt" deepen))
(require "lcf.rkt")
(require "lcfprop.rkt")
(require "folderived.rkt")

(provide (all-defined-out))

;; ===== unify complementary literals =====
(define (unify-complementsf env pp)
  (match pp
    [(cons `(atom (rel ,p1 ,@a1)) `(imp (atom (rel ,p2 ,@a2)) #f))
     (unify env (list (cons `(fn ,p1 ,@a1) `(fn ,p2 ,@a2))))]
    [(cons `(imp (atom (rel ,p1 ,@a1)) #f) `(atom (rel ,p2 ,@a2)))
     (unify env (list (cons `(fn ,p1 ,@a1) `(fn ,p2 ,@a2))))]
    [_ (error 'unify-complementsf "unify_complementsf")]))

;; move a "later implication" to the front
(define (use-laterimp i fm)
  (match fm
    [`(imp (imp ,q* ,s) (imp ,(and i* `(imp ,q ,p)) ,r))
     #:when (equal? i* i)
     (define th1 (axiom-distribimp i `(imp (imp ,q ,s) ,r) `(imp (imp ,p ,s) ,r)))
     (define th2 (imp-swap (imp-trans-th q p s)))
     (define th3 (imp-swap (imp-trans-th `(imp ,p ,s) `(imp ,q ,s) r)))
     (imp-swap2 (modusponens th1 (imp-trans th2 th3)))]
    [`(imp ,qs (imp ,a ,b)) (imp-swap2 (imp-add-assum a (use-laterimp i `(imp ,qs ,b))))]))

;; ===== deferred "closure" proof builders (each returns a builder es->thm) =====
(define ((imp-false-rule* th) es)
  (imp-false-rule (th es)))
(define ((imp-true-rule* th1 th2) es)
  (imp-true-rule (th1 es) (th2 es)))
(define ((imp-front* n thp) es)
  (imp-front n (thp es)))
(define ((add-assum* fm thp) es)
  (add-assum (onformula (car es) fm) (thp es)))
(define ((eliminate-connective* fm thp) es)
  (imp-trans (eliminate-connective (onformula (car es) fm)) (thp es)))
(define ((spec* y fm n thp) es)
  (define e (car es))
  (define th (imp-swap (imp-front n (thp es))))
  (imp-unduplicate (imp-trans (ispec (e y) (onformula e fm)) th)))
(define ((ex-falso* fms) es)
  (define e (car es))
  (ex-falso (foldr (λ (fm acc) (mk-imp (onformula e fm) acc)) (cdr es) fms)))
(define ((complits* fms+lits i) es)
  (match-define (cons (cons p fl) lits) fms+lits)
  (define e (car es))
  (define-values (l1 rest) (chop-list i lits))
  (match-define (cons p* l2) rest)
  (foldr (λ (fm acc) (imp-insert (onformula e fm) acc))
         (imp-contr (onformula e p) (foldr (λ (fm acc) (mk-imp (onformula e fm) acc)) (cdr es) l2))
         (append fl l1)))
(define ((deskol* skh thp) es)
  (define th (thp es))
  (modusponens (use-laterimp (onformula (car es) skh) (concl th)) th))

;; ===== main refutation (cont takes (proof-builder esk); esk = (env sks k)) =====
(define (lcftab skofun fms lits n cont esk)
  (if (< n 0)
      (error 'lcftab "no proof")
      (match fms
        ['() (error 'lcftab "No contradiction")]
        [(cons #f fl) (cont (ex-falso* (append fl lits)) esk)]
        [(cons (and fm `(imp ,p ,q)) fl)
         #:when (equal? p q)
         (lcftab skofun fl lits n (λ (thp e2) (cont (add-assum* fm thp) e2)) esk)]
        [(cons `(imp (imp ,p ,q) #f) fl)
         (lcftab skofun
                 (cons p (cons `(imp ,q #f) fl))
                 lits
                 n
                 (λ (thp e2) (cont (imp-false-rule* thp) e2))
                 esk)]
        [(cons `(imp ,p ,q) fl)
         #:when (not (equal? q #f))
         (lcftab
          skofun
          (cons `(imp ,p #f) fl)
          lits
          n
          (λ (th e2)
            (lcftab skofun (cons q fl) lits n (λ (thp e3) (cont (imp-true-rule* th thp) e3)) e2))
          esk)]
        [(cons (and p (or `(atom ,_) `(imp (atom ,_) #f))) fl)
         (match-define (list env sks k) esk)
         (with-handlers ([exn:fail? (λ (ex)
                                      (lcftab skofun
                                              fl
                                              (cons p lits)
                                              n
                                              (λ (thp e2) (cont (imp-front* (length fl) thp) e2))
                                              esk))])
           (tryfind* (λ (p*)
                       (define env* (unify-complementsf env (cons p p*)))
                       (cont (complits* (cons fms lits) (index p* lits)) (list env* sks k)))
                     lits))]
        [(cons (and fm `(forall ,x ,p)) fl)
         (match-define (list env sks k) esk)
         (define y `(var ,(string->symbol (string-append "X_" (number->string k)))))
         (lcftab skofun
                 (append (cons (subst (update x y undefined) p) fl) (list fm))
                 lits
                 (- n 1)
                 (λ (thp e2) (cont (spec* y fm (length fms) thp) e2))
                 (list env sks (+ k 1)))]
        [(cons `(imp ,(and yp `(forall ,y ,p)) #f) fl)
         (match-define (list env sks k) esk)
         (define fx (skofun yp))
         (define p* (subst (update y fx undefined) p))
         (define skh `(imp ,p* (forall ,y ,p)))
         (define sks* (cons (cons `(forall ,y ,p) fx) sks))
         (lcftab skofun
                 (cons `(imp ,p* #f) fl)
                 lits
                 n
                 (λ (thp e2) (cont (deskol* skh thp) e2))
                 (list env sks* k))]
        [(cons fm fl)
         (define fm* (consequent (concl (eliminate-connective fm))))
         (lcftab skofun
                 (cons fm* fl)
                 lits
                 n
                 (λ (thp e2) (cont (eliminate-connective* fm thp) e2))
                 esk)])))

;; local tryfind (lib's is fine, but keep the lcffol search self-contained)
(define (tryfind* f l)
  (cond
    [(null? l) (error 'tryfind "tryfind")]
    [else
     (with-handlers ([exn:fail? (λ (e) (tryfind* f (cdr l)))])
       (f (car l)))]))

;; ===== identify quantified subformulas, accounting for parity =====
(define (quantforms e fm)
  (match fm
    [`(not ,p) (quantforms (not e) p)]
    [`(and ,p ,q) (union (quantforms e p) (quantforms e q))]
    [`(or ,p ,q) (union (quantforms e p) (quantforms e q))]
    [`(imp ,p ,q) (quantforms e `(or (not ,p) ,q))]
    [`(iff ,p ,q) (quantforms e `(or (and ,p ,q) (and (not ,p) (not ,q))))]
    [`(exists ,x ,p)
     (if e
         (cons fm (quantforms e p))
         (quantforms e p))]
    [`(forall ,x ,p)
     (if e
         (quantforms e p)
         (cons fm (quantforms e p)))]
    [_ '()]))

;; ===== Skolem functions =====
(define (skolemfuns fm)
  (define fns (map car (functions fm)))
  (define skts
    (map (λ (q)
           (match q
             [`(exists ,x ,p) `(forall ,x (not ,p))]
             [_ q]))
         (quantforms #t fm)))
  (define (skofun i ap)
    (match ap
      [`(forall ,y ,p)
       (cons ap
             `(fn ,(variant (string->symbol (string-append "f_" (number->string i))) fns)
                  ,@(map (λ (v) `(var ,v)) (fv ap))))]))
  (map skofun (range 1 (add1 (length skts))) skts))

;; ===== matching =====
(define (form-match fp env)
  (match fp
    [(cons #f #f) env]
    [(cons #t #t) env]
    [(cons `(atom (rel ,p ,@pa)) `(atom (rel ,q ,@qa)))
     (term-match env (list (cons `(fn ,p ,@pa) `(fn ,q ,@qa))))]
    [(cons `(not ,p1) `(not ,p2)) (form-match (cons p1 p2) env)]
    [(cons `(,(and o (or 'and 'or 'imp 'iff)) ,p1 ,q1) `(,o2 ,p2 ,q2))
     #:when (eq? o o2)
     (form-match (cons p1 p2) (form-match (cons q1 q2) env))]
    [(cons `(,(and qf (or 'forall 'exists)) ,x1 ,p1) `(,qf2 ,x2 ,p2))
     #:when (and (eq? qf qf2) (equal? x1 x2))
     (define z (variant x1 (union (fv p1) (fv p2))))
     (define (inst-fn f)
       (subst (update x1 `(var ,z) undefined) f))
     (undefine z (form-match (cons (inst-fn p1) (inst-fn p2)) env))]
    [_ (error 'form-match "form_match")]))

(define (lcfrefute fm n cont)
  (define sl (skolemfuns fm))
  (define (find-skolem fm2)
    (tryfind* (λ (ft) (tsubst (form-match (cons (car ft) fm2) undefined) (cdr ft))) sl))
  (lcftab find-skolem (list fm) '() n cont (list undefined '() 0)))

;; ===== de-Skolemization =====
(define (mk-skol ap-fx q)
  (match (car ap-fx)
    [`(forall ,y ,p) `(imp (imp ,(subst (update y (cdr ap-fx) undefined) p) (forall ,y ,p)) ,q)]))

(define (simpcont thp esk)
  (match-define (list env sks k) esk)
  (define (ifn tm)
    (tsubst (solve env) tm))
  (thp (cons ifn (onformula ifn (foldr mk-skol #f sks)))))

(define (elim-skolemvar th)
  (match (concl th)
    [`(imp (imp ,pv ,(and apx `(forall ,x ,px))) ,q)
     (define th12 (map (λ (t) (imp-trans (imp-add-concl #f th) t)) (imp-false-conseqs pv apx)))
     (define th1 (car th12))
     (define th2 (cadr th12))
     (define v (car (append (subtract (fv pv) (fv apx)) (list x))))
     (define th3 (gen-right v th1))
     (define th4 (imp-trans th3 (alpha x (consequent (concl th3)))))
     (modusponens (axiom-doubleneg q) (right-mp th2 th4))]
    [_ (error 'elim-skolemvar "elim_skolemvar")]))

(define (deskolcont thp esk)
  (match-define (list env sks k) esk)
  (define (ifn tm)
    (tsubst (solve env) tm))
  (define isk (setify (map (λ (pt) (cons (onformula ifn (car pt)) (ifn (cdr pt)))) sks)))
  (define ssk (sort isk (λ (a b) (> (termsize (cdr a)) (termsize (cdr b))))))
  (define vs
    (map (λ (i) `(var ,(string->symbol (string-append "Y_" (number->string i)))))
         (range 1 (add1 (length ssk)))))
  (define vfn-map (foldr (λ (pt v acc) (update (cdr pt) v acc)) undefined ssk vs))
  (define (vfn tm)
    (replacet vfn-map tm))
  (define th (thp (cons (λ (tm) (vfn (ifn tm))) (onformula vfn (foldr mk-skol #f ssk)))))
  (repeat (λ (t) (elim-skolemvar (imp-swap t))) th))

;; ===== overall prover =====
(define (lcffol fm)
  (define fvs (fv fm))
  (define fm* `(imp ,(foldr (λ (x acc) `(forall ,x ,acc)) fm fvs) #f))
  (define th1 (deepen (λ (n) (lcfrefute fm* n deskolcont)) 0))
  (modusponens (axiom-doubleneg (negatef fm*)) th1))
