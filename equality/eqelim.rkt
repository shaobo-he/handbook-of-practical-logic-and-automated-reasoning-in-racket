#lang racket/base

;; eqelim --- equality elimination: Brand's S/T/E modifications and the
;; Brand transformation, fed into MESON (bmeson); plus emeson via axioms.

(require racket/match)
(require (only-in "../core/lib.rkt" tryfind subtract insert union apply update undefined))
(require (only-in "../core/formulas.rkt" list-conj))
(require (only-in "../prop/prop.rkt" simpcnf simpdnf))
(require (only-in "../fol/fol.rkt" fv variant onformula generalize))
(require (only-in "../fol/skolem.rkt" specialize pnf askolemize))
(require (only-in "equal.rkt" mk-eq dest-eq is-eq equalitize))
(require (only-in "../fol/meson.rkt" contrapositives mexpand002 meson002))
(require (only-in "../fol/tableaux.rkt" deepen))

(provide (all-defined-out))

;; find that raises (rather than returning #f) when nothing matches
(define (list-find pred l)
  (or (findf pred l) (error 'list-find "find")))

;; ===== Brand's S modification (symmetrize equations) =====
;; tryfind locates one equation s=t in the clause; we recurse on the rest and
;; emit both orientations (s=t and t=s) into every resulting clause. The handler
;; fires when no equation remains, terminating the recursion with the clause as-is.
(define (modify-S cl)
  (with-handlers ([exn:fail? (λ (e) (list cl))])
    (define st (tryfind dest-eq cl))
    (define s (car st))
    (define t (cdr st))
    (define eq1 (mk-eq s t))
    (define eq2 (mk-eq t s))
    (define sub (modify-S (subtract cl (list eq1))))
    (append (map (λ (c) (insert eq1 c)) sub) (map (λ (c) (insert eq2 c)) sub))))

;; ===== Brand's T modification (flatten equation right-hand sides) =====
;; Each equation s=t is replaced by  (not t=w), s=w  for a fresh w (variant 'w
;; avoids capture against the variables of the rest of the clause). Non-equation
;; literals are passed through; equations are handled before the other literals.
(define (modify-T cl)
  (match cl
    ['() '()]
    [`(,(and eq `(atom (rel = ,s ,t))) . ,ps)
     (define ps* (modify-T ps))
     (define w `(var ,(variant 'w (foldr (λ (p acc) (union (fv p) acc)) (fv eq) ps*))))
     (cons `(not ,(mk-eq t w)) (cons (mk-eq s w) ps*))]
    [`(,p . ,ps) (cons p (modify-T ps))]))

;; ===== E modification (abstract non-variable subterms) =====
(define (is-nonvar tm)
  (match tm
    [`(var ,x) #f]
    [_ #t]))

(define (find-nestnonvar tm)
  (match tm
    [`(var ,x) (error 'find-nestnonvar "findnvsubt")]
    [`(fn ,f ,@args) (list-find is-nonvar args)]))

(define (find-nvsubterm fm)
  (match fm
    [`(atom (rel = ,s ,t)) (tryfind find-nestnonvar (list s t))]
    [`(atom (rel ,p ,@args)) (list-find is-nonvar args)]
    [`(not ,p) (find-nvsubterm p)]))

(define (replacet rfn tm)
  (with-handlers ([exn:fail? (λ (e)
                               (match tm
                                 [`(fn ,f ,@args) `(fn ,f ,@(map (λ (a) (replacet rfn a)) args))]
                                 [_ tm]))])
    (apply rfn tm)))

(define (replace rfn fm)
  (onformula (λ (t) (replacet rfn t)) fm))

;; Repeatedly abstract one non-variable proper subterm t into a fresh variable w,
;; replacing every occurrence and adding the side literal (not t=w); fvs threads
;; the in-use variables so each w is fresh. The handler ends the loop when
;; find-nvsubterm raises (no non-variable subterm is left to abstract).
(define (emodify fvs cls)
  (with-handlers ([exn:fail? (λ (e) cls)])
    (define t (tryfind find-nvsubterm cls))
    (define w (variant 'w fvs))
    (define cls* (map (λ (c) (replace (update t `(var ,w) undefined) c)) cls))
    (emodify (cons w fvs) (cons `(not ,(mk-eq t `(var ,w))) cls*))))

(define (modify-E cls)
  (emodify (foldr (λ (c acc) (union (fv c) acc)) '() cls) cls))

;; ===== overall Brand transformation =====
;; Apply E then S then T, and always prepend the reflexivity clause x=x: with
;; equality replaced by a plain predicate, MESON needs this as its base fact.
(define (brand cls)
  (define cls1 (map modify-E cls))
  (define cls2 (foldr (λ (c acc) (union (modify-S c) acc)) '() cls1))
  (cons (list (mk-eq '(var x) '(var x))) (map modify-T cls2)))

;; ===== MESON with the Brand transformation =====
;; Brand-transform the CNF clauses, turn them into contrapositive rules, and run
;; the model-elimination core (mexpand002) inside deepen, which iteratively raises
;; the depth bound until a proof is found.
(define (bpuremeson fm)
  (define cls (brand (simpcnf (specialize (pnf fm)))))
  (define rules (foldr (λ (c acc) (append (contrapositives c) acc)) '() cls))
  (deepen (λ (n)
            (mexpand002 rules '() #f (λ (env n k) env) undefined n 0)
            n)
          0))

(define (bmeson fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (bpuremeson (list-conj d))) (simpdnf fm1)))

;; equality via explicit axioms then ordinary MESON
(define (emeson fm)
  (meson002 (equalitize fm)))
