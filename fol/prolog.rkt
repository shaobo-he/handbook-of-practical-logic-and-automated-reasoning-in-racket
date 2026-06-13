#lang racket/base

;; prolog.fs --- backchaining for Horn clauses and a toy Prolog.
;;
;; Harrison's parserule/simpleprolog/prolog take rules as strings parsed
;; with the concrete-syntax reader. This port has no string parser (it uses
;; s-expressions as the AST), so a "rule" is given directly as a pair
;;   (asm . head)
;; where `asm` is a list of body literal-formulas and `head` is the head
;; literal-formula; a goal is a single literal-formula.

(require racket/match)
(require (only-in racket/list partition range filter-map))
(require (only-in "../core/lib.rkt" fpf tryapplyd undefined tryfind))
(require (only-in "../core/formulas.rkt" list-conj))
(require (only-in "../prop/prop.rkt" positive negate simpcnf))
(require (only-in "fol.rkt" fv subst generalize))
(require (only-in "skolem.rkt" skolemize))
(require (only-in "unif.rkt" solve))
(require (only-in "tableaux.rkt" unify-literals deepen))

(provide (all-defined-out))

;; ===== rename a rule's variables, returning (rule . next-counter) =====
(define (renamerule k rule)
  (define asm (car rule))
  (define c (cdr rule))
  (define fvs (fv (list-conj (cons c asm))))
  (define n (length fvs))
  (define vvs (map (λ (i) (string->symbol (string-append "_" (number->string i)))) (range k (+ k n))))
  (define inst (fpf fvs (map (λ (x) `(var ,x)) vvs)))
  (values (cons (map (λ (a) (subst inst a)) asm) (subst inst c)) (+ k n)))

;; ===== backchaining prover =====
(define (backchain rules n k env goals)
  (match goals
    ['() env]
    [(cons g gs)
     (if (= n 0)
         (error 'prolog "Too deep")
         (tryfind (λ (rule)
                    (define-values (rc k*) (renamerule k rule))
                    (backchain rules (- n 1) k*
                               (unify-literals env (cons (cdr rc) g))
                               (append (car rc) gs)))
                  rules))]))

(define (hornify cls)
  (define-values (pos neg) (partition positive cls))
  (if (> (length pos) 1)
      (error 'prolog "non-Horn clause")
      (cons (map negate neg) (if (null? pos) #f (car pos)))))

(define (hornprove fm)
  (define rules (map hornify (simpcnf (skolemize `(not ,(generalize fm))))))
  (deepen (λ (n) (cons (backchain rules n 0 undefined (list #f)) n)) 0))

;; ===== toy Prolog over s-expression rules =====
(define (simpleprolog rules gl)
  (backchain rules -1 0 undefined (list gl)))

(define (prolog rules gl)
  (define i (solve (simpleprolog rules gl)))
  (filter-map (λ (x)
                (define t (tryapplyd i x #f))
                (and t `(atom (rel = (var ,x) ,t))))
              (fv gl)))
