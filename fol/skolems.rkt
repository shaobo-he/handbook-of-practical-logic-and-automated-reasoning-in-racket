#lang racket/base

;; skolems --- Skolemizing a *set* of formulas simultaneously, renaming
;; function symbols apart first.

(require racket/match)
(require (only-in "fol.rkt" onformula))
(require (only-in "skolem.rkt" skolem))

(provide (all-defined-out))

;; prefix every existing function symbol with "old_" so it cannot clash with the
;; fresh c_/f_ Skolem functions introduced below when several formulas are
;; Skolemized together.
(define (rename-term tm)
  (match tm
    [`(fn ,f ,@args)
     `(fn ,(string->symbol (string-append "old_" (symbol->string f))) ,@(map rename-term args))]
    [_ tm]))

;; apply the "old_" renaming to every term in fm (onformula maps over its atoms)
(define (rename-form fm)
  (onformula rename-term fm))

;; Skolemize each formula in turn, threading `corr` (the list of Skolem function
;; names already used) through the whole set so names stay unique across formulas.
(define (skolems fms corr)
  (match fms
    ['() (values '() corr)]
    [`(,p . ,ofms)
     (define-values (p* corr*) (skolem (rename-form p) corr))
     (define-values (ps* corr**) (skolems ofms corr*))
     (values (cons p* ps*) corr**)]))

(define (skolemizes fms)
  (let-values ([(r _) (skolems fms '())])
    r))
