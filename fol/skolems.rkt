#lang racket/base

;; skolems --- Skolemizing a *set* of formulas simultaneously, renaming
;; function symbols apart first.

(require racket/match)
(require (only-in "fol.rkt" onformula))
(require (only-in "skolem.rkt" skolem))

(provide (all-defined-out))

(define (rename-term tm)
  (match tm
    [`(fn ,f ,@args)
     `(fn ,(string->symbol (string-append "old_" (symbol->string f))) ,@(map rename-term args))]
    [_ tm]))

(define (rename-form fm)
  (onformula rename-term fm))

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
