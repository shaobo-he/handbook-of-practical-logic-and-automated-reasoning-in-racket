#lang racket/base

(require racket/match)

(provide (all-defined-out))
;; grammar of terms
;; term ::= (var symbol)
;;        | (fn symbol term*)

;; grammar of fol
;; fol ::= (rel symbol term*)

;; grammar of formula
;; formula := #t
;;          | #f
;;          | (atom fol)
;;          | (not formula)
;;          | (and formula formula)
;;          | (or formula formula)
;;          | (imp formula formula)
;;          | (iff formula formula)
;;          | (forall formula formula)
;;          | (exists formula formula)

(define (termval func v tm)
  (match tm
    [`(var ,vn) (v vn)]
    [`(fn ,f ,@args)
     (func
      f
      (map
       (λ (tm) (termval func v tm))
       args))]))

(define (holds domain func pred v fm)
  (match fm
    [#t #t]
    [#f #f]
    [`(atom (rel ,rn ,@args))
     (pred
      rn
      (map
       (λ (tm) (termval func v tm))
       args))]))