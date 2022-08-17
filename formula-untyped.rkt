#lang racket/base

(require racket/match)
(require racket/set)

(provide atom-union)

;; grammar of formula
;; formula := #t
;;          | #f
;;          | (atom a)
;;          | (not formula)
;;          | (and formula formula)
;;          | (or formula formula)
;;          | (imp formula formula)
;;          | (iff formula formula)
;;          | (forall symbol formula)
;;          | (exists symbol formula)

(define (overatoms fun fm b)
  (match fm
    [`(atom ,a) (fun a b)]
    [`(not ,f) (overatoms fun f b)]
    [`(,(or 'and 'or 'imp 'iff) ,f1 ,f2) (overatoms fun f1 (overatoms fun f2 b))]
    [`(,(or 'forall 'exists) ,s ,f) (overatoms fun f b)]
    [_ b]))

(define (atom-union fun fm)
  (set->list (list->set (overatoms (λ (h t) (append (fun h) t)) fm '()))))
