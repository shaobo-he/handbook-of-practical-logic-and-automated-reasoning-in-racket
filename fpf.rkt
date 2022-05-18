#lang racket/base

(require racket/match)
(provide (all-defined-out))

;; naive finite partial functions
;; a partial function is simply pattern matching
;; thus it's not canonical as the one in the
;; ocaml implmentation

(define (tryapplyd f k d)
  (with-handlers ([exn:misc:match? (λ (e) d)])
    (f k)))

(define (undefine x f)
  (λ (k)
    (match k
      [y #:when (not (equal? x k)) (f k)])))

(define (update k v f)
  (λ (k^)
    (match k^
      [x #:when (equal? x k) v]
      [_ (f k^)])))

(define (undefined k)
  (match k
    [x #:when #f '⊥]))
