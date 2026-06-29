#lang racket/base

;; Property tests for herbrand.rkt: herbfuns partitions the function symbols
;; into constants and proper functions (always supplying a constant), the
;; ground-term enumerators only ever produce ground terms / fixed-length tuples,
;; and the Gilmore / Davis-Putnam procedures succeed on valid formulas (run only
;; on guaranteed tautologies, since they are semi-decidable).

(require rackcheck
         rackunit
         "common.rkt")
(require (only-in racket/list partition))
(require (only-in "../../core/lib.rkt" image set-eq))
(require (only-in "../../prop/prop.rkt" tautology))
(require (only-in "../../fol/fol.rkt" functions fvt))
(require (only-in "../../fol/herbrand.rkt"
                  herbfuns
                  groundterms
                  groundtuples
                  gilmore
                  davisputnam
                  davisputnam002))

;; ===== first-order formulas whose atoms carry real terms (so functions vary) =====
(define gen:fatom
  (gen:bind (gen:one-of '(P Q)) (λ (p) (gen:map gen:term (λ (t) `(atom (rel ,p ,t)))))))
(define (folf-gen n)
  (if (<= n 0)
      gen:fatom
      (gen:frequency (list (cons 1 gen:fatom)
                           (cons 2 (gen:map (folf-gen (sub1 n)) (λ (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or imp iff) folf-gen n))
                           (cons 2 (quant-gen '(forall exists) '(x y) folf-gen n))))))

;; constant-free propositional tautology source (FOL-compatible atoms)
(define gen:fol-prop-nc (prop-gen-over '((atom (rel p)) (atom (rel q))) 3 #f))

;; ===== herbfuns: non-empty constants, correct arity classification =====
(check-property big
                (property ([fm (folf-gen 2)])
                          (let-values ([(consts funcs) (herbfuns fm)])
                            (and (pair? consts)
                                 (andmap (λ (c) (= (cdr c) 0)) consts)
                                 (andmap (λ (f) (> (cdr f) 0)) funcs)))))

;; ===== herbfuns exactly partitions the formula's functions (by arity) =====
;; when the formula has a constant, consts+funcs = (functions fm); otherwise the
;; default constant (c . 0) is supplied and the proper functions are unchanged
(check-property big
                (property ([fm (folf-gen 2)])
                          (define all (functions fm))
                          (define-values (c0 f0) (partition (λ (fa) (= (cdr fa) 0)) all))
                          (let-values ([(consts funcs) (herbfuns fm)])
                            (and (set-eq funcs f0)
                                 (if (null? c0)
                                     (equal? consts '((c . 0)))
                                     (set-eq consts c0))))))

;; ===== groundterms enumerates only ground terms =====
(check-property low
                (property ([fm (folf-gen 2)] [n (gen:integer-in 0 2)])
                          (let-values ([(consts funcs) (herbfuns fm)])
                            (define cntms (image (λ (c) `(fn ,(car c))) consts))
                            (andmap (λ (t) (null? (fvt t))) (groundterms cntms funcs n)))))

;; ===== groundtuples produces tuples of exactly length m =====
(check-property low
                (property ([fm (folf-gen 2)] [n (gen:integer-in 0 2)] [m (gen:integer-in 0 3)])
                          (let-values ([(consts funcs) (herbfuns fm)])
                            (define cntms (image (λ (c) `(fn ,(car c))) consts))
                            (andmap (λ (tup) (= (length tup) m)) (groundtuples cntms funcs n m)))))

;; ===== Gilmore / Davis-Putnam succeed on every (lifted) propositional taut =====
(check-property tiny
                (property ([fm gen:fol-prop-nc])
                          (or (not (tautology fm))
                              (and (exact-nonnegative-integer? (gilmore fm))
                                   (exact-nonnegative-integer? (davisputnam fm))
                                   (exact-nonnegative-integer? (davisputnam002 fm))))))

;; the refinement never keeps more instances than the full Davis-Putnam run
(check-property tiny
                (property ([fm gen:fol-prop-nc])
                          (or (not (tautology fm)) (<= (davisputnam002 fm) (davisputnam fm)))))
