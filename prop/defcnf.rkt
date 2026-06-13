#lang racket/base

;; defcnf.fs --- definitional (Tseitin) conjunctive normal form.
;;
;; Instead of F#'s (fm, defs, n) triple threaded through every call, we
;; keep the fresh-variable counter in a box and the subformula->definition
;; map in a mutable hash. maincnf etc. then return just the replacement
;; formula and mutate that shared state.

(require racket/match)
(require (only-in "../core/lib.rkt" unions))
(require (only-in "../core/formulas.rkt" overatoms mk-and mk-or mk-iff list-conj list-disj))
(require (only-in "prop.rkt" nenf simpcnf))

(provide (all-defined-out))

;; ===== fresh propositional variables =====
(define (mkprop! counter)
  (define n (unbox counter))
  (set-box! counter (add1 n))
  `(atom ,(string->symbol (string-append "p_" (number->string n)))))

;; index of a "p_<k>" atom (0 if it isn't one), used to pick a safe start
(define (var-index pfx a)
  (define s (symbol->string a))
  (define m (string-length pfx))
  (if (and (> (string-length s) m)
           (string=? (substring s 0 m) pfx)
           (let ([rest (substring s m)])
             (and (positive? (string-length rest))
                  (andmap char-numeric? (string->list rest)))))
      (string->number (substring s m))
      0))

;; ===== core procedure =====
(define (maincnf fm defs counter)
  (match fm
    [`(and ,p ,q) (defstep mk-and p q defs counter)]
    [`(or ,p ,q) (defstep mk-or p q defs counter)]
    [`(iff ,p ,q) (defstep mk-iff p q defs counter)]
    [_ fm]))

(define (defstep op p q defs counter)
  (define fm1 (maincnf p defs counter))
  (define fm2 (maincnf q defs counter))
  (define fm* (op fm1 fm2))
  (cond
    [(hash-ref defs fm* #f) => car]
    [else
     (define v (mkprop! counter))
     (hash-set! defs fm* (cons v `(iff ,v ,fm*)))
     v]))

;; ===== overall definitional CNF =====
(define (mk-defcnf fn fm)
  (define fm* (nenf fm))
  (define counter (box (add1 (overatoms (λ (a acc) (max acc (var-index "p_" a))) fm* 0))))
  (define defs (make-hash))
  (define fm** (fn fm* defs counter))
  (define deflist (map cdr (hash-values defs)))
  (unions (cons (simpcnf fm**) (map simpcnf deflist))))

(define (defcnf-orig fm)
  (list-conj (map list-disj (mk-defcnf maincnf fm))))

;; ===== version that exploits the initial /\ \/ structure =====
(define (subcnf sfn op p q defs counter)
  (define fm1 (sfn p defs counter))
  (define fm2 (sfn q defs counter))
  (op fm1 fm2))

(define (orcnf fm defs counter)
  (match fm
    [`(or ,p ,q) (subcnf orcnf mk-or p q defs counter)]
    [_ (maincnf fm defs counter)]))

(define (andcnf fm defs counter)
  (match fm
    [`(and ,p ,q) (subcnf andcnf mk-and p q defs counter)]
    [_ (orcnf fm defs counter)]))

;; set-of-clauses form (this is what the SAT procedures consume)
(define (defcnfs fm) (mk-defcnf andcnf fm))

(define (defcnf fm)
  (list-conj (map list-disj (defcnfs fm))))

;; ===== version guaranteeing 3-CNF =====
(define (andcnf3 fm defs counter)
  (match fm
    [`(and ,p ,q) (subcnf andcnf3 mk-and p q defs counter)]
    [_ (maincnf fm defs counter)]))

(define (defcnf3 fm)
  (list-conj (map list-disj (mk-defcnf andcnf3 fm))))
