#lang racket/base

;; Unit tests for prop/bdd: node construction and the unique/expand tables
;; (reduction when l=r, idempotent insertion, complement-edge expansion),
;; the iff-definition destructors, and ebddtaut agreeing with bddtaut on
;; formulas that carry no shared definitions.

(require rackunit)
(require (only-in "../prop/prop.rkt" atoms))
(require "../prop/bdd.rkt")

;; ===== mk-node: reduction, fresh insertion, idempotent insertion =====
;; a brand-new BDD has ids 0,1 reserved (n starts at 2)
(define b0 (mk-bdd symbol<?))
(check-equal? (bdd-n b0) 2)
;; an honest node (l != r) is inserted and gets the next free id, 2
(define-values (b1 m1) (mk-node b0 (list 'p 1 -1)))
(check-equal? m1 2)
(check-equal? (bdd-n b1) 3)
;; inserting the same node again returns the same id and grows nothing
(define-values (b2 m2) (mk-node b1 (list 'p 1 -1)))
(check-equal? m2 m1)
(check-equal? (bdd-n b2) 3)
;; a redundant node (l = r) collapses to that child, with no new id
(define-values (b3 m3) (mk-node b2 (list 'q 5 5)))
(check-equal? m3 5)
(check-equal? (bdd-n b3) 3)

;; ===== expand-node: a complemented id flips both children's signs =====
(check-equal? (expand-node b1 m1) (list 'p 1 -1))
(check-equal? (expand-node b1 (- m1)) (list 'p -1 1))

;; ===== dest-iffdef: extract the defined variable and its body =====
;; the LEFT atom is preferred when both sides are atoms
(check-equal? (dest-iffdef '(iff (atom x) (atom q))) (cons 'x '(atom q)))
(check-equal? (dest-iffdef '(iff (atom q) (atom x))) (cons 'q '(atom x)))
;; the right atom is taken only when the left side is a compound formula
(check-equal? (dest-iffdef '(iff (and (atom a) (atom b)) (atom x)))
              (cons 'x '(and (atom a) (atom b))))
;; a non-defining formula raises
(check-exn exn:fail? (λ () (dest-iffdef '(and (atom p) (atom q)))))
(check-exn exn:fail? (λ () (dest-iffdef '(imp (atom p) (atom q)))))

;; ===== dest-nimp: split (not p) and (imp p q); reject other shapes =====
(check-equal? (dest-nimp '(not (atom p))) (cons '(atom p) #f))
(check-equal? (dest-nimp '(imp (atom p) (atom q))) (cons '(atom p) '(atom q)))
(check-exn exn:fail? (λ () (dest-nimp '(atom p))))
(check-exn exn:fail? (λ () (dest-nimp '(and (atom p) (atom q)))))

;; ===== ebddtaut equals bddtaut when there are no shared iff-definitions =====
(define peirce '(imp (imp (imp (atom p) (atom q)) (atom p)) (atom p)))
(for ([fm (in-list (list peirce
                         '(or (atom p) (not (atom p)))
                         '(or (atom p) (atom q))
                         '(and (atom p) (atom q))
                         '(imp (and (atom p) (atom q)) (atom p))))])
  (check-equal? (ebddtaut fm) (bddtaut fm) (format "ebddtaut/bddtaut disagree on ~s" fm)))

;; ===== ebddtaut exploits a shared definition p <=> (q /\ r) =====
(check-true (ebddtaut '(imp (iff (atom p) (and (atom q) (atom r))) (imp (atom p) (atom q)))))
(check-false (ebddtaut '(imp (iff (atom p) (and (atom q) (atom r))) (imp (atom p) (atom s)))))

;; ===== sort-defs topologically orders definitions (no forward references) =====
;; d2 depends on d1, d1 on d0, d0 only on base atoms; sort-defs must list each
;; definition before any that it refers to
(define (no-forward-refs? sorted)
  (let loop ([ds sorted])
    (cond
      [(null? ds) #t]
      [else
       (define rhs-atoms (atoms (cdr (car ds))))
       (define later-lhs (map car (cdr ds)))
       (and (null? (filter (λ (a) (and (member a rhs-atoms) #t)) later-lhs)) (loop (cdr ds)))])))
(let ([defs (list (cons 'd2 '(and (atom d1) (atom a)))
                  (cons 'd0 '(and (atom a) (atom b)))
                  (cons 'd1 '(or (atom d0) (atom c))))])
  (define-values (sorted fm*) (sort-defs '() defs '(atom d2)))
  (check-equal? (map car sorted) '(d0 d1 d2))
  (check-true (no-forward-refs? sorted)))