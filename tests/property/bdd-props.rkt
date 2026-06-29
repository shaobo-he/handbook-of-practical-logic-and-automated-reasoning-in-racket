#lang racket/base

;; Property tests for prop/bdd: canonicity, the diagram as a decision function,
;; complement-edge negation, and the binary combinators.

(require rackunit
         rackcheck
         racket/match
         "common.rkt")
(require (only-in "../../core/lib.rkt" undefined))
(require (only-in "../../prop/prop.rkt" eval tautology psubst))
(require (only-in "../../prop/bdd.rkt"
                  mk-bdd
                  mkbdd
                  mkbdde
                  expand-node
                  bdd-and
                  bdd-or
                  bdd-imp
                  bdd-iff
                  dest-iffdef
                  ebddtaut
                  bddtaut))

(define (fresh-bc)
  (cons (mk-bdd symbol<?) undefined))
(define (eval-bdd b root v)
  (cond
    [(= root 1) #t]
    [(= root -1) #f]
    [else
     (match-define (list s l r) (expand-node b root))
     (if (v s)
         (eval-bdd b l v)
         (eval-bdd b r v))]))

;; canonicity: two formulas get the same node iff they are logically equivalent
(check-property mid
                (property ([fm1 gen:prop] [fm2 gen:prop])
                          (define-values (bc1 r1) (mkbdd (fresh-bc) fm1))
                          (define-values (bc2 r2) (mkbdd bc1 fm2))
                          (eq? (= r1 r2) (tautology `(iff ,fm1 ,fm2)))))
;; the diagram computes exactly the truth-table function
(check-property mid
                (property ([fm gen:prop] [b1 gen:boolean] [b2 gen:boolean] [b3 gen:boolean])
                          (define v
                            (λ (s)
                              (case s
                                [(p) b1]
                                [(q) b2]
                                [(r) b3]
                                [else #f])))
                          (define-values (bc root) (mkbdd (fresh-bc) fm))
                          (eq? (eval-bdd (car bc) root v) (eval fm v))))
;; negation is a complemented edge: root flips sign
(check-property mid
                (property ([fm gen:prop])
                          (define-values (bc1 r1) (mkbdd (fresh-bc) fm))
                          (define-values (_ r2) (mkbdd bc1 `(not ,fm)))
                          (= r2 (- r1))))
;; the binary combinators match building the compound formula directly
(define (bdd-combiner op)
  (case op
    [(and) bdd-and]
    [(or) bdd-or]
    [(imp) bdd-imp]
    [(iff) bdd-iff]))
(check-property mid
                (property ([op (gen:one-of '(and or imp iff))] [fm1 gen:prop] [fm2 gen:prop])
                          (define-values (bc1 r1) (mkbdd (fresh-bc) fm1))
                          (define-values (bc2 r2) (mkbdd bc1 fm2))
                          (define-values (bc3 rc) ((bdd-combiner op) bc2 (cons r1 r2)))
                          (define-values (_ rd) (mkbdd bc3 `(,op ,fm1 ,fm2)))
                          (= rc rd)))

;; ===== complement edges: expanding -id negates both children of id =====
;; a non-constant node (s l r) at id has its negation -id expand to (s -l -r)
(check-property mid
                (property ([fm gen:prop])
                          (define-values (bc root) (mkbdd (fresh-bc) fm))
                          (define b (car bc))
                          (cond
                            [(<= (abs root) 1) #t] ; constant: nothing to expand
                            [else
                             (match-define (list s l r) (expand-node b root))
                             (match-define (list s2 l2 r2) (expand-node b (- root)))
                             (and (equal? s s2) (= l2 (- l)) (= r2 (- r)))])))

;; ===== dest-iffdef succeeds exactly on a defining equivalence =====
(define (succeeds? f x)
  (with-handlers ([exn:fail? (λ (_) #f)])
    (f x)
    #t))
(define (is-iffdef? fm)
  (match fm
    [`(iff (atom ,_) ,_) #t]
    [`(iff ,_ (atom ,_)) #t]
    [_ #f]))
(check-property mid (property ([fm gen:prop]) (eq? (succeeds? dest-iffdef fm) (is-iffdef? fm))))

;; ===== mkbdde substitutes a shared definition for an atom =====
;; with sfn = {x -> node(g)}, mkbdde evaluates atom x as the BDD of g, so the
;; resulting decision function equals that of h with x replaced by g
(define gen:prop-x (prop-gen-over '((atom p) (atom q) (atom r) (atom x)) 4))
(check-property
 mid
 (property ([g gen:prop] [h gen:prop-x] [b1 gen:boolean] [b2 gen:boolean] [b3 gen:boolean])
           (define-values (bc1 mg) (mkbdd (fresh-bc) g))
           (define sfn (hash 'x mg))
           (define-values (bc2 root) (mkbdde sfn bc1 h))
           (define v
             (λ (s)
               (case s
                 [(p) b1]
                 [(q) b2]
                 [(r) b3]
                 [else #f])))
           (eq? (eval-bdd (car bc2) root v) (eval (psubst (hash 'x g) h) v))))

;; ===== ebddtaut agrees with bddtaut (the shared-definition path is sound) =====
(check-property mid (property ([fm gen:prop]) (eq? (ebddtaut fm) (bddtaut fm))))
