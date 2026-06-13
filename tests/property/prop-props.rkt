#lang racket/base

;; Property tests for propositional logic and SAT: every checker is
;; cross-validated against the truth-table oracle, normal forms preserve
;; meaning, and propexamples generators match arithmetic oracles.

(require rackunit
         rackcheck
         racket/match
         "common.rkt")
(require (only-in math/number-theory prime?))
(require (only-in "../../prop/prop.rkt"
                  eval
                  atoms
                  tautology
                  satisfiable
                  unsatisfiable
                  psimplify
                  nnf
                  nenf
                  dual
                  dnf
                  cnf))
(require (only-in "../../prop/dp.rkt" dptaut dplltaut dpsat dpllsat dplbsat dplbtaut))
(require (only-in "../../prop/bdd.rkt" bddtaut ebddtaut))
(require (only-in "../../prop/stal.rkt" stalmarck))
(require (only-in "../../prop/propexamples.rkt" prime mk-adder-test ramsey))

;; eval is a homomorphism on the connectives
(check-property
 big
 (property ([p gen:prop] [q gen:prop] [b1 gen:boolean] [b2 gen:boolean] [b3 gen:boolean])
           (define v
             (lambda (s)
               (case s
                 [(p) b1]
                 [(q) b2]
                 [(r) b3]
                 [else #f])))
           (and (eq? (eval `(and ,p ,q) v) (and (eval p v) (eval q v)))
                (eq? (eval `(or ,p ,q) v) (or (eval p v) (eval q v)))
                (eq? (eval `(imp ,p ,q) v) (or (not (eval p v)) (eval q v)))
                (eq? (eval `(iff ,p ,q) v) (eq? (eval p v) (eval q v)))
                (eq? (eval `(not ,p) v) (not (eval p v))))))
;; every tautology checker agrees with the truth-table oracle
(check-property mid
                (property ([fm gen:prop])
                          (let ([t (tautology fm)])
                            (and (eq? t (bddtaut fm))
                                 (eq? t (ebddtaut fm))
                                 (eq? t (dptaut fm))
                                 (eq? t (dplltaut fm))
                                 (eq? t (dplbtaut fm))))))
;; every satisfiability checker agrees
(check-property mid
                (property ([fm gen:prop])
                          (let ([s (satisfiable fm)])
                            (and (eq? s (dpsat fm)) (eq? s (dpllsat fm)) (eq? s (dplbsat fm))))))
;; satisfiable / unsatisfiable are dual
(check-property mid (property ([fm gen:prop]) (eq? (satisfiable fm) (not (unsatisfiable fm)))))
;; Stalmarck soundness: a returned verdict matches the oracle
(check-property mid
                (property ([fm gen:prop])
                          (define r
                            (with-handlers ([exn:fail? (lambda (e) 'unknown)])
                              (stalmarck fm)))
                          (or (eq? r 'unknown) (eq? r (tautology fm)))))
;; normal forms preserve meaning
(check-property mid (property ([fm gen:prop]) (tautology `(iff ,fm ,(nnf fm)))))
(check-property mid (property ([fm gen:prop]) (tautology `(iff ,fm ,(nenf fm)))))
(check-property mid (property ([fm gen:prop]) (tautology `(iff ,fm ,(dnf fm)))))
(check-property mid (property ([fm gen:prop]) (tautology `(iff ,fm ,(cnf fm)))))
(check-property mid (property ([fm gen:prop]) (tautology `(iff ,fm ,(psimplify fm)))))
;; normal-form idempotence and structure
(check-property mid (property ([fm gen:prop]) (equal? (psimplify (psimplify fm)) (psimplify fm))))
(define (nnf-shape? fm)
  (match fm
    [(or #t #f) #t]
    [`(atom ,_) #t]
    [`(not (atom ,_)) #t]
    [`(and ,p ,q) (and (nnf-shape? p) (nnf-shape? q))]
    [`(or ,p ,q) (and (nnf-shape? p) (nnf-shape? q))]
    [_ #f]))
(check-property mid (property ([fm gen:prop]) (nnf-shape? (nnf fm))))
;; dual is an involution on the {and,or,not} fragment
(define (aoi-gen n)
  (if (<= n 0)
      (gen:one-of '((atom p) (atom q) (atom r)))
      (gen:frequency (list (cons 1 (gen:one-of '((atom p) (atom q) (atom r))))
                           (cons 2 (gen:map (aoi-gen (sub1 n)) (lambda (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or) aoi-gen n))))))
(check-property big (property ([fm (aoi-gen 4)]) (equal? (dual (dual fm)) fm)))
;; propexamples against oracles
(check-property low (property ([p (gen:integer-in 2 20)]) (eq? (bddtaut (prime p)) (prime? p))))
(check-property tiny
                (property ([n (gen:integer-in 1 3)] [k (gen:integer-in 1 3)])
                          (bddtaut (mk-adder-test n k))))
;; Ramsey: ramsey(3,3,n) is a tautology iff n >= R(3,3) = 6
(check-property (make-config #:tests 10)
                (property ([n (gen:integer-in 2 6)]) (eq? (dplltaut (ramsey 3 3 n)) (>= n 6))))
