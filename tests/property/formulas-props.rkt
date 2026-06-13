#lang racket/base

;; Property tests for core/formulas: constructors, destructors, collectors.

(require rackunit
         rackcheck
         "common.rkt")
(require (only-in racket/list remove-duplicates))
(require (only-in "../../core/lib.rkt" set-eq))
(require (only-in "../../core/formulas.rkt"
                  mk-and
                  mk-or
                  mk-imp
                  mk-iff
                  dest-imp
                  antecedent
                  consequent
                  dest-iff
                  dest-and
                  dest-or
                  conjuncts
                  disjuncts
                  list-conj
                  list-disj
                  onatoms
                  overatoms
                  atom-union))
(require (only-in "../../prop/prop.rkt" atoms))

(check-property big
                (property ([p gen:prop] [q gen:prop]) (equal? (dest-imp (mk-imp p q)) (cons p q))))
(check-property big
                (property ([p gen:prop] [q gen:prop])
                          (and (equal? (antecedent (mk-imp p q)) p)
                               (equal? (consequent (mk-imp p q)) q))))
(check-property big
                (property ([p gen:prop] [q gen:prop]) (equal? (dest-and (mk-and p q)) (cons p q))))
(check-property big (property ([p gen:prop] [q gen:prop]) (equal? (dest-or (mk-or p q)) (cons p q))))
(check-property big
                (property ([p gen:prop] [q gen:prop]) (equal? (dest-iff (mk-iff p q)) (cons p q))))
(check-property big (property ([fm gen:prop]) (equal? (onatoms (lambda (a) `(atom ,a)) fm) fm)))
(check-property big (property ([fm gen:prop]) (set-eq (overatoms cons fm '()) (atoms fm))))

;; list-conj / conjuncts round-trip on a flat list of distinct atoms
(define gen:atomlist
  (gen:map (gen:list (gen:integer-in 0 8) #:max-length 5)
           (lambda (ns)
             (map (lambda (n) `(atom ,(string->symbol (format "a~a" n)))) (remove-duplicates ns)))))
(check-property big (property ([l gen:atomlist]) (or (null? l) (equal? (conjuncts (list-conj l)) l))))
(check-property big (property ([l gen:atomlist]) (or (null? l) (equal? (disjuncts (list-disj l)) l))))
