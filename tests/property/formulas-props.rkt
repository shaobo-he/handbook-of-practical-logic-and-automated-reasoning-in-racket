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
                  mk-forall
                  mk-exists
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
                  atom-union
                  strip-quant
                  end-itlist))
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
(check-property big (property ([fm gen:prop]) (equal? (onatoms (λ (a) `(atom ,a)) fm) fm)))
(check-property big (property ([fm gen:prop]) (set-eq (overatoms cons fm '()) (atoms fm))))

;; list-conj / conjuncts round-trip on a flat list of distinct atoms
(define gen:atomlist
  (gen:map (gen:list (gen:integer-in 0 8) #:max-length 5)
           (λ (ns) (map (λ (n) `(atom ,(string->symbol (format "a~a" n)))) (remove-duplicates ns)))))
(check-property big (property ([l gen:atomlist]) (or (null? l) (equal? (conjuncts (list-conj l)) l))))
(check-property big (property ([l gen:atomlist]) (or (null? l) (equal? (disjuncts (list-disj l)) l))))

;; ===== quantifier constructors produce the expected node =====
(define gen:var (gen:one-of '(x y z)))
(check-property big (property ([x gen:var] [p gen:prop]) (equal? (mk-forall x p) `(forall ,x ,p))))
(check-property big (property ([x gen:var] [p gen:prop]) (equal? (mk-exists x p) `(exists ,x ,p))))

;; ===== atom-union is deduplicated =====
(check-property big
                (property ([fm gen:prop])
                          (define u (atom-union (λ (a) (list a)) fm))
                          (equal? u (remove-duplicates u))))

;; ===== conjuncts / disjuncts already produce flat leaves =====
;; Re-flattening every returned leaf leaves the list unchanged (each leaf is
;; not an and/or node, so (conjuncts leaf) = (list leaf)).
(check-property big
                (property ([fm gen:prop])
                          (equal? (apply append (map conjuncts (conjuncts fm))) (conjuncts fm))))
(check-property big
                (property ([fm gen:prop])
                          (equal? (apply append (map disjuncts (disjuncts fm))) (disjuncts fm))))

;; ===== end-itlist is a right-associative reduce =====
;; For subtraction, x1 - (x2 - (x3 - ...)) collapses to an alternating sum.
(define gen:nonempty-intlist
  (gen:map (gen:tuple (gen:integer-in -5 5) (gen:list (gen:integer-in -5 5) #:max-length 6))
           (λ (t) (cons (car t) (cadr t)))))
(check-property big
                (property ([l gen:nonempty-intlist])
                          (= (end-itlist - l)
                             (for/sum ([v (in-list l)] [i (in-naturals)])
                                      (if (even? i)
                                          v
                                          (- v))))))

;; ===== strip-quant losslessly decomposes a like-quantifier run =====
;; A forall chain re-wraps to the original; the collected vars + remaining body
;; reconstruct fm regardless of the (non-forall-headed) body shape.
(define (rebuild-forall vs bod)
  (foldr (λ (v acc) `(forall ,v ,acc)) bod vs))
(check-property big
                (property ([x gen:var] [y gen:var] [p gen:prop])
                          (define fm `(forall ,x (forall ,y ,p)))
                          (let-values ([(vs bod) (strip-quant fm)])
                            (equal? (rebuild-forall vs bod) fm))))
;; an unlike inner quantifier stops the run: (forall x (exists y p)) keeps the
;; exists in the body rather than collecting its variable.
(check-property big
                (property ([x gen:var] [y gen:var] [p gen:prop])
                          (let-values ([(vs bod) (strip-quant `(forall ,x (exists ,y ,p)))])
                            (and (equal? vs (list x)) (equal? bod `(exists ,y ,p))))))
