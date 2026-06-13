#lang racket/base

;; Property tests for equality: equation accessors, congruence axioms,
;; subterms, the lexicographic path order, rewriting, and congruence closure.

(require rackunit
         rackcheck
         "common.rkt")
(require (only-in "../../lcf/limitations.rkt" numeral))
(require (only-in "../../equality/equal.rkt" mk-eq dest-eq lhs rhs is-eq function-congruence))
(require (only-in "../../equality/cong.rkt" subterms ccvalid))
(require (only-in "../../equality/order.rkt" termsize lpo-gt lpo-ge weight))
(require (only-in "../../equality/rewrite.rkt" rewrite))

;; ground terms (no variables), for total orderings and congruence closure
(define (gterm-gen n)
  (if (<= n 0)
      (gen:one-of '((fn a) (fn b) (fn c)))
      (gen:frequency (list (cons 1 (gen:one-of '((fn a) (fn b) (fn c))))
                           (cons 2 (gen:map (gterm-gen (sub1 n)) (λ (t) `(fn f ,t))))
                           (cons 2
                                 (gen:map (gen:tuple (gterm-gen (sub1 n)) (gterm-gen (sub1 n)))
                                          (λ (st) `(fn g ,(car st) ,(cadr st)))))))))
(define gen:gterm (gterm-gen 3))

;; equation accessors and congruence axioms
(check-property big (property ([s gen:term] [t gen:term]) (equal? (dest-eq (mk-eq s t)) (cons s t))))
(check-property
 big
 (property ([s gen:term] [t gen:term])
           (and (equal? (lhs (mk-eq s t)) s) (equal? (rhs (mk-eq s t)) t) (is-eq (mk-eq s t)))))
(check-property big
                (property ([k (gen:integer-in 1 4)])
                          (= (length (function-congruence (cons 'f k))) 1)))
(check-property big (property () (null? (function-congruence (cons 'c 0)))))

;; subterms contains the term itself
(check-property big (property ([t gen:term]) (and (member t (subterms t)) #t)))

;; termsize: positive and additive over arguments
(check-property big (property ([t gen:term]) (>= (termsize t) 1)))
(check-property big
                (property ([a gen:term] [b gen:term])
                          (= (termsize `(fn g ,a ,b)) (+ 1 (termsize a) (termsize b)))))

;; the lexicographic path order is a strict order with the subterm property
(define ord (λ (p q) (weight '(a b c f g) p q)))
(check-property big (property ([t gen:term]) (not (lpo-gt ord t t))))
(check-property big
                (property ([s gen:term] [t gen:term]) (not (and (lpo-gt ord s t) (lpo-gt ord t s)))))
(check-property big
                (property ([a gen:term] [b gen:term] [c gen:term])
                          (or (not (lpo-gt ord a b)) (not (lpo-gt ord b c)) (lpo-gt ord a c))))
(check-property big
                (property ([s gen:term] [t gen:term])
                          (eq? (lpo-ge ord s t) (or (equal? s t) (lpo-gt ord s t)))))
;; a compound term dominates each of its arguments
(check-property big
                (property ([a gen:term] [b gen:term])
                          (and (lpo-gt ord `(fn g ,a ,b) a) (lpo-gt ord `(fn g ,a ,b) b))))
;; LPO is total on distinct ground terms (total precedence)
(check-property mid
                (property ([s gen:gterm] [t gen:gterm])
                          (or (equal? s t) (lpo-gt ord s t) (lpo-gt ord t s))))
;; weight is asymmetric
(check-property big
                (property ([f1 (gen:one-of '(a b c f g))] [n1 (gen:integer-in 0 2)]
                                                          [f2 (gen:one-of '(a b c f g))]
                                                          [n2 (gen:integer-in 0 2)])
                          (or (and (eq? f1 f2) (= n1 n2))
                              (not (and (weight '(a b c f g) (cons f1 n1) (cons f2 n2))
                                        (weight '(a b c f g) (cons f2 n2) (cons f1 n1)))))))

;; rewriting with the +/* rules computes the right number and is idempotent
(define arith-eqs
  (list '(atom (rel = (fn + (fn |0|) (var x)) (var x)))
        '(atom (rel = (fn + (fn S (var x)) (var y)) (fn S (fn + (var x) (var y)))))
        '(atom (rel = (fn * (fn |0|) (var x)) (fn |0|)))
        '(atom (rel = (fn * (fn S (var x)) (var y)) (fn + (fn * (var x) (var y)) (var y))))))
(check-property mid
                (property ([t (nat-gen 2)]) (equal? (rewrite arith-eqs t) (numeral (nat-value t)))))
(check-property mid
                (property ([t (nat-gen 2)])
                          (equal? (rewrite arith-eqs (rewrite arith-eqs t)) (rewrite arith-eqs t))))

;; congruence closure decides valid ground equational implications
(check-property
 low
 (property ([s gen:gterm] [t gen:gterm] [u gen:gterm])
           (and (ccvalid `(atom (rel = ,s ,s)))
                (ccvalid `(imp (and (atom (rel = ,s ,t)) (atom (rel = ,t ,u))) (atom (rel = ,s ,u))))
                (ccvalid `(imp (atom (rel = ,s ,t)) (atom (rel = (fn f ,s) (fn f ,t))))))))
