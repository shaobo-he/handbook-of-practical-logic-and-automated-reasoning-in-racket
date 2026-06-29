#lang racket/base

;; Property tests for skolem.rkt: the normal-form transformers are idempotent
;; and produce the expected SHAPE -- nnf eliminates imp/iff and pushes negation
;; to the atoms, prenex/pnf float every quantifier to the front, specialize
;; strips leading universals, and askolemize removes all existentials.

(require rackcheck
         rackunit
         racket/match
         "common.rkt")
(require (only-in "../../fol/skolem.rkt" simplify nnf prenex pnf specialize askolemize))

;; ===== a first-order formula generator (atoms over P,Q and vars x,y) =====
(define (fol-gen n)
  (define as
    '((atom (rel P (var x))) (atom (rel P (var y))) (atom (rel Q (var x))) (atom (rel Q (var y)))))
  (if (<= n 0)
      (gen:one-of as)
      (gen:frequency (list (cons 1 (gen:one-of as))
                           (cons 2 (gen:map (fol-gen (sub1 n)) (λ (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or imp iff) fol-gen n))
                           (cons 2 (quant-gen '(forall exists) '(x y) fol-gen n))))))

;; ===== shape predicates (oracles) =====
;; negation-normal form: no imp/iff anywhere, negation only on atoms
(define (nnf-shape? fm)
  (match fm
    [(or #t #f) #t]
    [`(atom ,_) #t]
    [`(not (atom ,_)) #t]
    [`(not ,_) #f]
    [`(and ,p ,q) (and (nnf-shape? p) (nnf-shape? q))]
    [`(or ,p ,q) (and (nnf-shape? p) (nnf-shape? q))]
    [`(forall ,_ ,p) (nnf-shape? p)]
    [`(exists ,_ ,p) (nnf-shape? p)]
    [_ #f]))

;; quantifier-free matrix (no forall/exists below this point)
(define (quant-free? fm)
  (match fm
    [(or #t #f) #t]
    [`(atom ,_) #t]
    [`(not ,p) (quant-free? p)]
    [`(,(or 'and 'or 'imp 'iff) ,p ,q) (and (quant-free? p) (quant-free? q))]
    [`(,(or 'forall 'exists) ,_ ,_) #f]
    [_ #t]))

;; prenex normal form: a block of leading quantifiers over a quantifier-free body
(define (prenex-shape? fm)
  (match fm
    [`(,(or 'forall 'exists) ,_ ,p) (prenex-shape? p)]
    [_ (quant-free? fm)]))

;; no existential quantifier appears anywhere
(define (no-exists? fm)
  (match fm
    [(or #t #f) #t]
    [`(atom ,_) #t]
    [`(not ,p) (no-exists? p)]
    [`(,(or 'and 'or 'imp 'iff) ,p ,q) (and (no-exists? p) (no-exists? q))]
    [`(forall ,_ ,p) (no-exists? p)]
    [`(exists ,_ ,_) #f]
    [_ #t]))

;; ===== idempotence of each transformer =====
(check-property mid (property ([fm gen:prop]) (equal? (simplify (simplify fm)) (simplify fm))))
(check-property mid (property ([fm (fol-gen 3)]) (equal? (simplify (simplify fm)) (simplify fm))))
(check-property mid (property ([fm gen:prop]) (equal? (nnf (nnf fm)) (nnf fm))))
(check-property mid (property ([fm (fol-gen 3)]) (equal? (nnf (nnf fm)) (nnf fm))))
(check-property mid (property ([fm (fol-gen 3)]) (equal? (prenex (prenex fm)) (prenex fm))))
(check-property mid (property ([fm gen:prop]) (equal? (pnf (pnf fm)) (pnf fm))))
(check-property mid (property ([fm (fol-gen 3)]) (equal? (pnf (pnf fm)) (pnf fm))))

;; ===== structural shape of the outputs =====
(check-property mid (property ([fm (fol-gen 3)]) (nnf-shape? (nnf fm))))
;; pnf (= prenex . nnf . simplify) is the transform that yields true prenex form
(check-property mid (property ([fm (fol-gen 3)]) (prenex-shape? (pnf fm))))
;; specialize never leaves a leading universal
(check-property big
                (property ([fm (fol-gen 3)])
                          (match (specialize fm)
                            [`(forall ,_ ,_) #f]
                            [_ #t])))
;; askolemize eliminates every existential quantifier
(check-property mid (property ([fm (fol-gen 3)]) (no-exists? (askolemize fm))))
