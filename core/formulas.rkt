#lang racket/base

;; formulas --- generic syntax operations and printing for the
;; polymorphic formula type, shared by propositional and first-order
;; logic.
;;
;; Formulas are s-expressions:
;;   #t | #f
;;   (atom a)
;;   (not p) | (and p q) | (or p q) | (imp p q) | (iff p q)
;;   (forall x p) | (exists x p)

(require racket/match)
(require (only-in "lib.rkt" setify))

(provide (all-defined-out))

;; ===== constructors =====
(define (mk-and p q)
  `(and ,p ,q))
(define (mk-or p q)
  `(or ,p ,q))
(define (mk-imp p q)
  `(imp ,p ,q))
(define (mk-iff p q)
  `(iff ,p ,q))
(define (mk-forall x p)
  `(forall ,x ,p))
(define (mk-exists x p)
  `(exists ,x ,p))

;; ===== destructors =====
(define (dest-imp fm)
  (match fm
    [`(imp ,p ,q) (cons p q)]
    [_ (error 'dest-imp "dest_imp")]))
(define (antecedent fm)
  (car (dest-imp fm)))
(define (consequent fm)
  (cdr (dest-imp fm)))
(define (dest-iff fm)
  (match fm
    [`(iff ,p ,q) (cons p q)]
    [_ (error 'dest-iff "dest_iff")]))
(define (dest-and fm)
  (match fm
    [`(and ,p ,q) (cons p q)]
    [_ (error 'dest-and "dest_and")]))
(define (dest-or fm)
  (match fm
    [`(or ,p ,q) (cons p q)]
    [_ (error 'dest-or "dest_or")]))

(define (conjuncts fm)
  (match fm
    [`(and ,p ,q) (append (conjuncts p) (conjuncts q))]
    [_ (list fm)]))

(define (disjuncts fm)
  (match fm
    [`(or ,p ,q) (append (disjuncts p) (disjuncts q))]
    [_ (list fm)]))

;; right-associative reduce of a non-empty list: (f x1 (f x2 (... xn)))
(define (end-itlist f l)
  (cond
    [(null? l) (error 'end-itlist "empty list")]
    [(null? (cdr l)) (car l)]
    [else (f (car l) (end-itlist f (cdr l)))]))

(define (list-conj l)
  (if (null? l)
      #t
      (end-itlist mk-and l)))
(define (list-disj l)
  (if (null? l)
      #f
      (end-itlist mk-or l)))

;; ===== mapping / folding over atoms =====
(define (onatoms f fm)
  (match fm
    [`(atom ,a) (f a)]
    [`(not ,p) `(not ,(onatoms f p))]
    [`(,(and o (or 'and 'or 'imp 'iff)) ,p ,q) `(,o ,(onatoms f p) ,(onatoms f q))]
    [`(,(and qf (or 'forall 'exists)) ,x ,p) `(,qf ,x ,(onatoms f p))]
    [_ fm]))

(define (overatoms f fm b)
  (match fm
    [`(atom ,a) (f a b)]
    [`(not ,p) (overatoms f p b)]
    [`(,(or 'and 'or 'imp 'iff) ,p ,q) (overatoms f p (overatoms f q b))]
    [`(,(or 'forall 'exists) ,x ,p) (overatoms f p b)]
    [_ b]))

;; collect (f atom) over every atom, deduplicated. setify is needed because
;; the same atom can occur many times in fm (e.g. (and (atom p) (atom p))).
(define (atom-union f fm)
  (setify (overatoms (λ (h t) (append (f h) t)) fm '())))

;; ===== pretty printer =====
;; Produces the usual ASCII logic syntax: ~ /\ \/ ==> <=> forall exists.

;; collect a run of like quantifiers: (forall x (forall y p)) -> ((x y), p).
;; The (eq? Q Q2) guard requires the nested quantifier to be the SAME kind,
;; so a switch (forall x (exists y p)) stops the run, returning ((x), (exists y p)).
(define (strip-quant fm)
  (match fm
    [`(,(and Q (or 'forall 'exists)) ,x ,(and yp (list Q2 _ _)))
     #:when (eq? Q Q2)
     (let-values ([(xs bod) (strip-quant yp)])
       (values (cons x xs) bod))]
    [`(,(or 'forall 'exists) ,x ,p) (values (list x) p)]
    [_ (values '() fm)]))

;; pfn : (prec atom) -> string  (atom printer, receives surrounding precedence)
(define (formula->string pfn fm)
  (define (br b s)
    (if b
        (string-append "(" s ")")
        s))
  (define (go pr fm)
    (match fm
      [#f "false"]
      [#t "true"]
      [`(atom ,a) (pfn pr a)]
      [`(not ,p) (br (> pr 10) (string-append "~" (go 11 p)))]
      [`(and ,p ,q) (br (> pr 8) (infix 8 "/\\" p q))]
      [`(or ,p ,q) (br (> pr 6) (infix 6 "\\/" p q))]
      [`(imp ,p ,q) (br (> pr 4) (infix 4 "==>" p q))]
      [`(iff ,p ,q) (br (> pr 2) (infix 2 "<=>" p q))]
      [`(forall ,x ,p) (br (> pr 0) (qnt "forall" fm))]
      [`(exists ,x ,p) (br (> pr 0) (qnt "exists" fm))]))
  ;; print a binary connective at precedence newpr. The left operand is
  ;; printed at (add1 newpr) and the right at newpr, so a same-connective
  ;; chain a op b op c brackets to the left -- matching the right-associative
  ;; AST a op (b op c) by parenthesising the nested right operand only.
  (define (infix newpr sym p q)
    (string-append (go (add1 newpr) p) " " sym " " (go newpr q)))
  (define (qnt name fm)
    (define-values (bvs bod) (strip-quant fm))
    (string-append name
                   (apply string-append (map (λ (v) (string-append " " (symbol->string v))) bvs))
                   ". "
                   (go 0 bod)))
  (go 0 fm))

(define (print-formula pfn fm)
  (display (formula->string pfn fm)))
(define (print-qformula pfn fm)
  (display (string-append "<<" (formula->string pfn fm) ">>")))
