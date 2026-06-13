#lang racket/base

;; geom.fs --- geometry theorem proving by coordinate translation and a
;; trivial version of Wu's method (triangulation + pseudo-division).

(require racket/match)
(require (only-in racket/list partition range))
(require (only-in "../core/lib.rkt" fpf update undefined union subtract set-eq))
(require (only-in "../core/formulas.rkt" onatoms conjuncts dest-imp end-itlist))
(require (only-in "../fol/fol.rkt" subst fv fvt tsubst))
(require (only-in "cooper.rkt" zero))
(require (only-in "complex.rkt" is-constant degree pdivide coefficients head polyatom))
(require (only-in "../equality/equal.rkt" mk-eq lhs))

(provide (all-defined-out))

(define (sym+ v suffix) (string->symbol (string-append (symbol->string v) suffix)))

;; ===== geometric properties as coordinate formulas =====
;; generic point n has coordinates (var |n_x|), (var |n_y|)
(define coordinations
  (list
   (cons 'collinear
         '(atom (rel = (fn * (fn - (var |1_x|) (var |2_x|)) (fn - (var |2_y|) (var |3_y|)))
                       (fn * (fn - (var |1_y|) (var |2_y|)) (fn - (var |2_x|) (var |3_x|))))))
   (cons 'parallel
         '(atom (rel = (fn * (fn - (var |1_x|) (var |2_x|)) (fn - (var |3_y|) (var |4_y|)))
                       (fn * (fn - (var |1_y|) (var |2_y|)) (fn - (var |3_x|) (var |4_x|))))))
   (cons 'perpendicular
         '(atom (rel = (fn + (fn * (fn - (var |1_x|) (var |2_x|)) (fn - (var |3_x|) (var |4_x|)))
                             (fn * (fn - (var |1_y|) (var |2_y|)) (fn - (var |3_y|) (var |4_y|))))
                       (fn |0|))))
   (cons 'lengths_eq
         '(atom (rel = (fn + (fn ^ (fn - (var |1_x|) (var |2_x|)) (fn |2|))
                             (fn ^ (fn - (var |1_y|) (var |2_y|)) (fn |2|)))
                       (fn + (fn ^ (fn - (var |3_x|) (var |4_x|)) (fn |2|))
                             (fn ^ (fn - (var |3_y|) (var |4_y|)) (fn |2|))))))
   (cons 'is_midpoint
         '(and (atom (rel = (fn * (fn |2|) (var |1_x|)) (fn + (var |2_x|) (var |3_x|))))
               (atom (rel = (fn * (fn |2|) (var |1_y|)) (fn + (var |2_y|) (var |3_y|))))))
   (cons 'is_intersection
         '(and (atom (rel = (fn * (fn - (var |1_x|) (var |2_x|)) (fn - (var |2_y|) (var |3_y|)))
                            (fn * (fn - (var |1_y|) (var |2_y|)) (fn - (var |2_x|) (var |3_x|)))))
               (atom (rel = (fn * (fn - (var |1_x|) (var |4_x|)) (fn - (var |4_y|) (var |5_y|)))
                            (fn * (fn - (var |1_y|) (var |4_y|)) (fn - (var |4_x|) (var |5_x|)))))))
   (cons '=
         '(and (atom (rel = (var |1_x|) (var |2_x|))) (atom (rel = (var |1_y|) (var |2_y|)))))))

;; ===== convert a formula to coordinate form =====
(define (coordinate fm)
  (onatoms
   (λ (at)
     (match at
       [`(rel ,a ,@args)
        (define vs (map (λ (arg) (match arg [`(var ,v) v])) args))
        (define xtms (map (λ (v) `(var ,(sym+ v "_x"))) vs))
        (define ytms (map (λ (v) `(var ,(sym+ v "_y"))) vs))
        (define n (length args))
        (define xs (map (λ (i) (string->symbol (string-append (number->string i) "_x"))) (range 1 (add1 n))))
        (define ys (map (λ (i) (string->symbol (string-append (number->string i) "_y"))) (range 1 (add1 n))))
        (subst (fpf (append xs ys) (append xtms ytms)) (cdr (assoc a coordinations)))]))
   fm))

;; ===== invariance checks =====
(define (invariant x*y* sz)
  (define x* (car x*y*)) (define y* (cdr x*y*))
  (define z (cdr sz))
  (define (m n f)
    (define x (string->symbol (string-append (number->string n) "_x")))
    (define y (string->symbol (string-append (number->string n) "_y")))
    (define i (fpf '(x y) (list `(var ,x) `(var ,y))))
    (update x (tsubst i x*) (update y (tsubst i y*) f)))
  `(iff ,z ,(subst (foldr m undefined (range 1 6)) z)))

(define (invariant-under-translation sz)
  (invariant (cons '(fn + (var x) (var X)) '(fn + (var y) (var Y))) sz))

(define (invariant-under-rotation sz)
  `(imp (atom (rel = (fn + (fn ^ (var s) (fn |2|)) (fn ^ (var c) (fn |2|))) (fn |1|)))
        ,(invariant (cons '(fn - (fn * (var c) (var x)) (fn * (var s) (var y)))
                          '(fn + (fn * (var s) (var x)) (fn * (var c) (var y)))) sz)))

(define (invariant-under-scaling sz)
  `(imp (not (atom (rel = (var A) (fn |0|))))
        ,(invariant (cons '(fn * (var A) (var x)) '(fn * (var A) (var y))) sz)))

(define (invariant-under-shearing sz)
  (invariant (cons '(fn + (var x) (fn * (var b) (var y))) '(var y)) sz))

;; ===== choose origin and zero a coordinate =====
(define (originate fm)
  (match-define (list* a b ovs) (fv fm))
  (subst (fpf (list (sym+ a "_x") (sym+ a "_y") (sym+ b "_y")) (list zero zero zero))
         (coordinate fm)))

;; ===== Wu's method =====
(define (pprove vars triang p degens)
  (if (equal? p zero)
      degens
      (match triang
        ['() (cons (mk-eq p zero) degens)]
        [(cons (and q `(fn + ,c (fn * (var ,x) ,_))) qs)
         (if (not (equal? x (car vars)))
             (if (member (car vars) (fvt p))
                 (foldr (λ (coef acc) (pprove vars triang coef acc)) degens (coefficients vars p))
                 (pprove (cdr vars) triang p degens))
             (let-values ([(k p*) (pdivide vars p q)])
               (if (= k 0)
                   (pprove vars qs p* degens)
                   (let ([degens* (cons `(not ,(mk-eq (head vars q) zero)) degens)])
                     (foldr (λ (coef acc) (pprove vars qs coef acc)) degens* (coefficients vars p*))))))])))

(define (triangulate vars consts pols)
  (cond
    [(null? vars) pols]
    [else
     (define-values (cns tpols) (partition (λ (p) (is-constant vars p)) pols))
     (cond
       [(not (null? cns)) (triangulate vars (append cns consts) tpols)]
       [(<= (length pols) 1) (append pols (triangulate (cdr vars) '() consts))]
       [else
        (define n (end-itlist min (map (λ (p) (degree vars p)) pols)))
        (define p (findf (λ (p) (= (degree vars p) n)) pols))
        (define ps (subtract pols (list p)))
        (triangulate vars consts
                     (cons p (map (λ (q) (let-values ([(k r) (pdivide vars q p)]) r)) ps)))])]))

(define (wu fm vars zeros)
  (define gfm0 (coordinate fm))
  (define gfm (subst (foldr (λ (v acc) (update v zero acc)) undefined zeros) gfm0))
  (if (not (set-eq vars (fv gfm)))
      (error 'wu "bad parameters")
      (let ()
        (define ant-con (dest-imp gfm))
        (define pols (map (λ (c) (lhs (polyatom vars c))) (conjuncts (car ant-con))))
        (define ps (map (λ (c) (lhs (polyatom vars c))) (conjuncts (cdr ant-con))))
        (define tri (triangulate vars '() pols))
        (foldr (λ (p acc) (union (pprove vars tri p '()) acc)) '() ps))))
