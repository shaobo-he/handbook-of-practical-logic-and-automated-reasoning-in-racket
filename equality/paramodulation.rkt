#lang racket/base

;; paramodulation.fs --- paramodulation: rewriting with (non-oriented)
;; equations inside clauses during the resolution loop.

(require racket/match)
(require (only-in racket/list append*))
(require (only-in "../core/lib.rkt" subtract image insert mapfilter))
(require (only-in "../core/formulas.rkt" list-conj))
(require (only-in "../prop/prop.rkt" simpcnf simpdnf))
(require (only-in "../fol/fol.rkt" subst generalize))
(require (only-in "../fol/skolem.rkt" specialize pnf askolemize))
(require (only-in "equal.rkt" mk-eq dest-eq is-eq))
(require (only-in "completion.rkt" overlaps listcases))
(require (only-in "../fol/resolution.rkt" rename resolve-clauses incorporate))

(provide (all-defined-out))

(define paramodulation-verbose (make-parameter #f))

;; ===== paramodulation within a literal / clause =====
(define (overlapl lr fm rfn)
  (match fm
    [`(atom (rel ,f ,@args))
     (listcases (λ (t rf) (overlaps lr t rf))
                (λ (i a) (rfn i `(atom (rel ,f ,@a))))
                args '())]
    [`(not ,p) (overlapl lr p (λ (i p2) (rfn i `(not ,p2))))]
    [_ (error 'overlapl "not a literal")]))

(define (overlapc lr cl rfn acc)
  (listcases (λ (l rf) (overlapl lr l rf)) rfn cl acc))

;; ===== overall paramodulation of ocl by the equations in pcl =====
(define (paramodulate pcl ocl)
  (foldr (λ (eq acc)
           (define pcl* (subtract pcl (list eq)))
           (define st (dest-eq eq))
           (define l (car st)) (define r (cdr st))
           (define (rfn i ocl*) (image (λ (lit) (subst i lit)) (append pcl* ocl*)))
           (overlapc (cons l r) ocl rfn (overlapc (cons r l) ocl rfn acc)))
         '() (filter is-eq pcl)))

(define (para-clauses cls1 cls2)
  (define cls1* (rename "x" cls1))
  (define cls2* (rename "y" cls2))
  (append (paramodulate cls1* cls2*) (paramodulate cls2* cls1*)))

;; ===== resolution loop extended with paramodulation =====
(define (paraloop used unused)
  (match unused
    ['() (error 'paramodulation "No proof found")]
    [(cons cls ros)
     (when (paramodulation-verbose) (printf "~a used; ~a unused.\n" (length used) (length unused)))
     (define used* (insert cls used))
     (define news
       (append (append* (mapfilter (λ (c) (resolve-clauses cls c)) used*))
               (append* (mapfilter (λ (c) (para-clauses cls c)) used*))))
     (if (member '() news)
         #t
         (paraloop used* (foldr (λ (n acc) (incorporate cls n acc)) ros news)))]))

(define (pure-paramodulation fm)
  (paraloop '() (cons (list (mk-eq '(var x) '(var x)))
                      (simpcnf (specialize (pnf fm))))))

(define (paramodulation fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (pure-paramodulation (list-conj d))) (simpdnf fm1)))
