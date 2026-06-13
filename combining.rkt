#lang racket/base

;; combining.fs --- the Nelson-Oppen combined decision procedure.
;;
;; A "language" is a list (fn-pred pred-pred decision-proc): which function
;; and predicate symbols it owns, and a procedure that decides its formulas.

(require racket/match)
(require (only-in racket/list partition range))
(require (only-in "lib.rkt"
                  unions union subtract fpf update undefined can tryfind distinctpairs))
(require (only-in "formulas.rkt" list-conj dest-imp))
(require (only-in "prop.rkt" simpdnf negate))
(require (only-in "fol.rkt" fv fvt functions subst generalize))
(require (only-in "skolem.rkt" simplify))
(require (only-in "equal.rkt" mk-eq predicates))
(require (only-in "cong.rkt" ccvalid))
(require (only-in "cooper.rkt" is-numeral integer-qelim))
(require (only-in "real.rkt" real-qelim))
(require (only-in "defcnf.rkt" var-index))

(provide (all-defined-out))

;; ===== built-in languages =====
(define real-lang
  (let ([fn '((- . 1) (+ . 2) (- . 2) (* . 2) (^ . 2))]
        [pr '((<= . 2) (< . 2) (>= . 2) (> . 2))])
    (list (λ (sn) (or (and (= (cdr sn) 0) (is-numeral `(fn ,(car sn)))) (and (member sn fn) #t)))
          (λ (sn) (and (member sn pr) #t))
          (λ (fm) (equal? (real-qelim (generalize fm)) #t)))))

(define int-lang
  (let ([fn '((- . 1) (+ . 2) (- . 2) (* . 2))]
        [pr '((<= . 2) (< . 2) (>= . 2) (> . 2))])
    (list (λ (sn) (or (and (= (cdr sn) 0) (is-numeral `(fn ,(car sn)))) (and (member sn fn) #t)))
          (λ (sn) (and (member sn pr) #t))
          (λ (fm) (equal? (integer-qelim (generalize fm)) #t)))))

;; ===== add uninterpreted functions / equality as a default language =====
(define (add-default langs)
  (append langs
          (list (list (λ (sn) (not (ormap (λ (l) ((car l) sn)) langs)))
                      (λ (sn) (equal? sn (cons '= 2)))
                      ccvalid))))

;; ===== choose a language to homogenize an atom =====
(define (chooselang langs fm)
  (match fm
    [`(atom (rel = (fn ,f ,@args) ,_)) (findf (λ (l) ((car l) (cons f (length args)))) langs)]
    [`(atom (rel = ,_ (fn ,f ,@args))) (findf (λ (l) ((car l) (cons f (length args)))) langs)]
    [`(atom (rel ,p ,@args)) (findf (λ (l) ((cadr l) (cons p (length args)))) langs)]))

;; ===== CPS listify =====
;; f takes (elem cont n defs); cont takes (result-list n defs); (n,defs) thread.
(define (listify f l cont n defs)
  (match l
    ['() (cont '() n defs)]
    [(cons h t)
     (f h (λ (h* n2 d2) (listify f t (λ (t* n3 d3) (cont (cons h* t*) n3 d3)) n2 d2)) n defs)]))

;; ===== homogenization =====
(define (homot lang tm cont n defs)
  (match tm
    [`(var ,x) (cont tm n defs)]
    [`(fn ,f ,@args)
     (if ((car lang) (cons f (length args)))
         (listify (λ (a c n2 d2) (homot lang a c n2 d2)) args
                  (λ (a n2 d2) (cont `(fn ,f ,@a) n2 d2)) n defs)
         (let ([nv `(var ,(string->symbol (string-append "v_" (number->string n))))])
           (cont nv (+ n 1) (cons (mk-eq nv tm) defs))))]))

(define (homol langs fm cont n defs)
  (match fm
    [`(not ,f) (homol langs f (λ (p n2 d2) (cont `(not ,p) n2 d2)) n defs)]
    [`(atom (rel ,p ,@args))
     (define lang (chooselang langs fm))
     (listify (λ (a c n2 d2) (homot lang a c n2 d2)) args
              (λ (a n2 d2) (cont `(atom (rel ,p ,@a)) n2 d2)) n defs)]
    [_ (error 'homol "not a literal")]))

(define (homo langs fms cont n defs)
  (listify (λ (f c n2 d2) (homol langs f c n2 d2)) fms
           (λ (dun n2 defs2)
             (if (null? defs2)
                 (cont dun n2 defs2)
                 (homo langs defs2 (λ (res n3 d3) (cont (append dun res) n3 d3)) n2 '())))
           n defs))

(define (homogenize langs fms)
  (define fvs (unions (map fv fms)))
  (define n (+ 1 (foldr (λ (v acc) (max acc (var-index "v_" v))) 0 fvs)))
  (homo langs fms (λ (res n2 defs2) res) n '()))

;; ===== language membership / partition =====
(define (belongs lang fm)
  (and (andmap (car lang) (functions fm))
       (andmap (cadr lang) (subtract (predicates fm) (list (cons '= 2))))))

(define (langpartition langs fms)
  (match langs
    ['() (if (null? fms) '() (error 'langpartition "langpartition"))]
    [(cons l ls)
     (define-values (fms1 fms2) (partition (λ (fm) (belongs l fm)) fms))
     (cons fms1 (langpartition ls fms2))]))

;; ===== arrangements of variable partitions =====
(define (arreq l)
  (match l
    [(list* v1 v2 rest) (cons (mk-eq `(var ,v1) `(var ,v2)) (arreq (cons v2 rest)))]
    [_ '()]))

(define (arrangement part)
  (foldr (λ (p acc) (union (arreq p) acc))
         (map (λ (vw) `(not ,(mk-eq `(var ,(car vw)) `(var ,(cdr vw)))))
              (distinctpairs (map car part)))
         part))

;; ===== reduce with trivial equations =====
(define (dest-def fm)
  (match fm
    [`(atom (rel = (var ,x) ,t)) #:when (not (member x (fvt t))) (cons x t)]
    [`(atom (rel = ,t (var ,x))) #:when (not (member x (fvt t))) (cons x t)]
    [_ (error 'dest-def "dest_def")]))

(define (redeqs eqs)
  (define eq (findf (λ (e) (can dest-def e)) eqs))
  (if eq
      (let ([xt (dest-def eq)])
        (redeqs (map (λ (e) (subst (update (car xt) (cdr xt) undefined) e)) (subtract eqs (list eq)))))
      eqs))

;; ===== Nelson-Oppen =====
(define (trydps ldseps fms)
  (ormap (λ (lsep) (let ([dp (caddr (car lsep))] [fms0 (cdr lsep)])
                     (dp `(not ,(list-conj (redeqs (append fms0 fms)))))))
         ldseps))

(define (allpartitions l)
  (define (allinsertions x ll acc)
    (foldr (λ (p acc) (cons (cons (cons x p) (subtract ll (list p))) acc))
           (cons (cons (list x) ll) acc)
           ll))
  (foldr (λ (h y) (foldr (λ (part acc) (allinsertions h part acc)) '() y)) (list '()) l))

(define (findasubset p m l)
  (if (= m 0)
      (p '())
      (match l
        ['() (error 'findasubset "findasubset")]
        [(cons h t)
         (with-handlers ([exn:fail? (λ (e) (findasubset p m t))])
           (findasubset (λ (s) (p (cons h s))) (- m 1) t))])))

(define (findsubset p l)
  (tryfind (λ (n) (findasubset (λ (x) (if (p x) x (error 'findsubset ""))) n l))
           (range 0 (add1 (length l)))))

(define (nelop-refute eqs ldseps)
  (with-handlers ([exn:fail? (λ (e) #f)])
    (define dj (findsubset (λ (s) (trydps ldseps (map negate s))) eqs))
    (andmap (λ (eq)
              (nelop-refute (subtract eqs (list eq))
                            (map (λ (lsep) (cons (car lsep) (cons eq (cdr lsep)))) ldseps)))
            dj)))

(define (nelop1 langs fms0)
  (define fms (homogenize langs fms0))
  (define seps (langpartition langs fms))
  (define fvlist (map (λ (sep) (unions (map fv sep))) seps))
  (define vars (filter (λ (x) (>= (length (filter (λ (fl) (member x fl)) fvlist)) 2)) (unions fvlist)))
  (define eqs (map (λ (ab) (mk-eq `(var ,(car ab)) `(var ,(cdr ab)))) (distinctpairs vars)))
  (nelop-refute eqs (map cons langs seps)))

(define (nelop langs fm)
  (andmap (λ (d) (nelop1 langs d)) (simpdnf (simplify `(not ,fm)))))
