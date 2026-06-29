#lang racket/base

;; real --- quantifier elimination for real-closed fields, via the
;; Cohen-Hormander algorithm (sign matrices over a set of polynomials).

(require racket/match)
(require (only-in racket/list last))
(require (only-in "../core/lib.rkt" index butlast insertat chop-list subtract))
(require (only-in "../core/formulas.rkt" atom-union))
(require (only-in "../prop/prop.rkt" eval dnf))
(require (only-in "../fol/fol.rkt" generalize))
(require (only-in "../fol/skolem.rkt" simplify))
(require (only-in "qelim.rkt" lift-qelim cnnf))
(require (only-in "cooper.rkt" zero evalc relativize))
(require (only-in "complex.rkt"
                  poly-cmul
                  poly-neg
                  poly-mul
                  head
                  degree
                  is-constant
                  behead
                  pdivide
                  findsign
                  assertsign
                  split-zero
                  swap
                  polyatom
                  init-sgns))

(provide (all-defined-out))

;; ===== formal derivative =====
(define (poly-diffn x n p)
  (match p
    [`(fn + ,c (fn * ,y ,q))
     #:when (equal? y x)
     `(fn + ,(poly-cmul n c) (fn * ,x ,(poly-diffn x (+ n 1) q)))]
    [_ (poly-cmul n p)]))

(define (poly-diff vars p)
  (match p
    [`(fn + ,c (fn * (var ,x) ,q))
     #:when (equal? x (car vars))
     (poly-diffn `(var ,x) 1 q)]
    [_ zero]))

;; ===== evaluate a quantifier-free formula given a sign-matrix row =====
(define rel-signs
  (list (cons '= '(zero))
        (cons '<= '(zero negative))
        (cons '>= '(zero positive))
        (cons '< '(negative))
        (cons '> '(positive))))

(define (testform pmat fm)
  (eval fm
        (λ (at)
          (match at
            [`(rel ,a ,p ,z) (and (member (cdr (assoc p pmat)) (cdr (assoc a rel-signs))) #t)]))))

;; ===== sign inference =====
(define (inferpsign pdqd)
  (define pd (car pdqd))
  (define qd (cdr pdqd))
  (with-handlers ([exn:fail? (λ (e) (cons 'nonzero pd))])
    (cons (list-ref qd (index 'zero pd)) pd)))

(define (condense ps)
  (match ps
    [`(,iv ,pt . ,other)
     (define rest (condense other))
     (if (member 'zero pt)
         (cons iv (cons pt rest))
         rest)]
    [_ ps]))

;; Fill in the sign of each polynomial on the open intervals between its roots,
;; given the signs at the roots themselves. Walking consecutive (left, right)
;; sample signs: equal nonzero signs persist across the interval; opposite signs
;; force a zero crossing, so a 'zero point is spliced in between. 'nonzero or two
;; adjacent zeros mean the sample data is inconsistent and should never occur.
(define (inferisign ps)
  (match ps
    [`(,(and x (cons l ls)) (,_ . ,ints) . ,(and pts (cons (cons r rs) xs)))
     (match* (l r)
       [('zero 'zero) (error 'inferisign "inconsistent")]
       [('nonzero _) (error 'inferisign "indeterminate")]
       [(_ 'nonzero) (error 'inferisign "indeterminate")]
       [('zero _) (cons x (cons (cons r ints) (inferisign pts)))]
       [(_ 'zero) (cons x (cons (cons l ints) (inferisign pts)))]
       [('negative 'negative) (cons x (cons (cons l ints) (inferisign pts)))]
       [('positive 'positive) (cons x (cons (cons l ints) (inferisign pts)))]
       [(_ _)
        (cons x
              (cons (cons l ints) (cons (cons 'zero ints) (cons (cons r ints) (inferisign pts)))))])]
    [_ ps]))

;; Derive the sign matrix for a set of polynomials from the matrix for the larger
;; set {derivative + remainders, originals}. l is half the row length: each row
;; holds the q-signs in its first half and the p-derived signs in its second.
;; inferpsign reads off the sign of each original poly, inferisign then fills the
;; inter-root intervals, and the trailing column bookkeeping is dropped.
(define (dedmatrix cont mat)
  (define l (quotient (length (car mat)) 2))
  (define mat1
    (condense (map (λ (row)
                     (let-values ([(a b) (chop-list l row)])
                       (inferpsign (cons a b))))
                   mat)))
  (define mat2
    (cons (list (swap #t (list-ref (car mat1) 1)))
          (append mat1 (list (list (list-ref (last mat1) 1))))))
  (define mat3 (butlast (cdr (inferisign mat2))))
  (cont (condense (map (λ (l) (cons (car l) (cddr l))) mat3))))

;; ===== sign-preserving pseudo-division =====
(define (pdivide-pos vars sgns s p)
  (define a (head vars p))
  (define-values (k r) (pdivide vars s p))
  (define sgn (findsign sgns a))
  (cond
    [(eq? sgn 'zero) (error 'pdivide-pos "zero head coefficient")]
    [(or (eq? sgn 'positive) (= (modulo k 2) 0)) r]
    [(eq? sgn 'negative) (poly-neg r)]
    [else (poly-mul vars a r)]))

;; ===== sign case-splitting =====
(define (split-sign sgns pol cont)
  (match (findsign sgns pol)
    ['nonzero
     (define fm `(atom (rel > ,pol ,zero)))
     `(or (and ,fm ,(cont (assertsign sgns (cons pol 'positive))))
          (and (not ,fm) ,(cont (assertsign sgns (cons pol 'negative)))))]
    [_ (cont sgns)]))

(define (split-trichotomy sgns pol cont-z cont-pn)
  (split-zero sgns pol cont-z (λ (s) (split-sign s pol cont-pn))))

;; ===== recursive sign-matrix evaluation =====
;; Process the polynomial list one at a time, case-splitting on the sign of each
;; head coefficient (split-trichotomy). dun accumulates polynomials already fixed
;; as nonzero; the zero-branch recurses on (behead p) since the leading term
;; vanishes, the nonzero-branch keeps p at full degree. When pols is empty the
;; accumulated set is handed to `matrix` to build the actual sign matrix.
(define (casesplit vars dun pols cont sgns)
  (match pols
    ['() (matrix vars dun cont sgns)]
    [`(,p . ,ops)
     (define zbranch
       (if (is-constant vars p)
           (λ (s) (delconst vars dun p ops cont s))
           (λ (s) (casesplit vars dun (cons (behead vars p) ops) cont s))))
     (define nbranch
       (if (is-constant vars p)
           (λ (s) (delconst vars dun p ops cont s))
           (λ (s) (casesplit vars (append dun (list p)) ops cont s))))
     (split-trichotomy sgns (head vars p) zbranch nbranch)]))

(define (delconst vars dun p ops cont sgns)
  (define (cont* m)
    (cont (map (λ (row) (insertat (length dun) (findsign sgns p) row)) m)))
  (casesplit vars dun ops cont* sgns))

;; Build the sign matrix for `pols` (Cohen-Hormander). Pick a highest-degree
;; polynomial p, form its derivative p* and pseudo-divide every other poly by p
;; to get remainders gs of lower degree; recursively get the matrix for
;; {p*, others, gs}, from which p's own sign column is reconstructed (insertat i).
(define (matrix vars pols cont sgns)
  (if (null? pols)
      (with-handlers ([exn:fail? (λ (e) #f)])
        (cont (list '())))
      (let ()
        (define p (car (sort pols (λ (a b) (> (degree vars a) (degree vars b))))))
        (define p* (poly-diff vars p))
        (define i (index p pols))
        (define-values (p1 p2) (chop-list i pols))
        (define qs (cons p* (append p1 (cdr p2))))
        (define gs (map (λ (q) (pdivide-pos vars sgns p q)) qs))
        (define (cont* m)
          (cont (map (λ (l) (insertat i (car l) (cdr l))) m)))
        (casesplit vars '() (append qs gs) (λ (mat) (dedmatrix cont* mat)) sgns))))

;; ===== quantifier elimination =====
(define (basic-real-qelim vars fm)
  (match fm
    [`(exists ,x ,p)
     (define pols
       (atom-union (λ (at)
                     (match at
                       [`(rel ,a ,t (fn |0|)) (list t)]
                       [_ '()]))
                   p))
     (define (cont mat)
       (if (ormap (λ (m) (testform (map cons pols m) p)) mat) #t #f))
     (casesplit (cons x vars) '() pols cont init-sgns)]))

(define real-qelim
  (λ (fm)
    (simplify (evalc ((lift-qelim polyatom
                                  (λ (g) (simplify (evalc g)))
                                  (λ (vars) (λ (f) (basic-real-qelim vars f))))
                      fm)))))

(define real-qelim*
  (λ (fm)
    (simplify (evalc ((lift-qelim polyatom
                                  (λ (g) (dnf ((cnnf (λ (x) x)) (evalc g))))
                                  (λ (vars) (λ (f) (basic-real-qelim vars f))))
                      fm)))))

;; ===== group-theory-via-reals example helpers =====
(define (grpterm tm)
  (match tm
    [`(var ,x) tm]
    [`(fn * ,s ,t) `(fn * ,(grpterm s) (fn + (fn |1|) (fn * (fn |2|) ,(grpterm t))))]
    [`(fn i ,t) `(fn ^ ,(grpterm t) (fn |2|))]
    [`(fn |1|) `(fn |2|)]))

(define (grpform fm)
  (match fm
    [`(atom (rel = ,s ,t))
     (relativize (λ (x) `(atom (rel > (var ,x) (fn |1|))))
                 (generalize `(atom (rel > ,(grpterm s) ,(grpterm t)))))]))
