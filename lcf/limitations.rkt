#lang racket/base

;; limitations.fs --- the limitative results: Goedel numbering and
;; diagonalization, the Delta-decider and Sigma/Pi/Delta classification, the
;; Sigma_1 verifier, Turing machines, and the Robinson ground-term evaluator.
;;
;; Scope note: the book's second half builds Robinson-arithmetic *provability*
;; (robinson_thm, sigma_prove, ...) as a long tactic proof in which every
;; axiom/lemma is a concrete-syntax `parse "..."`. This port has no string
;; parser (s-expressions are the AST), so that demonstration is omitted; the
;; computational content of the chapter is ported in full below.

(require racket/match)
(require (only-in racket/list range))
(require (only-in "../core/lib.rkt" funpow update undefined apply tryapplyd defined first))
(require (only-in "../core/formulas.rkt" consequent))
(require (only-in "../fol/fol.rkt" subst fvt))
(require (only-in "../equality/equal.rkt" mk-eq dest-eq rhs))
(require "lcf.rkt")
(require "lcfprop.rkt")
(require "folderived.rkt")

(provide (all-defined-out))

;; ===== numerals (zero/successor form) =====
(define (numeral n)
  (if (= n 0)
      `(fn |0|)
      `(fn S ,(numeral (- n 1)))))

;; ===== string -> number (bijective) =====
(define (number s)
  (foldr (λ (i g) (+ (+ 1 (char->integer (string-ref s i))) (* 256 g)))
         0
         (range 0 (string-length s))))

;; ===== injective pairing =====
(define (pair x y)
  (+ (* (+ x y) (+ x y)) x 1))

;; ===== Goedel numbering =====
(define (gterm tm)
  (match tm
    [`(var ,x) (pair 0 (number (symbol->string x)))]
    [`(fn |0|) (pair 1 0)]
    [`(fn S ,t) (pair 2 (gterm t))]
    [`(fn + ,s ,t) (pair 3 (pair (gterm s) (gterm t)))]
    [`(fn * ,s ,t) (pair 4 (pair (gterm s) (gterm t)))]
    [_ (error 'gterm "not in the language")]))

(define (gform fm)
  (match fm
    [#f (pair 0 0)]
    [#t (pair 0 1)]
    [`(atom (rel = ,s ,t)) (pair 1 (pair (gterm s) (gterm t)))]
    [`(atom (rel < ,s ,t)) (pair 2 (pair (gterm s) (gterm t)))]
    [`(atom (rel <= ,s ,t)) (pair 3 (pair (gterm s) (gterm t)))]
    [`(not ,p) (pair 4 (gform p))]
    [`(and ,p ,q) (pair 5 (pair (gform p) (gform q)))]
    [`(or ,p ,q) (pair 6 (pair (gform p) (gform q)))]
    [`(imp ,p ,q) (pair 7 (pair (gform p) (gform q)))]
    [`(iff ,p ,q) (pair 8 (pair (gform p) (gform q)))]
    [`(forall ,x ,p) (pair 9 (pair (number (symbol->string x)) (gform p)))]
    [`(exists ,x ,p) (pair 10 (pair (number (symbol->string x)) (gform p)))]
    [_ (error 'gform "not in the language")]))

(define (gnumeral n)
  (gterm (numeral n)))

;; ===== diagonalization =====
(define (diag x p)
  (subst (update x (numeral (gform p)) undefined) p))
(define (qdiag x p)
  `(exists ,x (and ,(mk-eq `(var ,x) (numeral (gform p))) ,p)))

;; ===== decider for delta-sentences =====
(define (dtermval v tm)
  (match tm
    [`(var ,x) (apply v x)]
    [`(fn |0|) 0]
    [`(fn S ,t) (+ (dtermval v t) 1)]
    [`(fn + ,s ,t) (+ (dtermval v s) (dtermval v t))]
    [`(fn * ,s ,t) (* (dtermval v s) (dtermval v t))]
    [_ (error 'dtermval "not a ground term")]))

(define (dholds v fm)
  (match fm
    [#f #f]
    [#t #t]
    [`(atom (rel = ,s ,t)) (= (dtermval v s) (dtermval v t))]
    [`(atom (rel < ,s ,t)) (< (dtermval v s) (dtermval v t))]
    [`(atom (rel <= ,s ,t)) (<= (dtermval v s) (dtermval v t))]
    [`(not ,p) (not (dholds v p))]
    [`(and ,p ,q) (and (dholds v p) (dholds v q))]
    [`(or ,p ,q) (or (dholds v p) (dholds v q))]
    [`(imp ,p ,q) (or (not (dholds v p)) (dholds v q))]
    [`(iff ,p ,q) (eq? (dholds v p) (dholds v q))]
    [`(forall ,x (imp (atom (rel ,a (var ,y) ,t)) ,p)) (dhquant andmap v x y a t p)]
    [`(exists ,x (and (atom (rel ,a (var ,y) ,t)) ,p)) (dhquant ormap v x y a t p)]
    [_ (error 'dholds "not an arithmetical delta-formula")]))

(define (dhquant pred v x y a t p)
  (if (or (not (equal? x y)) (member x (fvt t)))
      (error 'dholds "not delta")
      (let ([m (if (equal? a '<)
                   (- (dtermval v t) 1)
                   (dtermval v t))])
        (pred (λ (n) (dholds (update x n v) p)) (range 0 (add1 m))))))

;; ===== Sigma / Pi / Delta classification =====
(define (opp c)
  (case c
    [(sigma) 'pi]
    [(pi) 'sigma]
    [(delta) 'delta]))

(define (classify c n fm)
  (match fm
    [(or #f #t) #t]
    [`(atom ,_) #t]
    [`(not ,p) (classify (opp c) n p)]
    [`(and ,p ,q) (and (classify c n p) (classify c n q))]
    [`(or ,p ,q) (and (classify c n p) (classify c n q))]
    [`(imp ,p ,q) (and (classify (opp c) n p) (classify c n q))]
    [`(iff ,p ,q) (and (classify 'delta n p) (classify 'delta n q))]
    [`(exists ,x ,p)
     #:when (and (not (= n 0)) (eq? c 'sigma))
     (classify c n p)]
    [`(forall ,x ,p)
     #:when (and (not (= n 0)) (eq? c 'pi))
     (classify c n p)]
    [`(exists ,x (and (atom (rel ,(or '< '<=) (var ,y) ,t)) ,p))
     #:when (and (equal? x y) (not (member x (fvt t))))
     (classify c n p)]
    [`(forall ,x (imp (atom (rel ,(or '< '<=) (var ,y) ,t)) ,p))
     #:when (and (equal? x y) (not (member x (fvt t))))
     (classify c n p)]
    [`(exists ,x ,p) (and (not (= n 0)) (classify (opp c) (- n 1) fm))]
    [`(forall ,x ,p) (and (not (= n 0)) (classify (opp c) (- n 1) fm))]))

;; ===== verification of true Sigma_1 / refutation of false Pi_1 =====
(define (veref sign m v fm)
  (match fm
    [#f (sign #f)]
    [#t (sign #t)]
    [`(atom (rel = ,s ,t)) (sign (= (dtermval v s) (dtermval v t)))]
    [`(atom (rel < ,s ,t)) (sign (< (dtermval v s) (dtermval v t)))]
    [`(atom (rel <= ,s ,t)) (sign (<= (dtermval v s) (dtermval v t)))]
    [`(not ,p) (veref (λ (x) (not (sign x))) m v p)]
    [`(and ,p ,q) (sign (and (sign (veref sign m v p)) (sign (veref sign m v q))))]
    [`(or ,p ,q) (sign (or (sign (veref sign m v p)) (sign (veref sign m v q))))]
    [`(imp ,p ,q) (veref sign m v `(or (not ,p) ,q))]
    [`(iff ,p ,q) (veref sign m v `(and (imp ,p ,q) (imp ,q ,p)))]
    [`(exists ,x ,p)
     #:when (sign #t)
     (ormap (λ (n) (veref sign m (update x n v) p)) (range 0 (add1 m)))]
    [`(forall ,x ,p)
     #:when (sign #f)
     (ormap (λ (n) (veref sign m (update x n v) p)) (range 0 (add1 m)))]
    [`(forall ,x (imp (atom (rel ,a (var ,y) ,t)) ,p))
     #:when (sign #t)
     (verefboundquant m v x y a t sign p)]
    [`(exists ,x (and (atom (rel ,a (var ,y) ,t)) ,p))
     #:when (sign #f)
     (verefboundquant m v x y a t sign p)]))

(define (verefboundquant m v x y a t sign p)
  (if (or (not (equal? x y)) (member x (fvt t)))
      (error 'veref "veref")
      (let ([m2 (if (equal? a '<)
                    (- (dtermval v t) 1)
                    (dtermval v t))])
        (andmap (λ (n) (veref sign m2 (update x n v) p)) (range 0 (add1 m2))))))

(define (sholds m v fm)
  (veref (λ (x) x) m v fm))
(define (sigma-bound fm)
  (first 0 (λ (n) (sholds n undefined fm))))

;; ===== Turing machines =====
;; tape = (tape head fn) ; config = (config state tape) ; symbols 'blank/'one ;
;; directions 'left/'right/'stay ; program = hash (state . symbol) -> (char dir state')
(define (look tp)
  (match-define `(tape ,r ,f) tp)
  (tryapplyd f r 'blank))
(define (twrite s tp)
  (match-define `(tape ,r ,f) tp)
  (list 'tape r (update r s f)))
(define (move dir tp)
  (match-define `(tape ,r ,f) tp)
  (list 'tape
        (+ r
           (cond
             [(eq? dir 'left) -1]
             [(eq? dir 'right) 1]
             [else 0]))
        f))

(define (run prog cfg)
  (match-define `(config ,state ,tp) cfg)
  (define stt (cons state (look tp)))
  (if (defined prog stt)
      (match-let ([`(,char ,dir ,state*) (apply prog stt)])
        (run prog (list 'config state* (move dir (twrite char tp)))))
      cfg))

(define (input-tape args)
  (define (writen n tp)
    (funpow n (λ (t) (move 'left (twrite 'one t))) (move 'left (twrite 'blank tp))))
  (foldr writen (list 'tape 0 undefined) args))

(define (output-tape tp)
  (define tp* (move 'right tp))
  (if (eq? (look tp*) 'blank)
      0
      (+ 1 (output-tape tp*))))

(define (exec prog args)
  (match-define `(config ,_ ,t) (run prog (list 'config 1 (input-tape args))))
  (output-tape t))

;; ===== Robinson arithmetic axioms (as s-expressions) =====
(define robinson
  `(and
    (forall
     m
     (forall n (imp (atom (rel = (fn S (var m)) (fn S (var n)))) (atom (rel = (var m) (var n))))))
    (and
     (forall n
             (iff (not (atom (rel = (var n) (fn |0|))))
                  (exists m (atom (rel = (var n) (fn S (var m)))))))
     (and
      (forall n (atom (rel = (fn + (fn |0|) (var n)) (var n))))
      (and
       (forall m
               (forall n (atom (rel = (fn + (fn S (var m)) (var n)) (fn S (fn + (var m) (var n)))))))
       (and (forall n (atom (rel = (fn * (fn |0|) (var n)) (fn |0|))))
            (and (forall m
                         (forall n
                                 (atom (rel =
                                            (fn * (fn S (var m)) (var n))
                                            (fn + (var n) (fn * (var m) (var n)))))))
                 (and (forall m
                              (forall n
                                      (iff (atom (rel <= (var m) (var n)))
                                           (exists d (atom (rel = (fn + (var m) (var d)) (var n)))))))
                      (forall m
                              (forall n
                                      (iff (atom (rel < (var m) (var n)))
                                           (atom (rel <= (fn S (var m)) (var n))))))))))))))

(define robinson-axioms (conjths robinson))
(define suc-inj (list-ref robinson-axioms 0))
(define num-cases (list-ref robinson-axioms 1))
(define add-0 (list-ref robinson-axioms 2))
(define add-suc (list-ref robinson-axioms 3))
(define mul-0 (list-ref robinson-axioms 4))
(define mul-suc (list-ref robinson-axioms 5))
(define le-def (list-ref robinson-axioms 6))
(define lt-def (list-ref robinson-axioms 7))

;; ===== "right-handed" derived rules =====
(define (right-spec t th)
  (imp-trans th (ispec t (consequent (concl th)))))
(define (right-imp-trans th1 th2)
  (imp-unduplicate (imp-front 2 (imp-trans2 th1 (imp-swap th2)))))
(define (right-sym th)
  (match-define `(,s . ,t) (dest-eq (consequent (concl th))))
  (imp-trans th (eq-sym s t)))
(define (right-trans th1 th2)
  (match-define `(,s . ,t) (dest-eq (consequent (concl th1))))
  (match-define `(,t2 . ,u) (dest-eq (consequent (concl th2))))
  (imp-trans-chain (list th1 th2) (eq-trans s t u)))

;; ===== Robinson ground-term evaluation (produces kernel proofs) =====
(define (robop tm)
  (match tm
    [`(fn ,op (fn |0|) ,t)
     (if (equal? op '*)
         (right-spec t mul-0)
         (right-trans (right-spec t add-0) (robeval t)))]
    [`(fn ,op (fn S ,u) ,t)
     (define th2 (foldr right-spec (if (equal? op '+) add-suc mul-suc) (list t u)))
     (right-trans th2 (robeval (rhs (consequent (concl th2)))))]))

(define (robeval tm)
  (match tm
    [`(fn S ,t)
     (define th (robeval t))
     (imp-trans th (axiom-funcong 'S (list t) (list (rhs (consequent (concl th))))))]
    [`(fn ,op ,s ,t)
     (define th1 (robeval s))
     (define s* (rhs (consequent (concl th1))))
     (define th3 (axiom-funcong op (list s t) (list s* t)))
     (define th4 (modusponens (imp-swap th3) (axiom-eqrefl t)))
     (right-trans (imp-trans th1 th4) (robop `(fn ,op ,s* ,t)))]
    [_ (add-assum robinson (axiom-eqrefl tm))]))
