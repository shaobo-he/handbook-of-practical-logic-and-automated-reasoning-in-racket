#lang racket/base

;; Property-based tests (rackcheck). Random inputs cross-validate independent
;; implementations against each other and against trusted oracles (truth
;; tables, native Racket arithmetic, prime?, finite-model evaluation), check
;; algebraic laws (set/ring/order axioms), round-trips, and structural
;; invariants -- function by function across every chapter.
;;
;; Local-only: needs `raco pkg install rackcheck`; CI does not run this file.

(require rackunit
         rackcheck
         racket/match)
(require (only-in racket/list remove-duplicates))
(require (only-in math/number-theory prime?))
(require (only-in "../core/lib.rkt"
                  setify
                  union
                  intersect
                  subtract
                  subset
                  psubset
                  set-eq
                  image
                  allpairs
                  distinctpairs
                  allsubsets
                  non
                  funpow
                  undefined
                  update
                  undefine
                  apply
                  tryapplyd
                  defined
                  fpf
                  dom
                  graph
                  mapf
                  earlier
                  unequal
                  canonize
                  equivalent
                  equate))
(require (only-in "../core/formulas.rkt"
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
(require (only-in "../core/intro.rkt" [simplify intro-simplify] parse-exp string-of-exp))
(require (only-in "../prop/prop.rkt"
                  eval
                  atoms
                  tautology
                  satisfiable
                  unsatisfiable
                  psimplify
                  nnf
                  nenf
                  dual
                  dnf
                  cnf))
(require (only-in "../prop/dp.rkt" dptaut dplltaut dpsat dpllsat dplbsat dplbtaut))
(require (only-in "../prop/bdd.rkt"
                  mk-bdd
                  mkbdd
                  expand-node
                  bdd-and
                  bdd-or
                  bdd-imp
                  bdd-iff
                  bddtaut
                  ebddtaut))
(require (only-in "../prop/stal.rkt" stalmarck))
(require (only-in "../prop/propexamples.rkt" prime mk-adder-test ramsey))
(require (only-in "../fol/fol.rkt" holds generalize tsubst fvt fv var))
(require (only-in "../fol/skolem.rkt" [nnf skolem-nnf] [simplify skolem-simplify] prenex pnf))
(require (only-in "../fol/unif.rkt" fullunify unify-and-apply))
(require (only-in "../fol/meson.rkt" meson))
(require (only-in "../fol/tableaux.rkt" tab))
(require (only-in "../equality/equal.rkt" mk-eq dest-eq lhs rhs is-eq function-congruence))
(require (only-in "../equality/cong.rkt" subterms ccvalid))
(require (only-in "../equality/order.rkt" termsize lpo-gt lpo-ge weight))
(require (only-in "../equality/rewrite.rkt" rewrite))
(require (only-in "../decidable/cooper.rkt" integer-qelim lint dest-numeral))
(require (only-in "../decidable/qelim.rkt" quelim-dlo))
(require (only-in "../decidable/complex.rkt" complex-qelim polynate poly-add poly-neg poly-mul))
(require (only-in "../decidable/real.rkt" real-qelim poly-diff))
(require (only-in "../decidable/grobner.rkt" grobner-decide mpolynate mpoly-add mpoly-neg mpoly-mul))
(require (only-in "../lcf/lcf.rkt" concl))
(require (only-in "../lcf/lcfprop.rkt" lcftaut imp-refl add-assum))
(require (only-in "../lcf/folderived.rkt" eq-sym ispec))
(require (only-in "../lcf/limitations.rkt" numeral dtermval dholds robeval gnumeral look twrite move))

;; ===== configs: high volume, scaled down only for expensive procedures =====
(define big (make-config #:tests 1500))
(define mid (make-config #:tests 400))
(define low (make-config #:tests 120))
(define tiny (make-config #:tests 30))
(define poly (make-config #:tests 250))

;; ===== generator helpers =====
(define (binop-gen ops sub n)
  (gen:bind (gen:one-of ops)
            (lambda (op)
              (gen:map (gen:tuple (sub (quotient n 2)) (sub (quotient n 2)))
                       (lambda (pq) `(,op ,(car pq) ,(cadr pq)))))))
(define (quant-gen quants vars sub n)
  (gen:bind (gen:one-of quants)
            (lambda (q)
              (gen:bind (gen:one-of vars)
                        (lambda (v) (gen:map (sub (sub1 n)) (lambda (p) `(,q ,v ,p))))))))

(define (prop-gen-over as n [consts? #t])
  (define base
    (if consts?
        (gen:choice (gen:one-of as) (gen:const #t) (gen:const #f))
        (gen:one-of as)))
  (let loop ([n n])
    (if (<= n 0)
        base
        (gen:frequency (list (cons 1 base)
                             (cons 2 (gen:map (loop (sub1 n)) (lambda (p) `(not ,p))))
                             (cons 4 (binop-gen '(and or imp iff) loop n)))))))
(define gen:prop (prop-gen-over '((atom p) (atom q) (atom r)) 4))
(define gen:small-prop (prop-gen-over '((atom (rel p)) (atom (rel q))) 3))
;; constant-free formulas: lcftaut (the LCF kernel prover) targets formulas over
;; genuine atoms and does not handle the #t/#f constants
(define gen:prop-nc (prop-gen-over '((atom p) (atom q) (atom r)) 4 #f))

(define (aoi-gen n)
  (if (<= n 0)
      (gen:one-of '((atom p) (atom q) (atom r)))
      (gen:frequency (list (cons 1 (gen:one-of '((atom p) (atom q) (atom r))))
                           (cons 2 (gen:map (aoi-gen (sub1 n)) (lambda (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or) aoi-gen n))))))

(define (term-gen n)
  (if (<= n 0)
      (gen:choice (gen:one-of '((var x) (var y) (var z))) (gen:const '(fn a)))
      (gen:frequency (list (cons 2 (gen:one-of '((var x) (var y) (var z))))
                           (cons 1 (gen:const '(fn a)))
                           (cons 2 (gen:map (term-gen (sub1 n)) (lambda (t) `(fn f ,t))))
                           (cons 2
                                 (gen:map (gen:tuple (term-gen (sub1 n)) (term-gen (sub1 n)))
                                          (lambda (st) `(fn g ,(car st) ,(cadr st)))))))))
(define gen:term (term-gen 3))
(define (gterm-gen n)
  (if (<= n 0)
      (gen:one-of '((fn a) (fn b) (fn c)))
      (gen:frequency (list (cons 1 (gen:one-of '((fn a) (fn b) (fn c))))
                           (cons 2 (gen:map (gterm-gen (sub1 n)) (lambda (t) `(fn f ,t))))
                           (cons 2
                                 (gen:map (gen:tuple (gterm-gen (sub1 n)) (gterm-gen (sub1 n)))
                                          (lambda (st) `(fn g ,(car st) ,(cadr st)))))))))
(define gen:gterm (gterm-gen 3))

(define gen:nat (gen:integer-in 0 6))
(define gen:natlist (gen:list gen:nat #:max-length 6))

;; ========================================================================= ;;
;; Chapter 1: lib (sets, finite partial functions, union-find)
;; ========================================================================= ;;
(check-property big (property ([a gen:natlist] [b gen:natlist]) (set-eq (union a b) (union b a))))
(check-property big
                (property ([a gen:natlist] [b gen:natlist] [c gen:natlist])
                          (set-eq (union (union a b) c) (union a (union b c)))))
(check-property big (property ([a gen:natlist]) (set-eq (union a a) a)))
(check-property big
                (property ([a gen:natlist] [b gen:natlist]) (set-eq (intersect a b) (intersect b a))))
(check-property big
                (property ([a gen:natlist] [b gen:natlist]) ; absorption
                          (set-eq (intersect a (union a b)) a)))
(check-property big
                (property ([a gen:natlist] [b gen:natlist]) ; de Morgan-ish decomposition
                          (set-eq (union (subtract a b) (intersect a b)) a)))
(check-property big
                (property ([a gen:natlist] [b gen:natlist])
                          (and (subset (subtract a b) a) (null? (intersect (subtract a b) b)))))
(check-property big (property ([a gen:natlist]) (subset a a)))
(check-property big
                (property ([a gen:natlist] [b gen:natlist] [c gen:natlist])
                          (or (not (subset a b)) (not (subset b c)) (subset a c))))
(check-property big
                (property ([a gen:natlist] [b gen:natlist]) ; agrees with native sets
                          (eq? (and (subset a b) #t) (andmap (lambda (x) (and (member x b) #t)) a))))
(check-property big (property ([a gen:natlist]) (not (psubset a a))))
(check-property big
                (property ([a gen:natlist] [b gen:natlist]) (not (and (psubset a b) (psubset b a)))))
(check-property big (property ([a gen:natlist]) (set-eq (setify (append a a)) a)))
(check-property big
                (property ([a gen:natlist]) (= (length (setify a)) (length (remove-duplicates a)))))
(check-property big
                (property ([a gen:natlist] [b gen:natlist])
                          (= (length (allpairs cons a b)) (* (length a) (length b)))))
(check-property big
                (property ([a gen:natlist])
                          (= (length (distinctpairs a))
                             (quotient (* (length a) (sub1 (length a))) 2))))
(check-property big (property ([a gen:natlist]) (= (length (allsubsets a)) (expt 2 (length a)))))
(check-property big
                (property ([a gen:natlist] [k gen:nat])
                          (<= (length (image (lambda (x) (modulo x 3)) a)) (length a))))
(check-property big
                (property ([k gen:nat] [m (gen:integer-in 0 5)]
                                       [n (gen:integer-in 0 5)]) ; funpow additivity
                          (= (funpow (+ m n) add1 k) (funpow m add1 (funpow n add1 k)))))
;; finite partial functions
(check-property big
                (property ([k gen:nat] [v gen:nat] [f gen:natlist])
                          (= (apply (update k v (fpf f f)) k) v)))
(check-property big
                (property ([k gen:nat] [j gen:nat] [v gen:nat])
                          (or (= j k) (= (tryapplyd (update k v undefined) j 99) 99))))
(check-property big
                (property ([k gen:nat] [v gen:nat])
                          (not (defined (undefine k (update k v undefined)) k))))
(check-property big (property ([ks gen:natlist]) (let ([d (setify ks)]) (set-eq (dom (fpf d d)) d))))
(check-property big
                (property ([ks gen:natlist])
                          (let ([d (setify ks)])
                            (andmap (lambda (kv) (= (apply (fpf d d) (car kv)) (cdr kv)))
                                    (graph (fpf d d))))))
(check-property big
                (property ([ks gen:natlist] [k gen:nat])
                          (let ([d (setify ks)])
                            (or (not (member k d)) (= (apply (mapf add1 (fpf d d)) k) (add1 k))))))
;; union-find
(check-property big (property ([a gen:nat] [b gen:nat]) (equivalent (equate (cons a b) unequal) a b)))
(check-property big
                (property ([a gen:nat] [b gen:nat] [c gen:nat]) ; transitivity of merging
                          (equivalent (equate (cons b c) (equate (cons a b) unequal)) a c)))
(check-property big
                (property ([a gen:nat] [b gen:nat])
                          (let ([p (equate (cons a b) unequal)])
                            (equal? (canonize p (canonize p a)) (canonize p a)))))

;; ========================================================================= ;;
;; Chapter 1: formulas (constructors / destructors / collectors)
;; ========================================================================= ;;
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

;; ========================================================================= ;;
;; Chapter 1: intro (expression simplifier / parser / printer)
;; ========================================================================= ;;
(define (expr-gen n)
  (if (<= n 0)
      (gen:choice (gen:map (gen:integer-in 0 5) (lambda (k) `(const ,k)))
                  (gen:one-of '((var "x") (var "y"))))
      (gen:bind (gen:one-of '(add mul))
                (lambda (op)
                  (gen:map (gen:tuple (expr-gen (sub1 n)) (expr-gen (sub1 n)))
                           (lambda (ab) `(,op ,(car ab) ,(cadr ab))))))))
(define (eval-expr e env)
  (match e
    [`(var ,s) (hash-ref env s)]
    [`(const ,k) k]
    [`(add ,a ,b) (+ (eval-expr a env) (eval-expr b env))]
    [`(mul ,a ,b) (* (eval-expr a env) (eval-expr b env))]))
(check-property big
                (property ([e (expr-gen 4)] [vx (gen:integer-in -3 3)] [vy (gen:integer-in -3 3)])
                          (= (eval-expr e (hash "x" vx "y" vy))
                             (eval-expr (intro-simplify e) (hash "x" vx "y" vy)))))
(check-property big
                (property ([e (expr-gen 4)])
                          (equal? (intro-simplify (intro-simplify e)) (intro-simplify e))))
(check-property big
                (property ([e (expr-gen 3)] [vx (gen:integer-in -3 3)] [vy (gen:integer-in -3 3)])
                          (= (eval-expr e (hash "x" vx "y" vy))
                             (eval-expr (parse-exp (string-of-exp 0 e)) (hash "x" vx "y" vy)))))

;; ========================================================================= ;;
;; Chapter 2: propositional logic and SAT
;; ========================================================================= ;;
;; eval is a homomorphism on the connectives
(check-property
 big
 (property ([p gen:prop] [q gen:prop] [b1 gen:boolean] [b2 gen:boolean] [b3 gen:boolean])
           (define v
             (lambda (s)
               (case s
                 [(p) b1]
                 [(q) b2]
                 [(r) b3]
                 [else #f])))
           (and (eq? (eval `(and ,p ,q) v) (and (eval p v) (eval q v)))
                (eq? (eval `(or ,p ,q) v) (or (eval p v) (eval q v)))
                (eq? (eval `(imp ,p ,q) v) (or (not (eval p v)) (eval q v)))
                (eq? (eval `(iff ,p ,q) v) (eq? (eval p v) (eval q v)))
                (eq? (eval `(not ,p) v) (not (eval p v))))))
;; every tautology checker agrees with the truth-table oracle
(check-property mid
                (property ([fm gen:prop])
                          (let ([t (tautology fm)])
                            (and (eq? t (bddtaut fm))
                                 (eq? t (ebddtaut fm))
                                 (eq? t (dptaut fm))
                                 (eq? t (dplltaut fm))
                                 (eq? t (dplbtaut fm))))))
;; every satisfiability checker agrees
(check-property mid
                (property ([fm gen:prop])
                          (let ([s (satisfiable fm)])
                            (and (eq? s (dpsat fm)) (eq? s (dpllsat fm)) (eq? s (dplbsat fm))))))
;; satisfiable / unsatisfiable are dual
(check-property mid (property ([fm gen:prop]) (eq? (satisfiable fm) (not (unsatisfiable fm)))))
;; Stalmarck soundness: a returned verdict matches the oracle
(check-property mid
                (property ([fm gen:prop])
                          (define r
                            (with-handlers ([exn:fail? (lambda (e) 'unknown)])
                              (stalmarck fm)))
                          (or (eq? r 'unknown) (eq? r (tautology fm)))))
;; normal forms preserve meaning
(check-property mid (property ([fm gen:prop]) (tautology `(iff ,fm ,(nnf fm)))))
(check-property mid (property ([fm gen:prop]) (tautology `(iff ,fm ,(nenf fm)))))
(check-property mid (property ([fm gen:prop]) (tautology `(iff ,fm ,(dnf fm)))))
(check-property mid (property ([fm gen:prop]) (tautology `(iff ,fm ,(cnf fm)))))
(check-property mid (property ([fm gen:prop]) (tautology `(iff ,fm ,(psimplify fm)))))
;; normal-form idempotence and structure
(check-property mid (property ([fm gen:prop]) (equal? (psimplify (psimplify fm)) (psimplify fm))))
(define (nnf-shape? fm)
  (match fm
    [(or #t #f) #t]
    [`(atom ,_) #t]
    [`(not (atom ,_)) #t]
    [`(and ,p ,q) (and (nnf-shape? p) (nnf-shape? q))]
    [`(or ,p ,q) (and (nnf-shape? p) (nnf-shape? q))]
    [_ #f]))
(check-property mid (property ([fm gen:prop]) (nnf-shape? (nnf fm))))
;; dual is an involution on the {and,or,not} fragment
(check-property big (property ([fm (aoi-gen 4)]) (equal? (dual (dual fm)) fm)))
;; propexamples against oracles
(check-property low (property ([p (gen:integer-in 2 20)]) (eq? (bddtaut (prime p)) (prime? p))))
(check-property tiny
                (property ([n (gen:integer-in 1 3)] [k (gen:integer-in 1 3)])
                          (bddtaut (mk-adder-test n k))))
;; Ramsey: ramsey(3,3,n) is a tautology iff n >= R(3,3) = 6
(check-property (make-config #:tests 10)
                (property ([n (gen:integer-in 2 6)]) (eq? (dplltaut (ramsey 3 3 n)) (>= n 6))))

;; ========================================================================= ;;
;; Chapter 2: BDD (canonicity, the diagram as a decision function, combinators)
;; ========================================================================= ;;
(define (fresh-bc)
  (cons (mk-bdd symbol<?) undefined))
(define (eval-bdd b root v)
  (cond
    [(= root 1) #t]
    [(= root -1) #f]
    [else
     (match-define (list s l r) (expand-node b root))
     (if (v s)
         (eval-bdd b l v)
         (eval-bdd b r v))]))
;; canonicity: two formulas get the same node iff they are logically equivalent
(check-property mid
                (property ([fm1 gen:prop] [fm2 gen:prop])
                          (define-values (bc1 r1) (mkbdd (fresh-bc) fm1))
                          (define-values (bc2 r2) (mkbdd bc1 fm2))
                          (eq? (= r1 r2) (tautology `(iff ,fm1 ,fm2)))))
;; the diagram computes exactly the truth-table function
(check-property mid
                (property ([fm gen:prop] [b1 gen:boolean] [b2 gen:boolean] [b3 gen:boolean])
                          (define v
                            (lambda (s)
                              (case s
                                [(p) b1]
                                [(q) b2]
                                [(r) b3]
                                [else #f])))
                          (define-values (bc root) (mkbdd (fresh-bc) fm))
                          (eq? (eval-bdd (car bc) root v) (eval fm v))))
;; negation is a complemented edge: root flips sign
(check-property mid
                (property ([fm gen:prop])
                          (define-values (bc1 r1) (mkbdd (fresh-bc) fm))
                          (define-values (_ r2) (mkbdd bc1 `(not ,fm)))
                          (= r2 (- r1))))
;; the binary combinators match building the compound formula directly
(define (bdd-combiner op)
  (case op
    [(and) bdd-and]
    [(or) bdd-or]
    [(imp) bdd-imp]
    [(iff) bdd-iff]))
(check-property mid
                (property ([op (gen:one-of '(and or imp iff))] [fm1 gen:prop] [fm2 gen:prop])
                          (define-values (bc1 r1) (mkbdd (fresh-bc) fm1))
                          (define-values (bc2 r2) (mkbdd bc1 fm2))
                          (define-values (bc3 rc) ((bdd-combiner op) bc2 (cons r1 r2)))
                          (define-values (_ rd) (mkbdd bc3 `(,op ,fm1 ,fm2)))
                          (= rc rd)))

;; ========================================================================= ;;
;; Chapter 3: first-order logic, unification, provers
;; ========================================================================= ;;
;; fvt distributes over function application
(check-property big
                (property ([a gen:term] [b gen:term])
                          (set-eq (fvt `(fn g ,a ,b)) (union (fvt a) (fvt b)))))
;; skolem's simplify/NNF/prenex/PNF preserve truth in every finite model
(define fmdom '(0 1))
(define (nofunc f args)
  (error "no function symbols"))
(define (mk-pred p0 p1 q0 q1)
  (lambda (psym args)
    (define d (car args))
    (cond
      [(eq? psym 'P) (if (= d 0) p0 p1)]
      [(eq? psym 'Q) (if (= d 0) q0 q1)])))
(define (fol-gen n)
  (define as
    '((atom (rel P (var x))) (atom (rel P (var y))) (atom (rel Q (var x))) (atom (rel Q (var y)))))
  (if (<= n 0)
      (gen:one-of as)
      (gen:frequency (list (cons 1 (gen:one-of as))
                           (cons 2 (gen:map (fol-gen (sub1 n)) (lambda (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or imp iff) fol-gen n))
                           (cons 2 (quant-gen '(forall exists) '(x y) fol-gen n))))))
(check-property
 mid
 (property ([fm0 (fol-gen 3)] [p0 gen:boolean] [p1 gen:boolean] [q0 gen:boolean] [q1 gen:boolean])
           (define fm (generalize fm0))
           (define pred (mk-pred p0 p1 q0 q1))
           (define h (holds fmdom nofunc pred (hash) fm))
           (and (null? (fv fm))
                (eq? h (holds fmdom nofunc pred (hash) (skolem-nnf fm)))
                (eq? h (holds fmdom nofunc pred (hash) (skolem-simplify fm)))
                (eq? h (holds fmdom nofunc pred (hash) (prenex fm)))
                (eq? h (holds fmdom nofunc pred (hash) (pnf fm))))))
;; holds and negation are complementary
(check-property
 mid
 (property ([fm0 (fol-gen 3)] [p0 gen:boolean] [p1 gen:boolean] [q0 gen:boolean] [q1 gen:boolean])
           (define fm (generalize fm0))
           (define pred (mk-pred p0 p1 q0 q1))
           (not (eq? (holds fmdom nofunc pred (hash) fm)
                     (holds fmdom nofunc pred (hash) `(not ,fm))))))
;; unification: soundness, symmetry, idempotence of the solved form
(define (unifiable? s t)
  (with-handlers ([exn:fail? (lambda (e) #f)])
    (fullunify (list (cons s t)))
    #t))
(check-property mid
                (property ([s gen:term] [t gen:term])
                          (with-handlers ([exn:fail? (lambda (e) #t)])
                            (andmap (lambda (e) (equal? (car e) (cdr e)))
                                    (unify-and-apply (list (cons s t)))))))
(check-property mid (property ([s gen:term] [t gen:term]) (eq? (unifiable? s t) (unifiable? t s))))
(check-property mid
                (property ([s gen:term] [t gen:term])
                          (or (not (unifiable? s t))
                              (let ([sig (fullunify (list (cons s t)))])
                                (equal? (tsubst sig (tsubst sig s)) (tsubst sig s))))))
;; MESON and the tableau prover prove every (small) propositional tautology
(check-property low
                (property ([fm gen:small-prop])
                          (or (not (tautology fm))
                              (and (andmap exact-nonnegative-integer? (meson fm))
                                   (exact-nonnegative-integer? (tab fm))))))

;; ========================================================================= ;;
;; Chapter 4: equality, term orderings, rewriting
;; ========================================================================= ;;
(check-property big (property ([s gen:term] [t gen:term]) (equal? (dest-eq (mk-eq s t)) (cons s t))))
(check-property
 big
 (property ([s gen:term] [t gen:term])
           (and (equal? (lhs (mk-eq s t)) s) (equal? (rhs (mk-eq s t)) t) (is-eq (mk-eq s t)))))
(check-property big
                (property ([k (gen:integer-in 1 4)])
                          (= (length (function-congruence (cons 'f k))) 1)))
(check-property big (property () (null? (function-congruence (cons 'c 0)))))
;; subterms includes the term itself and is reflexive on variables
(check-property big (property ([t gen:term]) (and (member t (subterms t)) #t)))
;; termsize: positive, and additive over arguments
(check-property big (property ([t gen:term]) (>= (termsize t) 1)))
(check-property big
                (property ([a gen:term] [b gen:term])
                          (= (termsize `(fn g ,a ,b)) (+ 1 (termsize a) (termsize b)))))
;; the lexicographic path order is a strict order with the subterm property
(define ord (lambda (p q) (weight '(a b c f g) p q)))
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
(define (nat-gen n)
  (if (<= n 0)
      (gen:map (gen:integer-in 0 3) numeral)
      (gen:bind (gen:one-of '(+ *))
                (lambda (op)
                  (gen:map (gen:tuple (nat-gen (sub1 n)) (nat-gen (sub1 n)))
                           (lambda (ab) `(fn ,op ,(car ab) ,(cadr ab))))))))
(define (nat-value t)
  (match t
    [`(fn |0|) 0]
    [`(fn S ,a) (add1 (nat-value a))]
    [`(fn + ,a ,b) (+ (nat-value a) (nat-value b))]
    [`(fn * ,a ,b) (* (nat-value a) (nat-value b))]))
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

;; ========================================================================= ;;
;; Chapter 5: polynomial / linear arithmetic and decision procedures
;; ========================================================================= ;;
(define (cnum k)
  `(fn ,(string->symbol (number->string k))))
(define (poly-term-gen n)
  (if (<= n 0)
      (gen:choice (gen:one-of '((var x) (var y))) (gen:map (gen:integer-in 0 4) cnum))
      (gen:frequency (list (cons 1 (gen:one-of '((var x) (var y))))
                           (cons 1 (gen:map (gen:integer-in 0 4) cnum))
                           (cons 3
                                 (gen:bind (gen:one-of '(+ - *))
                                           (lambda (op)
                                             (gen:map (gen:tuple (poly-term-gen (sub1 n))
                                                                 (poly-term-gen (sub1 n)))
                                                      (lambda (ab) `(fn ,op ,(car ab) ,(cadr ab)))))))
                           (cons 1
                                 (gen:map (gen:tuple (poly-term-gen (sub1 n)) (gen:integer-in 0 3))
                                          (lambda (te) `(fn ^ ,(car te) ,(cnum (cadr te))))))))))
(define pv '(x y))
(define zero-poly (polynate pv '(fn |0|)))
(define zero-mpoly (mpolynate pv '(fn |0|)))
;; complex.rkt nested polynomial ring laws (canonical form => structural equality)
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
                          (equal? (poly-add pv (polynate pv t1) (polynate pv t2))
                                  (poly-add pv (polynate pv t2) (polynate pv t1)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)] [t3 (poly-term-gen 2)])
                          (define p (polynate pv t1))
                          (define q (polynate pv t2))
                          (define r (polynate pv t3))
                          (equal? (poly-mul pv p (poly-add pv q r))
                                  (poly-add pv (poly-mul pv p q) (poly-mul pv p r)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)])
                          (equal? (poly-add pv (polynate pv t1) (poly-neg (polynate pv t1)))
                                  zero-poly)))
;; grobner.rkt monomial-list ring laws
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
                          (equal? (mpoly-add (mpolynate pv t1) (mpolynate pv t2))
                                  (mpoly-add (mpolynate pv t2) (mpolynate pv t1)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)] [t3 (poly-term-gen 2)])
                          (define p (mpolynate pv t1))
                          (define q (mpolynate pv t2))
                          (define r (mpolynate pv t3))
                          (equal? (mpoly-mul p (mpoly-add q r))
                                  (mpoly-add (mpoly-mul p q) (mpoly-mul p r)))))
(check-property poly
                (property ([t1 (poly-term-gen 2)])
                          (equal? (mpoly-add (mpolynate pv t1) (mpoly-neg (mpolynate pv t1)))
                                  zero-mpoly)))
;; real.rkt formal differentiation: linearity and the product rule
(check-property poly
                (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
                          (define p (polynate pv t1))
                          (define q (polynate pv t2))
                          (equal? (poly-diff pv (poly-add pv p q))
                                  (poly-add pv (poly-diff pv p) (poly-diff pv q)))))
(check-property
 poly
 (property ([t1 (poly-term-gen 2)] [t2 (poly-term-gen 2)])
           (define p (polynate pv t1))
           (define q (polynate pv t2))
           (equal? (poly-diff pv (poly-mul pv p q))
                   (poly-add pv (poly-mul pv (poly-diff pv p) q) (poly-mul pv p (poly-diff pv q))))))
;; cooper linearization of a ground term equals its native value
(define (cterm-gen n)
  (if (<= n 0)
      (gen:map (gen:integer-in 0 4) cnum)
      (gen:bind (gen:one-of '(+ - *))
                (lambda (op)
                  (gen:map (gen:tuple (cterm-gen (sub1 n)) (cterm-gen (sub1 n)))
                           (lambda (ab) `(fn ,op ,(car ab) ,(cadr ab))))))))
(define (cterm-value t)
  (match t
    [`(fn + ,a ,b) (+ (cterm-value a) (cterm-value b))]
    [`(fn - ,a ,b) (- (cterm-value a) (cterm-value b))]
    [`(fn * ,a ,b) (* (cterm-value a) (cterm-value b))]
    [`(fn ,k) (string->number (symbol->string k))]))
(check-property big (property ([t (cterm-gen 2)]) (= (dest-numeral (lint '() t)) (cterm-value t))))
;; QE procedures decide ground (in)equalities correctly
(define (rel-true? op av bv)
  (case op
    [(=) (= av bv)]
    [(<) (< av bv)]
    [(<=) (<= av bv)]
    [(>) (> av bv)]
    [(>=) (>= av bv)]))
(check-property mid
                (property ([op (gen:one-of '(= < <= > >=))] [a (cterm-gen 2)] [b (cterm-gen 2)])
                          (eq? (integer-qelim `(atom (rel ,op ,a ,b)))
                               (rel-true? op (cterm-value a) (cterm-value b)))))
(check-property mid
                (property ([op (gen:one-of '(= < <= > >=))] [a (cterm-gen 2)] [b (cterm-gen 2)])
                          (eq? (real-qelim `(atom (rel ,op ,a ,b)))
                               (rel-true? op (cterm-value a) (cterm-value b)))))
(check-property mid
                (property ([a (cterm-gen 2)] [b (cterm-gen 2)])
                          (eq? (complex-qelim `(atom (rel = ,a ,b)))
                               (= (cterm-value a) (cterm-value b)))))
;; DLO quantifier elimination removes all quantifiers
(define (qfree? fm)
  (match fm
    [`(,(or 'forall 'exists) ,_ ,_) #f]
    [`(not ,p) (qfree? p)]
    [`(,(or 'and 'or 'imp 'iff) ,p ,q) (and (qfree? p) (qfree? q))]
    [_ #t]))
(define (dlo-gen n)
  (define as
    '((atom (rel < (var x) (var y))) (atom (rel < (var y) (var x))) (atom (rel = (var x) (var y)))))
  (if (<= n 0)
      (gen:one-of as)
      (gen:frequency (list (cons 1 (gen:one-of as))
                           (cons 2 (gen:map (dlo-gen (sub1 n)) (lambda (p) `(not ,p))))
                           (cons 3 (binop-gen '(and or imp) dlo-gen n))
                           (cons 2 (quant-gen '(forall exists) '(x y z) dlo-gen n))))))
(check-property mid (property ([fm (dlo-gen 3)]) (qfree? (quelim-dlo fm))))
;; grobner-decide confirms congruence over a field: x=y => p(x)=p(y)
(define (x->y t)
  (match t
    [`(var x) '(var y)]
    [`(fn ,f . ,as) `(fn ,f ,@(map x->y as))]
    [_ t]))
(check-property low
                (property ([t (poly-term-gen 2)])
                          (grobner-decide `(imp (atom (rel = (var x) (var y)))
                                                (atom (rel = ,t ,(x->y t)))))))

;; ========================================================================= ;;
;; Chapters 6-7: LCF kernel and limitations
;; ========================================================================= ;;
;; kernel-derived rules produce conclusions of exactly the expected shape
(check-property big (property ([p gen:prop]) (equal? (concl (imp-refl p)) `(imp ,p ,p))))
(check-property big
                (property ([p gen:prop] [q gen:prop])
                          (equal? (concl (add-assum p (imp-refl q))) `(imp ,p (imp ,q ,q)))))
(check-property big
                (property ([s gen:term] [t gen:term])
                          (equal? (concl (eq-sym s t))
                                  `(imp (atom (rel = ,s ,t)) (atom (rel = ,t ,s))))))
(check-property big
                (property ([t gen:term])
                          (equal? (concl (ispec t '(forall x (atom (rel P (var x))))))
                                  `(imp (forall x (atom (rel P (var x)))) (atom (rel P ,t))))))
;; lcftaut succeeds exactly on tautologies, and the theorem it yields is the goal
(check-property low
                (property ([fm gen:prop-nc])
                          (define r
                            (with-handlers ([exn:fail? (lambda (e) 'fail)])
                              (lcftaut fm)))
                          (if (eq? r 'fail)
                              (not (tautology fm))
                              (and (tautology fm) (equal? (concl r) fm)))))
;; numerals / Goedel numbers / Robinson evaluation / delta-decider / Turing tape
(check-property big (property ([k (gen:integer-in 0 20)]) (= (dtermval (hash) (numeral k)) k)))
(check-property big
                (property ([n gen:nat] [m gen:nat]) (or (= n m) (not (= (gnumeral n) (gnumeral m))))))
(check-property mid
                (property ([t (nat-gen 2)])
                          (equal? (rhs (consequent (concl (robeval t)))) (numeral (nat-value t)))))
(check-property big
                (property ([op (gen:one-of '(= < <=))] [a (nat-gen 2)] [b (nat-gen 2)])
                          (eq? (dholds (hash) `(atom (rel ,op ,a ,b)))
                               (case op
                                 [(=) (= (nat-value a) (nat-value b))]
                                 [(<) (< (nat-value a) (nat-value b))]
                                 [(<=) (<= (nat-value a) (nat-value b))]))))
(check-property big
                (property ([sym (gen:one-of '(zero one blank))] [pos (gen:integer-in 0 4)])
                          (eq? (look (twrite sym (list 'tape pos (hash)))) sym)))
(check-property big
                (property ([sym (gen:one-of '(zero one))])
                          (eq? (look (move 'left (move 'right (twrite sym (list 'tape 0 (hash))))))
                               sym)))
