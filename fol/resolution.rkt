#lang racket/base

;; resolution.fs --- binary resolution with factoring, subsumption and
;; tautology deletion, positive (P1) resolution, and set-of-support.

(require racket/match)
(require (only-in racket/list partition append*))
(require (only-in "../core/lib.rkt"
                  allpairs
                  image
                  union
                  subtract
                  insert
                  fpf
                  allsubsets
                  allnonemptysubsets
                  mapfilter
                  tryfind
                  undefined
                  update
                  apply
                  defined))
(require (only-in "../core/formulas.rkt" list-conj list-disj))
(require (only-in "../prop/prop.rkt" negate positive trivial simpcnf simpdnf))
(require (only-in "fol.rkt" fv subst generalize))
(require (only-in "skolem.rkt" specialize pnf askolemize))
(require (only-in "unif.rkt" solve))
(require (only-in "tableaux.rkt" unify-literals))

(provide (all-defined-out))

(define resolution-verbose (make-parameter #f))

;; ===== most general unifier of a list of literals =====
(define (mgu l env)
  (match l
    [(list* a b rest) (mgu (cons b rest) (unify-literals env (cons a b)))]
    [_ (solve env)]))

(define (unifiable p q)
  (with-handlers ([exn:fail? (λ (e) #f)])
    (unify-literals undefined (cons p q))
    #t))

;; ===== rename a clause's variables with a prefix =====
(define (rename pfx
                cls)
  (define fvs (fv (list-disj cls)))
  (define vvs (map (λ (s) `(var ,(string->symbol (string-append pfx (symbol->string s))))) fvs))
  (map (λ (cl) (subst (fpf fvs vvs) cl)) cls))

;; ===== general resolution rule, with factoring (Robinson) =====
(define (resolvents cl1 cl2 p acc)
  (define ps2 (filter (λ (q) (unifiable (negate p) q)) cl2))
  (if (null? ps2)
      acc
      (let ()
        (define ps1 (filter (λ (q) (and (not (equal? q p)) (unifiable p q))) cl1))
        (define pairs
          (allpairs cons (map (λ (pl) (cons p pl)) (allsubsets ps1)) (allnonemptysubsets ps2)))
        (foldr (λ (pr sof)
                 (define s1 (car pr))
                 (define s2 (cdr pr))
                 (with-handlers ([exn:fail? (λ (e) sof)])
                   (cons (image (λ (lit) (subst (mgu (append s1 (map negate s2)) undefined) lit))
                                (union (subtract cl1 s1) (subtract cl2 s2)))
                         sof)))
               acc
               pairs))))

(define (resolve-clauses cls1 cls2)
  (define cls1*
    (rename "x"
            cls1))
  (define cls2*
    (rename "y"
            cls2))
  (foldr (λ (p acc) (resolvents cls1* cls2* p acc)) '() cls1*))

;; ===== basic "Argonne" loop (no deletion) =====
(define (resloop001 used unused)
  (match unused
    ['() (error 'resolution "No proof found")]
    [(cons cl ros)
     (when (resolution-verbose)
       (printf "~a used; ~a unused.\n" (length used) (length unused)))
     (define used* (insert cl used))
     (define news (append* (mapfilter (λ (c) (resolve-clauses cl c)) used*)))
     (if (member '() news)
         #t
         (resloop001 used* (append ros news)))]))

(define (pure-resolution001 fm)
  (resloop001 '() (simpcnf (specialize (pnf fm)))))

(define (resolution001 fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (pure-resolution001 (list-conj d))) (simpdnf fm1)))

;; ===== term/literal matching (for subsumption) =====
(define (term-match env eqs)
  (match eqs
    ['() env]
    [(cons (cons `(fn ,f ,@fa) `(fn ,g ,@ga)) oth)
     (if (and (equal? f g) (= (length fa) (length ga)))
         (term-match env (append (map cons fa ga) oth))
         (error 'term-match "term_match"))]
    [(cons (cons `(var ,x) t) oth)
     (cond
       [(not (defined env x)) (term-match (update x t env) oth)]
       [(equal? (apply env x) t) (term-match env oth)]
       [else (error 'term-match "term_match")])]
    [_ (error 'term-match "term_match")]))

(define (match-literals env tmp)
  (match tmp
    [(cons `(atom (rel ,p ,@a1)) `(atom (rel ,q ,@a2)))
     (term-match env (list (cons `(fn ,p ,@a1) `(fn ,q ,@a2))))]
    [(cons `(not (atom (rel ,p ,@a1))) `(not (atom (rel ,q ,@a2))))
     (term-match env (list (cons `(fn ,p ,@a1) `(fn ,q ,@a2))))]
    [_ (error 'match-literals "match_literals")]))

(define (subsumes-clause cls1 cls2)
  (define (subsume env cls)
    (match cls
      ['() env]
      [(cons l1 clt) (tryfind (λ (l2) (subsume (match-literals env (cons l1 l2)) clt)) cls2)]))
  (with-handlers ([exn:fail? (λ (e) #f)])
    (subsume undefined cls1)
    #t))

;; ===== loop with tautology deletion and bi-subsumption =====
(define (replace cl lis)
  (match lis
    ['() (list cl)]
    [(cons c cls)
     (if (subsumes-clause cl c)
         (cons cl cls)
         (cons c (replace cl cls)))]))

(define (incorporate gcl cl unused)
  (if (or (trivial cl) (ormap (λ (c) (subsumes-clause c cl)) (cons gcl unused)))
      unused
      (replace cl unused)))

(define (resloop002 used unused)
  (match unused
    ['() (error 'resolution "No proof found")]
    [(cons cl ros)
     (when (resolution-verbose)
       (printf "~a used; ~a unused.\n" (length used) (length unused)))
     (define used* (insert cl used))
     (define news (append* (mapfilter (λ (c) (resolve-clauses cl c)) used*)))
     (if (member '() news)
         #t
         (resloop002 used* (foldr (λ (n acc) (incorporate cl n acc)) ros news)))]))

(define (pure-resolution002 fm)
  (resloop002 '() (simpcnf (specialize (pnf fm)))))

(define (resolution002 fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (pure-resolution002 (list-conj d))) (simpdnf fm1)))

;; ===== positive (P1) resolution =====
(define (presolve-clauses cls1 cls2)
  (if (or (andmap positive cls1) (andmap positive cls2))
      (resolve-clauses cls1 cls2)
      '()))

(define (presloop used unused)
  (match unused
    ['() (error 'resolution "No proof found")]
    [(cons cl ros)
     (when (resolution-verbose)
       (printf "~a used; ~a unused.\n" (length used) (length unused)))
     (define used* (insert cl used))
     (define news (append* (mapfilter (λ (c) (presolve-clauses cl c)) used*)))
     (if (member '() news)
         #t
         (presloop used* (foldr (λ (n acc) (incorporate cl n acc)) ros news)))]))

(define (pure-presolution fm)
  (presloop '() (simpcnf (specialize (pnf fm)))))

(define (presolution fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (pure-presolution (list-conj d))) (simpdnf fm1)))

;; ===== set-of-support restriction =====
(define (pure-resolution003 fm)
  (define-values (used unused)
    (partition (λ (cl) (ormap positive cl)) (simpcnf (specialize (pnf fm)))))
  (resloop002 used unused))

(define (resolution003 fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (pure-resolution003 (list-conj d))) (simpdnf fm1)))

(define resolution resolution003)
