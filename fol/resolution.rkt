#lang racket/base

;; resolution --- binary resolution with factoring, subsumption and
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

;; ===== most general unifier of a whole list of literals =====
;; Unify the list pairwise (l0 with l1, then the result env carries into l1 with
;; l2, ...) and solve the accumulated env into an idempotent substitution that
;; makes all the literals equal at once.
(define (mgu l env)
  (match l
    [`(,a ,b . ,rest) (mgu (cons b rest) (unify-literals env (cons a b)))]
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
;; To resolve on literal p of cl1: collect the literals of cl2 that unify with
;; ~p (ps2) and the other literals of cl1 that unify with p (ps1). Factoring then
;; resolves any subset of {p}∪ps1 against any non-empty subset of ps2 at once,
;; unifying them all via one mgu — hence the allsubsets/allnonemptysubsets pairing.
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

;; ===== given-clause loop, basic "Argonne" form (no deletion) =====
;; The shared shape of all three loops below: pick the next clause cl from unused,
;; move it to used, resolve it against every used clause, and succeed if any
;; resolvent is the empty clause. resloop001 keeps every resolvent (just appends
;; news); resloop002 and presloop filter them through incorporate instead.
(define (resloop001 used unused)
  (match unused
    ['() (error 'resolution "No proof found")]
    [`(,cl . ,ros)
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

;; ===== one-way matching (for subsumption) =====
;; Unlike unify, term-match is asymmetric: only variables on the LEFT (the
;; pattern) may be bound, and a left variable already bound in env must match its
;; instance exactly. So it asks "does the pattern match this instance as-is?",
;; which is what subsumption needs (the subsuming clause must map INTO the other).
(define (term-match env eqs)
  (match eqs
    ['() env]
    [`(((fn ,f ,@fa) . (fn ,g ,@ga)) . ,oth)
     (if (and (equal? f g) (= (length fa) (length ga)))
         (term-match env (append (map cons fa ga) oth))
         (error 'term-match "term_match"))]
    [`(((var ,x) . ,t) . ,oth)
     (cond
       [(not (defined env x)) (term-match (update x t env) oth)]
       [(equal? (apply env x) t) (term-match env oth)]
       [else (error 'term-match "term_match")])]
    [_ (error 'term-match "term_match")]))

(define (match-literals env tmp)
  (match tmp
    [`((atom (rel ,p ,@a1)) . (atom (rel ,q ,@a2)))
     (term-match env (list (cons `(fn ,p ,@a1) `(fn ,q ,@a2))))]
    [`((not (atom (rel ,p ,@a1))) . (not (atom (rel ,q ,@a2))))
     (term-match env (list (cons `(fn ,p ,@a1) `(fn ,q ,@a2))))]
    [_ (error 'match-literals "match_literals")]))

;; cls1 subsumes cls2 iff some single substitution maps every literal of cls1 to a
;; literal of cls2 (so cls1 is at least as general and cls2 is redundant). subsume
;; threads one env across all of cls1's literals; tryfind backtracks over choices.
(define (subsumes-clause cls1 cls2)
  (define (subsume env cls)
    (match cls
      ['() env]
      [`(,l1 . ,clt) (tryfind (λ (l2) (subsume (match-literals env (cons l1 l2)) clt)) cls2)]))
  (with-handlers ([exn:fail? (λ (e) #f)])
    (subsume undefined cls1)
    #t))

;; ===== loop with tautology deletion and bi-subsumption =====
(define (replace cl lis)
  (match lis
    ['() (list cl)]
    [`(,c . ,cls)
     (if (subsumes-clause cl c)
         (cons cl cls)
         (cons c (replace cl cls)))]))

;; add a new clause cl to the unused list, but drop it if it is useless: a
;; tautology, or subsumed by the just-used clause gcl or by some existing unused
;; clause. Otherwise insert it, removing any unused clauses it subsumes (replace).
(define (incorporate gcl cl unused)
  (if (or (trivial cl) (ormap (λ (c) (subsumes-clause c cl)) (cons gcl unused)))
      unused
      (replace cl unused)))

(define (resloop002 used unused)
  (match unused
    ['() (error 'resolution "No proof found")]
    [`(,cl . ,ros)
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
;; restrict resolution so that at least one parent clause is all-positive; this
;; prunes the search space while staying refutation-complete.
(define (presolve-clauses cls1 cls2)
  (if (or (andmap positive cls1) (andmap positive cls2))
      (resolve-clauses cls1 cls2)
      '()))

(define (presloop used unused)
  (match unused
    ['() (error 'resolution "No proof found")]
    [`(,cl . ,ros)
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
;; Seed `used` with the clauses that have a positive literal and put the purely
;; negative clauses (the support set, typically derived from the negated goal)
;; into `unused`, so the search only ever resolves starting from the support.
(define (pure-resolution003 fm)
  (define-values (used unused)
    (partition (λ (cl) (ormap positive cl)) (simpcnf (specialize (pnf fm)))))
  (resloop002 used unused))

(define (resolution003 fm)
  (define fm1 (askolemize `(not ,(generalize fm))))
  (map (λ (d) (pure-resolution003 (list-conj d))) (simpdnf fm1)))

(define resolution resolution003)
