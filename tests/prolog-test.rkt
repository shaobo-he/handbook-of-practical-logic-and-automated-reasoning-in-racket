#lang racket/base

;; Unit tests for prolog.rkt: variable renaming of rules (renamerule), the
;; depth-bounded backchainer, Horn-clause conversion (hornify) and the toy
;; Prolog interpreter (simpleprolog / prolog). A "rule" is (asm . head).

(require rackunit)
(require "../fol/prolog.rkt")
(require (only-in "../core/lib.rkt" undefined))

;; ===== renamerule: rename fresh _N variables, advancing the counter =====
;; one distinct free variable -> counter advances by 1, x becomes _0
(let-values ([(rc k) (renamerule 0 (cons '() '(atom (rel p (var x)))))])
  (check-equal? rc (cons '() '(atom (rel p (var _0)))))
  (check-equal? k 1))
;; two distinct free vars (across head and body) -> counter advances by 2
(let-values ([(rc k) (renamerule 5 (cons (list '(atom (rel q (var y)))) '(atom (rel p (var x)))))])
  (check-equal? rc (cons (list '(atom (rel q (var _6)))) '(atom (rel p (var _5)))))
  (check-equal? k 7))
;; a ground rule has no free vars -> unchanged, counter unchanged
(let-values ([(rc k) (renamerule 3 (cons '() '(atom (rel p (fn a)))))])
  (check-equal? rc (cons '() '(atom (rel p (fn a)))))
  (check-equal? k 3))

;; ===== hornify: turn a clause into a (body . head) rule =====
;; one positive literal -> head; negatives -> body (de-negated)
(check-equal? (hornify '((not (atom (rel p))) (atom (rel q))))
              (cons (list '(atom (rel p))) '(atom (rel q))))
;; no positive literal -> head is #f (a goal/negative clause)
(check-equal? (hornify '((not (atom (rel p))))) (cons (list '(atom (rel p))) #f))
;; more than one positive literal is not Horn -> raise
(check-exn exn:fail? (λ () (hornify '((atom (rel p)) (atom (rel q))))))

;; ===== backchain: depth-bounded SLD resolution =====
(define rules
  (list (cons (list '(atom (rel q))) '(atom (rel p))) ; p :- q
        (cons '() '(atom (rel q))))) ; q.
;; with depth 0 and a non-empty goal stack, the search gives up
(check-exn exn:fail? (λ () (backchain rules 0 0 undefined (list '(atom (rel p))))))
;; an empty goal stack succeeds immediately, returning the env
(check-equal? (backchain rules 1 0 undefined '()) undefined)

;; ===== simpleprolog: backchain with unbounded depth =====
;; a two-step chain p :- q, q. proves p (returns a substitution)
(check-pred hash? (simpleprolog rules '(atom (rel p))))
;; an unprovable goal fails
(check-exn exn:fail? (λ () (simpleprolog rules '(atom (rel r)))))

;; ===== prolog: solve a goal and report the bindings of its free vars =====
(define facts (list (cons '() '(atom (rel point (fn a) (fn b))))))
(define sols (prolog facts '(atom (rel point (var u) (var w)))))
(check-equal? (length sols) 2) ; one binding per free variable
(check-true (and (member '(atom (rel = (var u) (fn a))) sols) #t))
(check-true (and (member '(atom (rel = (var w) (fn b))) sols) #t))
