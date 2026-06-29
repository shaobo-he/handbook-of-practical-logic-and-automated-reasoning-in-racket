#lang racket/base

;; Property tests for the limitative-results chapter: the pairing and string
;; encodings are invertible, Goedel numbering of terms/formulas is injective, the
;; Delta-decider matches native arithmetic, Sigma/Pi/Delta classification holds
;; on canonical witnesses, and the Turing tape primitives behave functionally.

(require rackunit
         rackcheck
         (only-in racket/list range)
         "common.rkt")
(require (only-in "../../lcf/limitations.rkt"
                  pair
                  number
                  gterm
                  gform
                  dtermval
                  dholds
                  classify
                  look
                  twrite))

;; ===== pair: invertible (hence injective) =====
;; pair x y = (x+y)^2 + x + 1, so with s = x+y we have s^2 < code <= (s+1)^2,
;; giving s = floor(sqrt(code-1)) and x = code - s^2 - 1, y = s - x.
(define (unpair v)
  (define s (integer-sqrt (- v 1)))
  (define x (- v (* s s) 1))
  (values x (- s x)))
(check-property big
                (property ([a (gen:integer-in 0 60)] [b (gen:integer-in 0 60)])
                          (let-values ([(x y) (unpair (pair a b))])
                            (and (= x a) (= y b)))))

;; ===== number: invertible base-256 encoding (first char least significant) =====
(define (unnumber n)
  (let loop ([n n]
             [acc '()])
    (if (= n 0)
        (list->string (reverse acc))
        (loop (quotient n 256) (cons (integer->char (- (modulo n 256) 1)) acc)))))
(define letter-string-gen
  (gen:map (gen:list (gen:one-of (map integer->char (range 97 123))) #:max-length 6) list->string))
(check-property big (property ([s letter-string-gen]) (equal? (unnumber (number s)) s)))

;; ===== gterm / gform: injective (distinct structures -> distinct codes) =====
(check-property big
                (property ([t1 (nat-gen 2)] [t2 (nat-gen 2)])
                          (or (equal? t1 t2) (not (= (gterm t1) (gterm t2))))))

(define delta-atom-gen
  (gen:bind (gen:one-of '(= < <=))
            (λ (op)
              (gen:map (gen:tuple (nat-gen 1) (nat-gen 1))
                       (λ (st) `(atom (rel ,op ,(car st) ,(cadr st))))))))
(define (delta-form-gen n)
  (if (<= n 0)
      delta-atom-gen
      (gen:frequency (list (cons 2 delta-atom-gen)
                           (cons 1 (gen:map (delta-form-gen (sub1 n)) (λ (p) `(not ,p))))
                           (cons 2 (binop-gen '(and or imp iff) delta-form-gen n))))))
(check-property mid
                (property ([f1 (delta-form-gen 2)] [f2 (delta-form-gen 2)])
                          (or (equal? f1 f2) (not (= (gform f1) (gform f2))))))

;; ===== dtermval: matches native arithmetic on compound ground terms =====
(check-property big (property ([t (nat-gen 2)]) (= (dtermval (hash) t) (nat-value t))))

;; ===== dholds: boolean combinations of ground delta-atoms match native logic =====
(define (atom-true? op a b)
  (case op
    [(=) (= (nat-value a) (nat-value b))]
    [(<) (< (nat-value a) (nat-value b))]
    [(<=) (<= (nat-value a) (nat-value b))]))
(check-property big
                (property ([op1 (gen:one-of '(= < <=))] [a1 (nat-gen 1)]
                                                        [b1 (nat-gen 1)]
                                                        [op2 (gen:one-of '(= < <=))]
                                                        [a2 (nat-gen 1)]
                                                        [b2 (nat-gen 1)]
                                                        [conn (gen:one-of '(and or imp iff))])
                          (define va (atom-true? op1 a1 b1))
                          (define vb (atom-true? op2 a2 b2))
                          (eq? (dholds (hash)
                                       `(,conn (atom (rel ,op1 ,a1 ,b1)) (atom (rel ,op2 ,a2 ,b2))))
                               (case conn
                                 [(and) (and va vb)]
                                 [(or) (or va vb)]
                                 [(imp) (or (not va) vb)]
                                 [(iff) (eq? va vb)]))))

;; ===== classify: canonical Delta_0 / Sigma_1 / Pi_1 witnesses are recognised =====
(check-property big
                (property ([a delta-atom-gen])
                          (and (classify 'delta 0 a)
                               (classify 'sigma 1 `(exists x ,a))
                               (classify 'pi 1 `(forall x ,a)))))

;; ===== tape: a later write at a cell shadows the earlier one =====
(check-property big
                (property ([s1 (gen:one-of '(zero one blank))] [s2 (gen:one-of '(zero one blank))]
                                                               [pos (gen:integer-in 0 4)])
                          (eq? (look (twrite s2 (twrite s1 (list 'tape pos (hash))))) s2)))
