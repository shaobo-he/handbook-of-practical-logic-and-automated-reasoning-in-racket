#lang racket/base

;; Property tests for the LCF kernel and the limitations chapter: derived rules
;; produce the expected theorems, lcftaut decides tautologies, and the
;; arithmetic/Goedel/Turing machinery matches native computation.

(require rackunit
         rackcheck
         "common.rkt")
(require (only-in "../../core/formulas.rkt" consequent))
(require (only-in "../../prop/prop.rkt" tautology))
(require (only-in "../../equality/equal.rkt" rhs))
(require (only-in "../../lcf/lcf.rkt" concl))
(require (only-in "../../lcf/lcfprop.rkt" lcftaut imp-refl add-assum))
(require (only-in "../../lcf/folderived.rkt" eq-sym ispec))
(require (only-in "../../lcf/limitations.rkt"
                  numeral
                  dtermval
                  dholds
                  robeval
                  gnumeral
                  look
                  twrite
                  move))

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
