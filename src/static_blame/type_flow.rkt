;; this file contains the core data structure of static blame: the type flow
;; conceptually, it consists of two parts: the type flow itself, and constraint
;; solvers

#lang racket
(require "./refinement.rkt"
         "../language/pprint.rkt"
         "../language/forms.rkt"
         racket/contract
         racket/contract/option)
(require "../logging.rkt")

(provide (all-defined-out))

;; Checks to make sure Mu types obey the productivity check
;; Return the a version of type where superflouos mu are droped
;; and unrolled Mus are rerolled.
;; Note that this definition is buggy
;(: validate-type : srcloc Grift-Type -> Grift-Type)
(define (validate-type t)
  (define who 'validate-type)
  (define eqs
    (make-hash '()))

  (define (vt pending)
    
    (define (rec t)
      (cond
        [(Mu? t)
         (match-define (Mu s0) t)
         (define rec-uvar (next-uid! 'rec-fvar))
         (define rec-fvar (FVar rec-uvar))
         (define t0 (grift-type-instantiate s0 rec-fvar))
         (define t1 ((vt (set-add pending rec-uvar)) t0))
         ;; If the inner type is a Mu then we merge the
         ;; Mu we are creating with the inner one.
         ;; This is because both Mu's variables point to
         ;; the same location in the type.
         (define t2
           (cond
             [(Mu? t1)
              (match-define (Mu s1) t1)
              (grift-type-instantiate s1 rec-fvar)]
             [else t1]))
         (define-values (s1 used?)
           (grift-type-abstract/used? rec-uvar t2))
         ;; if rec-uvar isn't abstracted then t1 doesn't contain
         ;; any occurences of it and we don't have to bind it.
         (define ret (if used? (Mu s1) t2))
         (hash-set! eqs (grift-type-instantiate s1 ret) ret)
         ret]
        [(FVar? t)
         (match-define (FVar u) t)
         (when (set-member? pending u)
           (error 'non-productive-variable
                  "recursive variable appears in non-productive position ~a"
                  ))
         t]
        [else
         ;; If the type constructor is for actual data then the mu is productive
         ;; and we can clear the pending recursive variables.
         (define vt/pending
           (if (structural-type? t) (vt (set)) rec))
         (define r (grift-type-map t vt/pending))
         (or (hash-ref eqs r #f) r)]))
    rec)
  (debug who type ((vt (set)) t)))

;; a flag, is a dummy flag, or just a string that stands for a blame message.
(define Dummy-Flag 'dummy)

(struct Ltype (clabel gtype))

(define (mk-ltype clabel gtype)
  (or 
   (Clabel? clabel)
   (error 'bad-clabel "call mk-ltype on an invalid label"))
  (Ltype (validate-type gtype)))

;; A type-flow is just a pair of two labeled type
(struct Tyflow (from to blame-label)
  #:transparent)



;; A labeled type, is just a pair of a gradual type and a Clabel
;; but, in our design, an expression only has one type, then the
;; gradual type becomes a redundancy.

(define (make-dummy-type-flow from to)
  (Tyflow from to Dummy-Flag))

(define (mk-dummy-type-flow from to blabel)
  (Tyflow from to blabel))




;; (define (make-type-flow from to src)
;;   (type-flow from to
;;              (format "type ~a flows into type ~b at source location: ~a/n"
;;                      (type->string (erase-type-label from))
;;                      (type->string (erase-type-label to))
;;                      (srcloc->string src))))

(define current-solver (make-parameter #f))

;; --A constraint-solver is a solver that can solve constraint --
;; Never mind, A constraint solver can add type flow, calculate closure, and
;; finally judge whether there exists potential error in the program.
(define (make-constraint-solver)
  (list);; for now, it is just a list of constraints, but laterly it will be improved to more efficient data structure.
  )

(define (add-type-flow-to-a-solver new-flow [solver (current-solver)])
  (cons new-flow solver))
(define (add-blabel-flow from to blabel [solver (current-solver)])
  (add-type-flow-to-a-solver (Tyflow from to blabel) solver ))
(define (add-dummy-flow from to [solver (current-solver)])
  (add-type-flow-to-a-solver (Tyflow from to Dummy-Flag) solver))


(define (solve-a-solver solver)
  (debug 'solve-a-solver solver))


