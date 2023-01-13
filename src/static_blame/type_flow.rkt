;; this file contains the core data structure of static blame: the type flow
;; conceptually, it consists of two parts: the type flow itself, and constraint
;; solvers

#lang racket
(require "./refinement.rkt"
         "../language/pprint.rkt")
(require "../logging.rkt")

(provide (all-defined-out))

;; A type-flow is just a pair of two labeled type
(struct type-flow (from to blame-label))

(define (make-type-flow from to src)
  (type-flow from to
             (format "type ~a flows into type ~b at source location: ~a/n"
                     (type->string (erase-type-label from))
                     (type->string (erase-type-label to))
                     (srcloc->string src))))

(define current-solver (make-parameter #f))

;; --A constraint-solver is a solver that can solve constraint --
;; Never mind, A constraint solver can add type flow, calculate closure, and
;; finally judge whether there exists potential error in the program.
(define (make-constraint-solver)
  (list);; for now, it is just a list of constraints, but laterly it will be improved to more efficient data structure.
  )

(define (add-type-flow-to-a-solver new-flow [solver (current-solver)])
  (cons new-flow solver))

(define (solve-a-solver solver)
  (debug 'solve-a-solver solver)
  )


