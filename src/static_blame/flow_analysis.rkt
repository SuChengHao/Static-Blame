#lang racket
(require "./type_flow_generation.rkt"
         "./type_flow.rkt"
         )

(require "../grift/type-check.rkt")
(require "../grift/syntax-to-grift0.rkt")
(require (rename-in "../grift/read.rkt"
                    (read grift-compiler-read)))
(provide (all-defined-out))

(define (flow-analyse prog-path)
  (define solver (make-constraint-solver))
  (define np null)
  (define sp null)
  (define wdt null)
  (define-values (lst cpu-time real-time gc-time) 
    (time-apply (lambda ()
                  (parameterize ([current-solver solver])
                    (generate-type-flows (type-check (syntax->grift0 (grift-compiler-read prog-path)))))
                  (solve-a-solver solver)
                  (set!-values (np sp wdt) 
                               (statistic-solver solver))
                  ) '()))
  (solver-report solver cpu-time np sp wdt))

(define (hit? set-of-error message)
  (if (member message (map (lambda (flow) (Tyflow-blame-label flow)) (set->list set-of-error)))
    #t
    #f))



