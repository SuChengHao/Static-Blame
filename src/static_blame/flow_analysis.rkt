#lang racket
(require "./type_flow_generation.rkt"
         "./type_flow.rkt"
         "./refinement.rkt"
         )

(require "../grift/type-check.rkt"
         "../unique-identifiers.rkt"
         "../language/pprint.rkt")
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

(define (Cref->string ref)
  (match ref
    [(Idref uid)
     (format "identity ~a"
             (Uid-prefix uid))]
    [(Constref c)
     (format "const ~a" c)]
    [(Fdomref index)
     (format "the ~ath domain" index)]
    [(Franref)
     (format "the range")]
    [(Boxref)
     (format "the box content")]
    [(Castref)
     (format "the cast content")]
    [(Vecref)
     (format "the vector content")]
    [(Tupref index)
     (format "the ~ath tuple content" index)]
    ))
(define (Clabel->string clabel)
  (match-define (Clabel pp ref*) clabel)
  (define (rec pp ref*)
    (if (null? ref*)
        (format "the position in ~a" (if (srcloc? (Ppoint-src pp))
                                         (srcloc->string (Ppoint-src pp))
                                         (Ppoint-src pp)))
        (let ([former (Cref->string (car ref*))]
              [latter (rec pp (cdr ref*))])
          (format "~a of \n ~a" former latter)
          ))
    )
  (rec pp ref* )
  )

(define (Ltype->string ltype)
  (format "the type ~a in \n ~a" (type->string (Ltype-gtype ltype)) (Clabel->string (Ltype-clabel ltype))  )
  )
(define (Tyflow->string flow)
  (match-define (Tyflow from to bl) flow)
  (format "[from]\n~a\n[to]\n~a\n[with label]~a\n"
          (Ltype->string from)
          (Ltype->string to)
          (if (dummy? flow)
              "dummy"
              bl)
          ))


;; perr judge whether a potential error hit the error report
;; p: potential error, a type flow
;; m: error message of the program
(define (perr-match? p m)
  (equal? (Tyflow-blame-label p)
          m))







