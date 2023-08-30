#lang racket
(require "./stx-seq-loc.rkt")
(provide blame-msg->srcloc-pred)
(provide blame-msg->line/col)

(define (blame-msg->line/col str)
  (define line-col  (regexp-match* #px"\\d+\\:\\d+" str))
  (unless line-col
    (error 'blame-msg->srcloc-pred (format "The parameter ~a is not a valid blame message" str)))
  (match-define (list (app string->number line)
                      (app string->number col)) (regexp-match* #px"(\\d+)" (last line-col)))
  (values line col))


(define (blame-msg->srcloc-pred str)
  (define-values (line col) (blame-msg->line/col str))
  (define predt (syntax-predictor/srcloc-line-column line col))
  predt)
