#lang racket
(require racket/syntax-srcloc)
(provide (all-defined-out))

(define (make-seq)
  '())
(define (seq-add s e)
  (cons e s))
(define (seq->list s)
  (reverse s))
(define (list->seq s)
  (reverse s))
(define (seq-app s1 s2)
  (append s2 s1))
(define (seq-singleton e)
  (list e))
(define (seq->string s)
  (format "~a" (seq->list s)))

(define (port->seq port)
  (let ([s (read port)]
        )
    (unless (list? s)
      (error 'prot->seq (format "the content ~a is not a seq" s)))
    (list->seq s)))

(define (file->seq pos-path)
  (call-with-input-file pos-path (lambda (p) (port->seq p))))

(define (string->seq str)
  (define sp (open-input-string str))
  (port->seq sp))

(define seq? list?)

(define (immediate-father seq)
  (cond [(cons? seq) 
         (cdr seq)]
        [else seq]))

;; true if the first is the prefix of the second
(define (prefix?/seq base sub)
  (define (prefix-list A B)
    (cond [(null? A) #t]
          [(null? B) #f]
          [(equal? (car A) (car B))
           (prefix-list (cdr A) (cdr B))]
          [else #f]))
  (prefix-list (seq->list base) (seq->list sub)))
(define (seq-equal? A B)
  (equal? A B))

(define (sub-stx stx)
  (match (syntax-e stx)
        [(box sstx)
        (list sstx)]
        [(vector ele ...)
         ele]
        ['() #f]
        [(list ele ...)
         ele]
        [(cons sstx1 sstx2)
         (list sstx1 sstx2)]
        [_ #f]))

(define (syntax-search p stx)
  (define (then-subtrees lsub)
    ;; find the first un-false result in l
    (let-values ([(pos res-seq)
                  (for/fold ([pos -1]
                             [seq #f])
                            ([s lsub]
                             #:break (seq? seq))
                    (values (+ pos 1) (syntax-search p s)))])
      (and res-seq
          (seq-app (seq-singleton pos) res-seq))))
  (if (p stx)
      (make-seq)
      (and (sub-stx stx) (then-subtrees (sub-stx stx)))
      ))

(define (syntax-predictor/srcloc-line-column line column)
  (define/contract (predt stx)
    (-> syntax? (or/c #t #f))
    (let ([src (syntax-srcloc stx)])
      (and (equal? line (srcloc-line src))
           (equal? column (srcloc-column src)))))
  predt)

;;aux function, search a srcloc in a syntax tree
;;WARNING: POSSIBLE confusing part: only search for the same line and column-number
(define (syntax-search/srcloc-line-column line column source-syntax)
  (syntax-search (syntax-predictor/srcloc-line-column line column) source-syntax))

(define (syntax-at stx seq)
  (define (syntax-at-rev-list stx r-seq)
    (if (empty? r-seq)
      stx
      (let ([res-seq (cdr r-seq)]
            [index (car r-seq)]
            [lsub (sub-stx stx)])
        (unless (and lsub (<= index (length lsub)) )
          (error 'syntax-at (format "the syntax ~a does not have enough branch with respect to ~a"
                                    stx r-seq)))
        (syntax-at-rev-list (list-ref lsub index) res-seq)
        )))
  (define r-seq (seq->list seq))
  (syntax-at-rev-list stx r-seq))

(define (seq->srcloc stx seq)
  (define substx (syntax-at stx seq))
  (syntax-srcloc substx))
