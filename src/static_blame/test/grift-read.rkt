#lang racket/base
(require
 
 
 racket/exn
 racket/path)

(provide read)

#|
Function: get-name-of-file
This helper function called by read extracts a file name from a path.
|#
(define (get-name-of-file p)
  (let ([maybe-name (file-name-from-path p)])
    (if maybe-name
	(path->string maybe-name)
	(error 'grift "expected path to file: ~a" p))))

#|
Function: get-reader
This helper function called by read-syntax-from-file creates a syntax-reader
that annotates the syntax with source location and file name.
|#
;; string -> input-port -> syntax
(define ((get-reader name) p) 
  (read-syntax name p))

#|
Function: read-syntax-from-file
This helper function called by read collects all syntax in a file and returns
it as a list.
|#
;(: read-syntax-from-file (Path String . -> . (Listof (Syntaxof Any))))
(define (read-syntax-from-file path name)
  (unless (file-exists? path)
    (error 'grift/read
           "couldn't read grift source code\n\tno such file: ~a"
           path))
  (when (directory-exists? path)
    (error 'grift/read
           (string-append
            "couldn't read grift source code:\n"
            "\t found director instead of text file: ~a")
           path))
  (define (handle-unkown-read-exception e)
    (error 'grift/read
           "couldn't read grift source code:\n\tunkown exception follows\n~a"
           (exn->string e)))
  (with-handlers ([exn? handle-unkown-read-exception])
    (call-with-input-file path #:mode 'text
      (lambda (p) (read-syntax-from-port p name)))))

(define (read-syntax-from-port port name)
  (let ((read (get-reader name)))
    (let loop ([stx (read port)])
      (if (eof-object? stx)
          '()
          (cons stx (loop (read port)))))))


#|
Pass: read
Collects the syntax from a file and returns it a Syntax-Prog ast.
|#
;(: read (Path . -> . Syntax-Lang))
(define (read path)
  (parameterize
      ;; The following parameters change what the reader is willing
      ;; to accept as input.
      ([port-count-lines-enabled #t]
       [read-case-sensitive #t]
       [read-square-bracket-as-paren #t]
       [read-curly-brace-as-paren #t]
       [read-accept-box #f]
       [read-accept-compiled #f]
       [read-accept-bar-quote #f]
       [read-accept-graph #f]
       [read-decimal-as-inexact #t]
       [read-accept-dot #f]
       [read-accept-infix-dot #f]
       [read-accept-quasiquote #f]
       [read-accept-reader #f]
       [read-accept-lang #f])
    (let ([name (get-name-of-file path)])
       (read-syntax-from-file path name))))
