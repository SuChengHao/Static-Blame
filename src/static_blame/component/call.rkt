#lang racket
(require (for-syntax syntax/parse))
(provide call-with-output-file/multi
         syscall/timed
         simple-call)
;;(require macro-debugger/stepper)

(begin-for-syntax
  (define-splicing-syntax-class path-spec
    (pattern {~or x:id s:string}
     )))

(define-syntax (call-with-output-file/multi stx)
  (syntax-parse stx
    [(_ ([x:id p (~alt
                            (~optional (~seq #:mode mode-flag))
                            (~optional (~seq #:exists exists-flag))
                            (~optional (~seq #:permissions permissions))
                            )...]) body* ...)
     #'(call-with-output-file*  p
         (~? (~@ #:mode mode-flag))
         (~? (~@ #:exists exists-flag))
         (~? (~@ #:permissions permissions))
         (lambda (x) body* ...))
     ]
    [(_ ([x:id p (~alt
                            (~optional (~seq #:mode mode-flag))
                            (~optional (~seq #:exists exists-flag))
                            (~optional (~seq #:permissions permissions))
                            )...] . bind*) body* ...)
     #'(call-with-output-file*  p
         (~? (~@ #:mode mode-flag))
         (~? (~@ #:exists exists-flag))
         (~? (~@ #:permissions permissions))
         (lambda (x) (call-with-output-file/multi bind* body* ...))
         )]))

;; my syscall
;; iport/sp oport/sp eport/sp are stdin, stdout and stderr of
;; the new subprocess
;; the timeout is default 5(5 seconds)
;; all the ports must be file-stream-port
(define (syscall/timed oport/sp inport/sp eport/sp
                       program-path
                       #:time-out [time-out 5] . args)
  (let-values ([(subp f-out f-in f-err)
                (apply subprocess oport/sp inport/sp  eport/sp
                       program-path args)])
    (unless (sync/timeout time-out subp)
      (subprocess-kill subp #t))
    (when f-out
      (close-input-port f-out))
    (when f-err
      (close-input-port f-err))
    (when f-in
      (close-output-port f-in))
    ))



;; get the output of a program, without any further action
;; 
;; no input, get the std-out and std-err
(define (simple-call program-path . args)
  (let ([sout-file (make-temporary-file)]
        [serr-file (make-temporary-file)])

    (call-with-output-file/multi
     ([soutp sout-file #:mode 'text #:exists 'replace]
      [serrp serr-file #:mode 'text #:exists 'replace])
     (apply syscall/timed soutp #f serrp
         program-path args))
    ;; then, transfer the content of file into string and output.
    (values (file->string sout-file)
            (file->string serr-file))
    ))
