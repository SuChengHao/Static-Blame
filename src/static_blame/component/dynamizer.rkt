#lang racket
(require "call.rkt")
(require megaparsack megaparsack/text)
(require data/monad)
(require data/applicative)
(provide run-dynamizer
         (struct-out Dynamizer-Report)
         dynamizer-path
         (struct-out exn:dynamizer))

(struct Dynamizer-Report (config/total typenode config/requested)
  #:transparent)
(struct exn:dynamizer exn:fail ())
(define dynamizer/p
  (do (string/p "Number of all configurations: ")
      [x <- integer/p]
    (string/p "\nNumber of all type nodes: ")
    [y <- integer/p]
    (string/p "\nNumber of requested configurations: ")
    [z <- integer/p]
    (char/p #\newline)
    (pure (Dynamizer-Report x y z))))

;; test it is the dynamizer
(define (dynamizer-guard program-path)
  (unless (file-exists? program-path)
    (error 'dynamizer-path
           "~a is not an existing file"
           program-path))
  (let-values ([(stdout stderr)
                (simple-call program-path "--help")])
    (unless (string-prefix? stdout "Dynamizer")
      (error 'dynamizer-guard
             "~a is not path of a dynamizer executable"
             program-path))
    program-path))

(define dynamizer-path (make-parameter #f
                                       dynamizer-guard))
;;dynamizer interface, call a dynamizer.
;; the dynamizer will
;; 1. make a output and error message
;; 2. if success, make a directory with the same name to the input grift program file
;; 3. make sure you know the result(run it in command line first!) before run it
(define/contract (run-dynamizer source-filepath config-count bin-count)
  (-> path-string? exact-integer? exact-integer? Dynamizer-Report?)
  (unless (dynamizer-path)
    (error 'run-dynamizer "dynamizer file path is not instantiated!\n"))
  (let-values ([(stdout stderr)
                (simple-call (dynamizer-path)
                             "--fine"
                             "--configurations-count" (number->string config-count)
                             "--bins" (number->string bin-count)
                             source-filepath)])
    (when (non-empty-string? stderr)
      (raise (exn:dynamizer (format 
                             "Dynamizer Error with output:\n ~a\n" stderr)
                            (current-continuation-marks))))
    (with-handlers ([exn:fail:read:megaparsack? (lambda (exn) (error 'run-dynamizer "fault internal error! the result format cannot be parsed:\n ~a" stdout)) ])
     (parse-result! (parse-string dynamizer/p stdout)))
    ))
