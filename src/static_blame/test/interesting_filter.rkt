#lang racket
(require "../../grift/syntax-to-grift0.rkt"
         "../../grift/type-check.rkt"
         (rename-in "../../grift/read.rkt"
                    (read grift-compiler-read))
         (rename-in "../../compile.rkt"
                    (compile grift-compiler-compile)))

(provide (all-defined-out))

(define (from-mutant-to-names dir)
  (define dir-name
    (let-values ([(base name c) (split-path dir)])
      (path->string name)))
  (define static-file-path-name (build-path dir (string-append dir-name "-static.grift")))
  (define dynamic-file-path-name (build-path dir (string-append dir-name "-dynamic.grift")))
  (values static-file-path-name dynamic-file-path-name dir-name))

;; note that, the dir is not a file path, but a directory path
;; the directory should contain two file, one end with static and the other ends with dynamic. Both of them needs have the same name of the dir.
;; on the other hand, the input is a text file store inputs that will input to the compiled file
(define (is-interesting? dir input)
  ;; (display (format "test mutatnt in ~a \n" dir))
  (define temp-path (find-system-path 'temp-dir))
  ;; (define code-name (path-replace-extension (file-name-from-path filename) #""))
  ;; (define work-directory (build-path temp-path code-name))
  ;;(unless (directory-exists? work-directory)
  ;;  (make-directory work-directory))
  ;; first, list files
  
  (define-values (s d m) (from-mutant-to-names dir))
  ;;(define s-s? (statically-accepted? s))
  (define s-d? (statically-accepted? d))
  ;;(when s-s? (display (format "static version of ~a is statically accepted\n" m)))
  ;;(unless s-d? (display (format "dynamic version of ~a is statically rejected\n" m)))

  (when ;;(and (not s-s?) s-d?)
      s-d?
      (display (format "generating runtime information for ~a \n" m))
      (define exe-name (build-path temp-path m))
      (grift-compiler-compile d
                              #:output exe-name)
    (define dynamic-out-put-file (build-path dir "dynamic-output.txt"))
    (run-compiled-program exe-name input dynamic-out-put-file)
       ;;(with-output-to-file dynamic-out-put-file (lambda ()
       ;;                (with-input-from-file input
       ;;                  (lambda () (system (path->string exe-name) #:set-pwd? #t)
       ;;                             ))) #:exists 'replace)
      ;;(display (format "~a\n" output)) 
      ))


;; 'real' interesting filter, with a source file and a input, output into the temporary directory,
;; then return error-message if
;; 1. the dynamically file is statically accepted
;; 2. running the dynamic situation will trigger blame
;; return #f else
(define (interesting/p source-file input )
  (define temp-path (find-system-path 'temp-dir))
  ;;(define-values (s d m) (from-mutant-to-names dir))
  ;;(define s-d? (statically-accepted? d))
  ;;(define s-s? (statically-accepted? s))
  (define s-d? (statically-accepted? source-file))
  (define m "grift-interesting-running")
  (define exe-name (build-path temp-path m))
  (define (grift-prog-trigger? exe-name)
    (grift-compiler-compile source-file #:output exe-name)
    (define dynamic-out-put-file (build-path temp-path "grift-interesting-dynamic-output.txt"))
    (run-compiled-program exe-name input dynamic-out-put-file)
    (define s (port->string (open-input-file dynamic-out-put-file) #:close? #t))
    (define mc (regexp-match "Implicit cast.*" s))
    (if mc (first mc) #f))
  (and s-d? (grift-prog-trigger? exe-name)))

(define (statically-and-dynamically-accepted? dir)
  (define-values (s d m) (from-mutant-to-names dir))
  (and (statically-accepted? s) (statically-accepted? d)))


;;input: path is a path to a grift file
;;output: #t if it pass the static type-check
;; #f otherwise
(define (statically-accepted? path)
  (if 
   (with-handlers ([exn:fail? (lambda (exn) #f)])
     (type-check (syntax->grift0 (grift-compiler-read path))))
   #t
   #f))

(define (run-compiled-program prog-path input-path output-path)
  (call-with-output-file output-path (lambda (out-port)
                       (call-with-input-file input-path
                         (lambda (in-port)
                           (let-values ([(subp fa fb fc)
                                  (subprocess out-port in-port out-port prog-path)])
                             ;; the process will close when the process returns.
                             (sync/timeout 5  subp)
                             (when (equal? (subprocess-status subp) 'running)
                               (display (format "~a is still running after 5 seconds!\n" prog-path))
                               (subprocess-kill subp #t))
                             )))) #:exists 'replace))


(define (run-dynamizer source-file output-path config-count bin-count)
  (call-with-output-file output-path #:exists 'replace
    (lambda (temp-out-port)
      (let-values ([(subp f-out f-in f-err)
                    (subprocess temp-out-port #f temp-out-port "/home/sch/.local/bin/dynamizer" "--fine" "--configurations-count" (number->string config-count) "--bins" (number->string bin-count) source-file)])
        (sync/timeout 5 subp)
        (close-output-port f-in)))))
(require megaparsack megaparsack/text)
(require data/monad)
(require data/applicative)
(define dynamizer/p
  (do (string/p "Number of all configurations: ")
      [x <- integer/p]
    (string/p "\nNumber of all type nodes: ")
    [y <- integer/p]
    (string/p "\nNumber of requested configurations: ")
    [z <- integer/p]
    (char/p #\newline)
    (pure (list x y z))))
(define (analyse-dynamizer-output dyn-output)
  (define str (port->string (open-input-file dyn-output) #:close? #t))
  (with-handlers ([exn:fail:read:megaparsack? (lambda (exn) (error 'dyn/format (string-append (path->string dyn-output) "\nfails") )) ])
    (match (parse-result! (parse-string dynamizer/p str))
      [(list n-config n-type-node n-req-config) (values n-config n-type-node n-req-config)])))


;; (for ([f (directory-list "/home/sch/grift-exp/blackscholes/position-swap/" #:build? #t)]
;;                               #:when (directory-exists? f))
;;                           (is-interesting? f "/home/sch/code/benchmarks/inputs/blackscholes/in_16.txt"))

;;exp-dir: one directory for each test-case
;;             where one directory for each mutant
;;                   where one file static and one file dynamic
;;bench-dir: src: directory of source files
;;           inputs: one directory for each source file
;;                   which include exactly one input file.
(define benchmark-directory "/home/sch/code/Grift/src/static_blame/test/benchmark")
(define exp-dir "/home/sch/grift-exp/")
;; (main-work exp-dir benchmark-directory)
(define (main-work exp-dir bench-dir)
  ;; first, get a list of test-case
  (define bench-src-dir (build-path bench-dir "src"))
  (define bench-inputs-dir (build-path bench-dir "inputs"))
  (define list-of-cases
    (for/list ([f (directory-list bench-src-dir)]
               #:when (string-suffix? (path->string f) ".grift"))
      (string-trim (path->string f) ".grift" #:left? #f)))

  ;; then, get input file for each file in the list
  (define (get-input-file case-name)
    (for/first ([f (directory-list (build-path bench-inputs-dir case-name) #:build? #t)])
      f))
  (define input-files-list (map get-input-file list-of-cases))
  ;; then, for each mutant in the exp dir, filter it and collect its result into
  ;; a file output.
  (map (lambda (case-name input-file)
         (let ([exp-case-dir (build-path exp-dir case-name)])
           (display (format "test for case: ~a \n" case-name))
           (for ([f (directory-list exp-case-dir #:build? #t)]
                 #:when (directory-exists? f))
             (define-values (b mutation b2) (split-path f))
             (display (format "test for mutation: ~a \n" f))
             (for ([mutant (directory-list f #:build? #t)]
                   #:when (directory-exists? mutant))
               (is-interesting? mutant input-file))
             )
           )
         )
       list-of-cases input-files-list)
  
  )
(require file/glob)
(define (analyse-error-pattern exp-dir)
  (define glob-pattern (build-path exp-dir  "*/*/*/*-output.txt"))
  (for ([f (in-glob glob-pattern)])
    (let ([s (port->string (open-input-file f) #:close? #t)])
      (define start-with-Impilicit-Cast? (string-prefix? s "Implicit cast"))
      (define has-time-info? (string-contains? s "time (sec):"))
      
      (when (and (not start-with-Impilicit-Cast? ) (not has-time-info?))
        (display (format "\n[file content]~a:\n~a\n" f s)
        )))))

;;(for ([f (directory-list "/home/sch/grift-exp/blackscholes/position-swap" #:build? #t)]
;;                               #:when (directory-exists? f))
;;                           (is-interesting? f "/home/sch/code/benchmarks/inputs/blackscholes/in_16.txt"))

(define current-case (make-parameter #f))
(define current-mutator (make-parameter #f))

(define true/p
    (do (string/p "true")
        (pure "true")))
(define false/p
  (do (string/p "false")
      (pure "false")))
(define boolean/p
  (or/p true/p
        false/p))
(define sharp-t/p
  (do (string/p "#t")
      (pure "true")))
(define sharp-f/p
  (do (string/p "#f")
      (pure "false")))
(define sharp-value/p
  (or/p (try/p sharp-t/p)
        sharp-f/p))

;; (printf "~a,~a,~a,~a,~a,~a,~a,~a,~a\n" loc blame-error? msec ncons normal-hit? strict-hit? nnor nstr ndyn)
(define ana-res-sucess/p
  (do
      true/p
      (char/p #\,)
    [loc <- integer/p]
      (char/p #\,)
    [blame-error? <- sharp-value/p]
    (char/p #\,)
    [msec <- integer/p]
    (char/p #\,)
    [ncons <- integer/p]
    (char/p #\,)
    [normal-hit? <- sharp-value/p]
    (char/p #\,)
    [strict-hit? <- sharp-value/p]
    (char/p #\,)
    [nnor <- integer/p]
    (char/p #\,)
    [nstr <- integer/p]
    (char/p #\,)
    [ndyn <- integer/p]
    (pure (format "true,~a,~a,~a,~a,~a,~a,~a,~a,~a"
                  loc blame-error? msec ncons normal-hit? strict-hit? nnor nstr ndyn))
    ))
(define ana-res-fail/p
  (do false/p
      (char/p #\,)
      (string/p "0,0,0,0,0,0,0,0,0")
      (pure "false,0,0,0,0,0,0,0,0,0")))
(define ana-res/p
  (or/p ana-res-sucess/p
        ana-res-fail/p))
(define number-suffix/p
  (do (char/p #\.)
      (sent <- integer/p)
    (pure (string-append "." (number->string sent)))))
(define full-number-suffix/p
  (do [pre <- integer/p]
      [suf <- number-suffix/p]
    (pure (string-append (number->string pre) suf))))
(define half-number/p
  (do [pre <- integer/p]
      (pure (number->string pre))))
(define real/p
  (or/p
   (try/p full-number-suffix/p)
   half-number/p
   ))
(define dynamized-line/p
  (do (string/p "config: ")
      [percentage <- real/p]
    (char/p #\,)
    [res <- ana-res/p]
    (char/p #\newline)
    (pure (string-append percentage "," res "\n"))))
;; 
(define final-report/p
  (do (string/p "Number of annotations: ")
      [nann <- integer/p]
    (char/p #\newline)
    (string/p "Static config: ")
    [static-line <- ana-res/p]
    (char/p #\newline)
    (string/p "Dynamic config: ")
    [dynamic-line <- ana-res/p]
    (char/p #\newline)
    [dynamized-lines <- (many/p dynamized-line/p)]
    (pure
     (let* ([str-nann (number->string nann)]
            [add-prefix (lambda (x) (string-append
                                     (current-case) "," (current-mutator) "," str-nann "," x))])
       (string-append
        (add-prefix (string-append "999," static-line "\n"))
        (add-prefix (string-append "-1," dynamic-line "\n"))
        (foldr (lambda (v l) (string-append (add-prefix (string-append v l))))  "" dynamized-lines)    
        )))
    ))
(define (analyse-final-report final-report cas mutator)
  (define str (port->string (open-input-file final-report) #:close? #t))
  (with-handlers ([exn:fail:read:megaparsack? (lambda (exn) #f)])
    (parameterize ([current-case cas]
                   [current-mutator mutator])
      (parse-result! (parse-string final-report/p str)))))
