#lang racket
(require "../type_flow_generation.rkt"
         "../type_flow.rkt"
         "../bug-detector.rkt"
         "../../grift/syntax-to-grift0.rkt"
         "./fake-insert-casts.rkt"
         "../../grift/type-check.rkt"
         "../../language/forms.rkt"
         "./interesting_filter.rkt"
         "../flow_analysis.rkt"
         "./mutate.rkt"
         "../../logging.rkt"
         "../component/stx-seq-loc.rkt"
         "../component/blame-label.rkt"
         "../component/exp-file-manage.rkt"
         (except-in "../component/dynamizer.rkt"
                    run-dynamizer)
         (rename-in "../component/dynamizer.rkt"
                    (run-dynamizer run-dynamizer/v-clean))
         
         )
(require (rename-in "../../grift/read.rkt"
                    (read grift-read))
         (rename-in "../../compile.rkt"
                    (compile grift-compiler-compile)))
(require racket/date)
(require racket/logging)

(provide temp-test/v2)

(define (cast-stored->message c)
                    (match-define (cons _ e)  c)
                    (match e
                      [ (Cast _ (Twosome _ _ message)) message]
                      [(Dyn-GRef-Ref _ message) message]
                      [(Dyn-GRef-Set! _ _ _ message) message]
                      [(Dyn-GVector-Ref _ _ m) m]
                      [(Dyn-GVector-Set! _ _ _ _ m) m]
                      [(Dyn-GVector-Len _ (Quote m)) m]
                      [(Dyn-Tuple-Proj _ _ (Quote m)) m]
                      [(Dyn-Fn-App _ _ _ m) m]))
(define (prg->generate-messages checked-prg)
                    (define solver (make-constraint-solver))
                    (parameterize ([current-solver solver])
                      (generate-type-flows checked-prg))
  (map Tyflow-blame-label (filter (lambda (x) (not (dummy? x))) (export-type-flow solver))))
(define (prg->stored-messages checked-prg)
  (insert-casts checked-prg)
  (map cast-stored->message (unbox casts-inserted)))

(define (is-generation-ok? checked-prg)
  (let ([stored-messages (prg->stored-messages checked-prg)]
        [generate-messages (prg->generate-messages checked-prg)])
    (= (length (filter (lambda (s) (not (member s generate-messages)))
                          stored-messages) ) 0)))
(require file/glob)
;; (find-all-unmatched-mutant  "/home/sch/grift-exp/")
(define (find-all-unmatched-mutant exp-dir)
  (define glob-pattern (build-path exp-dir  "*/*/*/*-dynamic.grift"))
  (for ([f (in-glob glob-pattern)]
        #:when (statically-accepted? f))
    (define checked-prg (type-check (syntax->grift0 (grift-read f))))
    (unless (is-generation-ok? checked-prg)
      (display (format "The file ~a is not ok\n" f)))))

(define (find-all-unhit-mutant exp-dir)
  (define glob-pattern (build-path exp-dir  "*/*/*/*-dynamic.grift"))
  (define-values (normal-hit sum) 
  (for/fold
      ([normal-hit 0]
       [sum        0])
      ([f (in-glob glob-pattern)]
        #:when (statically-accepted? f))
    (define-values (n-c s-c) (whether-hit f))
    (values (+ normal-hit n-c ) (+ sum s-c))))
  (display (format" ~a/~a hits " normal-hit sum)))

(define (extract-error-message s)
  (define mc (regexp-match "Implicit cast.*" s))
  (if mc
      (first mc)
      #f))

;; basic assumption:
;; the output is recorded in a file name dynamic-output.rkt
(define (whether-hit prog-file)
  (define-values (base prog-name must-be-dir?) (split-path prog-file))
  (define output-filepath (build-path base "dynamic-output.txt"))
  (define sum 0)
  (define normal-hit-counter 0)
  (if (file-exists? output-filepath)
      (begin 
        (let ([report (flow-analyse prog-file)]
              [error-msg (extract-error-message (port->string #:close? #t (open-input-file output-filepath)))])
          (when error-msg
            (set! sum 1)
            (let ([normal-hit? (hit? (SolverReport-normal report) error-msg)]
                  [strict-hit? (hit? (SolverReport-strict report) error-msg)]
                  [report-path (build-path base "dynamic-report.txt")])
              (unless normal-hit?
                (display (format  "Normal Potential Error is not hit for ~a\n" prog-file)))
              (unless strict-hit?
                (display (format  "Strict Potential Error is not hit for ~a\n" prog-file)))
              (call-with-output-file report-path #:exists 'replace
                (lambda (p)
                  (fprintf p "~a" (make-report-statistic report))
                  (fprintf p "Hit as Normal Potential Error?:~a\nHit as Strict Potential Error?:~a\n" normal-hit? strict-hit?)))
              (when normal-hit? (set! normal-hit-counter 1))))
          ))
      (begin 
        (display (format "the output file for ~a is missing\n" prog-file))))
  (values normal-hit-counter sum))
(define (count-of-lines ifile)
  (call-with-input-file ifile (lambda (p)
                                (for/sum ([_ (in-lines p)]) 1))))
(define (dynamized-file->config-percentage ifile)
  (call-with-input-file ifile (lambda (p)
                                (for/first ([s (in-lines p)])
                                  (string->number (string-trim (string-trim s "%") ";; "))))))

(define (first-pass-on-file f)
  (define-values (base prog-name must-be-dir?) (split-path f))
  (define output-filepath (build-path base "dynamic-output.txt"))
  (if (file-exists? output-filepath)
      (begin 
        (let ([report (flow-analyse f)]
              [error-msg (extract-error-message (port->string #:close? #t (open-input-file output-filepath)))]
              [normal-hit? #f]
              [strict-hit? #f]
              [loc (count-of-lines f)]
              [blame-error? #f])
          (define-values (ncons msec nnor nstr ndyn) (report-props report))
          (when error-msg
            (set!-values (normal-hit? strict-hit? blame-error?) (values (hit? (SolverReport-normal report) error-msg)
                                                                        (hit? (SolverReport-strict report) error-msg)
                                                                        #t)))
          (display (format "~a,~a,~a,~a,~a,~a,~a,~a,~a,~a\n" f loc blame-error? msec ncons normal-hit? strict-hit? nnor nstr ndyn))
          ))
      (begin 
        (display (error 'exp-error (format "the output file for ~a is missing\n" f)))))
  )

;; if the program is accepted by the static system and we run it with an output, we
;; analyse it by the flow analyse.
(define (analyse-by-output-file prog-source-file output-filepath-of-prog)
  (let ([report (flow-analyse prog-source-file)]
        [error-msg (extract-error-message (port->string #:close? #t (open-input-file output-filepath-of-prog)))]
        [normal-hit? #f]
        [strict-hit? #f]
        [loc (count-of-lines prog-source-file)]
        [blame-error? #f])
    (define-values (ncons msec nnor nstr ndyn) (report-props report))
    (when error-msg
      (set!-values (normal-hit? strict-hit? blame-error?) (values (hit? (SolverReport-normal report) error-msg)
                                                                  (hit? (SolverReport-strict report) error-msg)
                                                                  #t)))
    (values loc blame-error? msec ncons normal-hit? strict-hit? nnor nstr ndyn)))
(define (path->name/m p)
  (let-values ([(base name must-be-dir?) (split-path p)])
    name))
;; a mutant path has a static and a dynamic source file
;; this function does the following:
;; 1. run dynamizer on static file, record its annotation number
;; 2. run a source file, get whether it is statically accepted, the percentage of annotations
;;    and the result of run if it is statically accepted
;; 3. do a flow analyse and record whether it is hit.
;; the return value is a string record every thing
;; mutant report:
;; Number of annotations: n \n
;; Static config: statically accept? analyse-res. . . \n
;; Dynamic config: statically accepted? analyse-res . . . \n
;; configuration: percentage? statically accepted? analyse-res ... \n
;; ...
;;(final-analyse-mutant "/home/sch/grift-exp/blackscholes/arithmetic/mutant0/" "/home/sch/code/Grift/src/static_blame/test/benchmark/inputs/blackscholes/in_16.txt")
(define (final-analyse-mutant mutant-path input-file)
  (define temp-path (find-system-path 'temp-dir))
  (define dynamizer-res-output-file (build-path temp-path "dynamizer-output.txt"))
  (define (boolean->str b)
    (if b "true"
        "false"))

  (define-values (s d m) (from-mutant-to-names mutant-path))
  (define (print-source-analyse-res acc? ts)
    (if acc?
        (begin
          (let ([exe-name (build-path temp-path m)]
                [version-output-filepath (build-path temp-path "version-output.txt")]
                )
            (grift-compiler-compile ts
                                    #:output exe-name)
            (run-compiled-program exe-name input-file version-output-filepath)
            (let-values ([(loc blame-error? msec ncons normal-hit? strict-hit? nnor nstr ndyn)
                          (analyse-by-output-file ts version-output-filepath)])
              (printf "~a,~a,~a,~a,~a,~a,~a,~a,~a\n" loc blame-error? msec ncons normal-hit? strict-hit? nnor nstr ndyn)
              )))
        (printf "0,0,0,0,0,0,0,0,0\n")))
  
  (define s-s? (statically-accepted? s))
  (define s-d? (statically-accepted? d))
  ;; run dynamizer on the static source-file
  (run-dynamizer s dynamizer-res-output-file 1 10)
  (define-values (n-config n-type-node n-req-config) (analyse-dynamizer-output dynamizer-res-output-file) )
  (printf "Number of annotations: ~a\n" n-type-node)
  (printf "Static config: ~a," (boolean->str s-s?))
  (print-source-analyse-res s-s? s)
  
  (printf "Dynamic config: ~a," (boolean->str s-d?))
  (print-source-analyse-res s-d? d)

  (define dynamizer-path (path-replace-extension s ""))
  (unless (directory-exists? dynamizer-path)
    (error 'final-analyse-mutant (format  "dynamizer with error in ~a" mutant-path )))
  (for ([dyn (in-directory dynamizer-path)])
    (printf "config: ~a," (dynamized-file->config-percentage dyn))
    (define ac? (statically-accepted? dyn))
    (printf "~a," (boolean->str ac?))
    (print-source-analyse-res ac? dyn)))

(define (date-format/my idate)
  (match-define (date s m h d mon y _ _ _ _) idate)
  (format "~a/~a/~a ~a:~a:~a" y mon d h m s))
(define exp-dir "/home/sch/grift-exp/")
(define benchmark-directory "/home/sch/code/Grift/src/static_blame/test/benchmark")
(define interesting-mutation-directory "/home/sch/grift-exp-interesting-mutants")
;; (final-analyse-exp exp-dir benchmark-directory )
(define (final-analyse-exp exp-dir bench-dir)
    ;; first, get a list of test-case
  (define bench-src-dir (build-path bench-dir "src"))
  (define bench-inputs-dir (build-path bench-dir "inputs"))
  (define list-of-cases
    (for/list ([f (directory-list bench-src-dir)]
               #:when (string-suffix? (path->string f) ".grift"))
      (string-trim (path->string f) ".grift" #:left? #f)))
  (define (get-input-file case-name)
    (for/first ([f (directory-list (build-path bench-inputs-dir case-name) #:build? #t)])
      f))
  (define (case->mutator-list cas)
    (map path->name/m (filter directory-exists? (directory-list (build-path exp-dir cas) #:build? #t))))
  (define (mutator->mutation-list cas mut)
    (map path->name/m (filter directory-exists? (directory-list (build-path exp-dir cas mut) #:build? #t))))
  (for ([cas list-of-cases])
    
    (printf "[current: ~a]in case :~a\n" (date-format/my (current-date)) cas)
    (let ([mut-list (case->mutator-list cas)]
          [input-file (get-input-file cas)])
      (for ([mut mut-list])
        (printf "[current: ~a]in mutator :~a\n" (date-format/my (current-date)) mut)
        (let ([mutation-list (mutator->mutation-list cas mut)])
          (for ([mutation mutation-list])
            (define mutation-path (build-path exp-dir cas mut mutation))
            (with-handlers ([exn:fail? (lambda (exn)
                                         (printf "error on file: ~a with message: ~a" (build-path exp-dir cas mut mutation) (exn-message exn))
                                             )])
              (with-output-to-file #:exists 'replace (build-path mutation-path  "final report.txt")
                (lambda ()
                  
                  (final-analyse-mutant mutation-path input-file)
                  )))))))))

;; Then final analyse process
;;(final-analyse-exp exp-dir benchmark-directory )



(define (first-pass-on-mutants exp-dir)
  (define glob-pattern (build-path exp-dir  "*/*/*/*-dynamic.grift"))

  (display "file name,loc,blame error?,analyse time,constraints,hit as normal,hit as strict,Normal,Strict,Wrong dynamic\n")
  (for
      ([f (in-glob glob-pattern)]
       #:when (statically-accepted? f))
    (first-pass-on-file f)
    ;; (define-values (n-c s-c) (whether-hit f))
    ;; (values (+ normal-hit n-c ) (+ sum s-c))))
    ))

;; (with-output-to-file #:exists 'replace (build-path exp-dir  "first on mutants.csv")
;;     (lambda ()
;;       (first-pass-on-mutants exp-dir)))



(define (copy-interesting-mutants source-dir dest-dir bench-dir)
  (define bench-inputs-dir (build-path bench-dir "inputs"))
  (define (get-input-file case-name)
    (for/first ([f (directory-list (build-path bench-inputs-dir case-name) #:build? #t)])
      f))
  (define case-list (map path->name/m  (filter directory-exists? (directory-list source-dir #:build? #t))))
  (define (case->mutator-list cas)
    (map path->name/m (filter directory-exists? (directory-list (build-path source-dir cas) #:build? #t))))
  (define (mutator->mutation-list cas mut)
    (map path->name/m (filter directory-exists? (directory-list (build-path source-dir cas mut) #:build? #t))))
  (define (copy-mutantion cas mut mutation)
    (define source-mutation-path (build-path source-dir cas mut mutation))
    (define des-mutation-path (build-path dest-dir cas mut mutation))
    (unless (directory-exists? (build-path dest-dir cas))
      (make-directory (build-path dest-dir cas)))
    (unless (directory-exists? (build-path dest-dir cas mut))
      (make-directory (build-path dest-dir cas mut)))
    (unless (directory-exists? des-mutation-path)
      (make-directory des-mutation-path))
    (for ([f (directory-list #:build? #t source-mutation-path)]
          #:when (not (directory-exists? f)))
      (let-values ([(base name must-be-dir?) (split-path f)])
        (copy-file f (build-path des-mutation-path name) #:exists-ok? #t))
      ))
  (for ([cas case-list])
    (let ([mut-list (case->mutator-list cas)]
          [input-file (get-input-file cas)])
      (for ([mut mut-list])
        (let ([mutation-list (mutator->mutation-list cas mut)])
          (for ([mutation mutation-list])
            (when (interesting/p (build-path source-dir cas mut mutation (string-append (path->string mutation) "-dynamic.grift" ) ) input-file )
              (copy-mutantion cas mut mutation)
              )
            ))))))

(define fine-niubi-file "/home/sch/code/Grift/src/static_blame/test/benchmark/src/ray.grift")
(define configuration-report-path (build-path exp-dir "configuration test.csv"))
(define size-report-path (build-path exp-dir "size test.csv") )




;; we do not need to run this file, just analyse it.
(define (fine-configuration-test source-file dest-dir)
  (unless (directory-exists? dest-dir)
    (error 'fine-configuration-test (format "destination directory ~a does not exists" dest-dir) ))
  (define source-name (path->name/m source-file))
  (define dest-file (build-path dest-dir source-name) )
  (copy-file source-file (build-path dest-dir source-name) #:exists-ok? #t)
  ;; split 1200 configurations
  (define dynamizer-res-report (build-path dest-dir "dynamizer-test.txt"))
  (define dynamized-dir (build-path dest-dir (path-replace-extension source-name "")))
  (run-dynamizer dest-file dynamizer-res-report 100 10)
  (define-values (n-config n-type-node n-req-config) (analyse-dynamizer-output dynamizer-res-report))
  ;; now analyse each file
  (printf "percentage,count of dummy constraints,count of not dummy constraints,time\n")
  (for ([f (in-directory dynamized-dir)])
    (let ([report (flow-analyse f)])
      (define-values (ndum n-not-dum milisec) (report-props-refined report))
      (define percentage (dynamized-file->config-percentage f))
      (printf "~a,~a,~a,~a\n" percentage ndum n-not-dum milisec)
      )))

;; we do not need to run this file, just analyse it.
(define (fine-configuration-test-bug-detect source-file dest-dir)
  (unless (directory-exists? dest-dir)
    (error 'fine-configuration-test (format "destination directory ~a does not exists" dest-dir) ))
  (define source-name (path->name/m source-file))
  (define dest-file (build-path dest-dir source-name) )
  (copy-file source-file (build-path dest-dir source-name))
  ;; split 1200 configurations
  (define dynamizer-res-report (build-path dest-dir "dynamizer-test.txt"))
  (define dynamized-dir (build-path dest-dir (path-replace-extension source-name "")))
  (parameterize ([dynamizer-path "/usr/bin/dynamizer"])
      (with-handlers ([exn:dynamizer? (lambda (exn) (displayln (format "dynamizer error with ~a" (exn-message exn)))
                                        #f)])
        (run-dynamizer/v-clean dest-file 100 10)
        ))
  ;;(run-dynamizer dest-file dynamizer-res-report 100 10)
  ;; (define-values (n-config n-type-node n-req-config) (analyse-dynamizer-output dynamizer-res-report))
  ;; now analyse each file
  (printf "percentage,count of dummy constraints,count of not dummy constraints,time,number of bugs\n")
  (for ([f (in-directory dynamized-dir)])
    (define out-report '())
    (define-values (lst cpu-time real-time gc-time)
      (time-apply
       (lambda ()
         (let* ([report (flow-analyse f)]
                [source-syntax (read-program-from-name dest-file)]
                [sberrors ( set-union  ( set->list (SolverReport-strict report))
                                       (set->list  (SolverReport-dynamic report))
                                       (set->list
                                        (SolverReport-normal report)))])
           (set! out-report report)
           (length (bug-detect sberrors naive-cluster source-syntax))
           )
         )
       '()
       ))
    (define-values (ndum n-not-dum milisec) (report-props-refined out-report))
    ;; (define-values (ndum n-not-dum milisec) (report-props-refined report))
    (define percentage (dynamized-file->config-percentage f))
    (printf "~a,~a,~a,~a,~a\n" percentage ndum n-not-dum cpu-time (first lst))
    ))


(define (fine-size-test source-file dest-dir)
  (unless (directory-exists? dest-dir)
    (error 'fine-configuration-test (format "destination directory ~a does not exists" dest-dir) ))
  (define source-name (path->name/m source-file))
  (copy-file source-file (build-path dest-dir source-name) #:exists-ok? #t)
  ;; create n-sized files
  (define sized-dir (build-path dest-dir (path-replace-extension source-name "")))
  (unless (directory-exists? sized-dir)
    (make-directory sized-dir))
  ;; temporary 20-size
  ;; size expander, given a syntax object, return a list of syntax object
  (define source-syntax (read-program-from-name source-file))
  (define l-source-syntax (syntax->list source-syntax))
  (printf "loc,count of dummy constraints,count of not dummy constraints,time\n")
  (for ([i (in-range 0 9)])
    (define dest-file (build-path sized-dir (string-append (number->string i) ".grift")))
    (define lstx* (foldr append '() (map (lambda (stx) (size-expander stx i)) l-source-syntax)))
    (with-output-to-file dest-file #:exists 'replace
      (lambda ()
        (printf (syntax->string 
                 (with-syntax ([(s ...) lstx*])
                   #'(s ...))))
        ))
    (let ([report (flow-analyse dest-file)])
      (define-values (ndum n-not-dum milisec) (report-props-refined report))
      ;; (define-values (ncons msec nnor nstr ndyn) (report-props report))
      (define loc (count-of-lines dest-file))
      (printf "~a,~a,~a,~a\n" loc ndum n-not-dum milisec )
      )))

;; the same test, but test bug detector times
(define (fine-size-test-bug-detect source-file dest-dir)
  (unless (directory-exists? dest-dir)
    (error 'fine-configuration-test (format "destination directory ~a does not exists" dest-dir) ))
  (define source-name (path->name/m source-file))
  (copy-file source-file (build-path dest-dir source-name))
  ;; create n-sized files
  (define sized-dir (build-path dest-dir (path-replace-extension source-name "")))
  (unless (directory-exists? sized-dir)
    (make-directory sized-dir))
  ;; temporary 20-size
  ;; size expander, given a syntax object, return a list of syntax object
  (define source-syntax (read-program-from-name source-file))
  (define l-source-syntax (syntax->list source-syntax))
  (printf "loc,count of dummy constraints,count of not dummy constraints,time\n")
  (for ([i (in-range 0 9)])
    (define dest-file (build-path sized-dir (string-append (number->string i) ".grift")))
    (define lstx* (foldr append '() (map (lambda (stx) (size-expander stx i)) l-source-syntax)))
    (with-output-to-file dest-file #:exists 'replace
      (lambda ()
        (printf (syntax->string 
                 (with-syntax ([(s ...) lstx*])
                   #'(s ...))))
        ))
    (define out-report '())
    (define-values (lst cpu-time real-time gc-time)
      (time-apply
       (lambda ()
         (let* ([report (flow-analyse dest-file)]
                [source-syntax (read-program-from-name dest-file)]
                [sberrors ( set-union  ( set->list (SolverReport-strict report))
                                       (set->list  (SolverReport-dynamic report))
                                       (set->list
                                        (SolverReport-normal report)))])
           (bug-detect sberrors naive-cluster source-syntax)
           (set! out-report report))
         )
       '()
       ))
    (define-values (ndum n-not-dum milisec) (report-props-refined out-report))
    (define loc (count-of-lines dest-file))
    (printf "~a,~a,~a,~a\n" loc ndum n-not-dum cpu-time)
    ))


;;(fine-size-test-bug-detect "/src/Grift/src/static_blame/test/benchmark/src/ray.grift" "/app/size-test/")
(fine-configuration-test-bug-detect "/src/Grift/src/static_blame/test/benchmark/src/ray.grift" "/app/configuration-test/" )



(define (report-path->base-information p)
    (let ([elements (reverse (explode-path p))])
      (values (path->string (third elements)) (path->string (fourth elements))))
    )
(define (final-exp-analyse-report exp-dir)
  (define glob-pattern (build-path exp-dir  "*/*/*/final report.txt"))
  
  (display "cas,mutator,anntations,percentage,accepted?,loc,blame error?,analyse time,constraints,hit as normal,hit as strict,Normal,Strict,Wrong dynamic\n")
  (for
      ([f (in-glob glob-pattern)])
    (let-values ([(mutator cas) (report-path->base-information f)])    
      (let ([v (analyse-final-report f cas mutator)])
        (when v
          (display v))))
    ;; (define-values (n-c s-c) (whether-hit f))
    ;; (values (+ normal-hit n-c ) (+ sum s-c))))
    ))
;; (with-output-to-file #:exists 'replace (build-path exp-dir  "final report.csv")
;;     (lambda ()
;;       (final-exp-analyse-report exp-dir)))

;; (with-output-to-file #:exists 'replace configuration-report-path
;;     (lambda ()
;;       (fine-configuration-test fine-niubi-file "/home/sch/grift-configuration-test")))
;; (with-output-to-file #:exists 'replace size-report-path 
;;     (lambda ()
;;       (fine-size-test fine-niubi-file "/home/sch/grift-size-test")))




;; report/v1: how many different blame labels
;;            how many error for each blame labels
;;            error in each category
(define (detail-top-report/v1 report error-msg file-path)
  (let ([normal-hit? #f]
        [strict-hit? #f])
    (define-values (ncons msec nnor nstr ndyn) (report-props report))
    (when error-msg
      (set!-values (normal-hit? strict-hit?) (values (hit? (SolverReport-normal report) error-msg)
                                                     (hit? (SolverReport-strict report) error-msg)
                                                     )))
    (define strict-group (group-by
                          Tyflow-blame-label
                          (set->list (SolverReport-strict report))
                          ))
    
    
    (display (format "file name: ~a \n" file-path))
    (display (format "blame error?/err-msg: ~a\n" error-msg))
    (display (format "normal-hit?: ~a\n" normal-hit?))
    (display (format "strict-hit?: ~a\n" strict-hit?))
    (display (format "number of normal-hit: ~a\n" nnor))
    (display (format "number of strict-hit: ~a\n" nstr))
    (display (format "number of strict-group/blame-label: ~a\n" (length strict-group)))
    (for ([g strict-group])
      (let* ([bl (Tyflow-blame-label (car g))]
            [hit? (equal? bl error-msg)])
        (display (format "\n[group] Blame label:~a\n" bl))
        (display (format "\n    hit?:~a\n" hit?))
        (for ([i g])
          (display (format "\n~a\n" (Tyflow->string i)))
          ))
      )
    ))

;; the abstraction of exp-path is useless
(define (temp-test/v1 exp-path bench-dir)
  (define glob-patterns (build-path exp-dir  "*/*/*/*/*.grift"))
  (define shuffled (shuffle (glob glob-patterns)))
  
  (define bench-inputs-dir (build-path bench-dir "inputs"))
  
  (define (get-input-file case-name)
    (for/first ([f (directory-list (build-path bench-inputs-dir case-name) #:build? #t)])
      f))

  (define (get-case-from-path path)
    (path->string
     (fifth (reverse (explode-path path))))
    )

  (define counter 0)
  (for ([f shuffled]
        #:break (> counter 30))
    (let ([exe-name (make-temporary-file)]
          [out-file (make-temporary-file)]
          [input-file (get-input-file (get-case-from-path f))]
          [report (flow-analyse f)])
      (display (format "the file is ~a\n" f))
      (display (format "the input is ~a\n" input-file))
      (grift-compiler-compile f
                                    #:output exe-name)
      (run-compiled-program exe-name input-file out-file)
      (define error-msg (extract-error-message (port->string #:close? #t (open-input-file out-file))))
      (detail-top-report/v1 report error-msg f)
      
      (when error-msg (set! counter (+ counter 1)))
      )
    
    ;;(grift-compiler-compile f
    ;;                        #:output exe-name)
    ;; (run-compiled-program exe-name input-file version-output-filepath)

    ))
;; (with-output-to-file #:exists 'replace (build-path exp-dir  "precision.txt")
;;   (lambda ()  
;;     (temp-test/v1  exp-dir benchmark-directory)))

;;maybe just run
;;how many configuration?
;;maybe 12
(define (test-func)
  (grift-compiler-compile "src/static_blame/test/benchmark/src/blackscholes.grift"
                         
                          #:output "/tmp/test.o"))
;; (parameterize ([grift-logger-filter "src/static_blame/grift/*"]
;;                [grift-log-port (current-output-port)]
;;                [grift-log-level 'debug])
;;   (with-logging-to-port
;;     (current-output-port)
;;     (lambda ()
;;       (log-grift-debug-filter "testdebug")
;;       (grift-read "src/static_blame/test/benchmark/src/blackscholes.grift" ))
;;     #:logger grift-logger
;;     'debug)
  
;;   (test-func))

;; the abstraction of exp-path is useless
(define (temp-test/v2 exp-path)
  (define glob-patterns (build-path exp-path  "*/*/*/*.grift"))
  (define shuffled (shuffle (glob glob-patterns)))

  (define (get-mutate-pos-file prog-path)
    (define dir-path (path-only (path->complete-path prog-path)))
    (define mutant-index (path->string (first (reverse (explode-path dir-path)))))
    (build-path dir-path (format "~a-mutate-pos" mutant-index)))
  

  (define (get-case-from-path path)
    (path->string
     (fifth (reverse (explode-path path))))
    )
  (define blame-label-counter 0)
  (define true-positive-counter 0)

  (for ([f shuffled]
        [counter (in-naturals)]
        #:break (> counter 100))
    (let ([report (flow-analyse f)]
          [pos-file (get-mutate-pos-file f)])
      
      (displayln (format "the file is ~a\n" f))
      (displayln (format "the pos-file is ~a\n" pos-file))
      (define source-syntax (read-program-from-name f))

      (define mutated-seq (call-with-input-file pos-file (lambda (p) (port->seq p))))
      (define-values (ncons msec nnor nstr ndyn) (report-props report))

      (define strict-group (group-by
                            Tyflow-blame-label
                            (set->list (SolverReport-strict report))
                            ))
      (for ([g strict-group])
        (set! blame-label-counter (+ blame-label-counter 1))
        (let* ([bl (Tyflow-blame-label (car g))]
               [blame-label-pred (blame-msg->srcloc-pred bl)]
               [blame-syntax-seq (syntax-search blame-label-pred source-syntax)])
          (unless blame-syntax-seq
            (error 'blame-syntax-seq (format "I cannot find the blamed part in the source file, the blame message is ~a" bl)))
          (when (or (prefix?/seq blame-syntax-seq mutated-seq)
                    (prefix?/seq mutated-seq blame-syntax-seq))
            (set! true-positive-counter (+ true-positive-counter 1))
            )
          )))
    
    ;;(grift-compiler-compile f
    ;;                        #:output exe-name)
    ;; (run-compiled-program exe-name input-file version-output-filepath)
    )
  (displayln (format "the full predicate is ~a, the true positive is ~a" blame-label-counter true-positive-counter))
  )

;; input: source file, pos file
;; output: number of predications, number of true positives
(define (static-blame-bug-detection-test prog-path pos-path )
  (define blame-label-counter 0)
  (define true-positive-counter 0)
  (define source-syntax (read-program-from-name prog-path))
  (let ([report (flow-analyse prog-path)]
        [mutated-seq (call-with-input-file pos-path (lambda (p) (port->seq p))) ])
    (define strict-group (group-by
                            Tyflow-blame-label
                            (set->list (SolverReport-strict report))
                            ))
    (for ([g strict-group])
        (set! blame-label-counter (+ blame-label-counter 1))
        (let* ([bl (Tyflow-blame-label (car g))]
               [blame-label-pred (blame-msg->srcloc-pred bl)]
               [blame-syntax-seq (syntax-search blame-label-pred source-syntax)])
          (unless blame-syntax-seq
            (error 'blame-syntax-seq (format "I cannot find the blamed part in the source file, the blame message is ~a" bl)))
          (when (or (prefix?/seq blame-syntax-seq mutated-seq)
                    (prefix?/seq mutated-seq blame-syntax-seq))
            (set! true-positive-counter (+ true-positive-counter 1))
            )
          ))
    
    )
  (values blame-label-counter true-positive-counter)
  )

(define (dynamize!-static-file/files-and-pos-file file-path [nconfig 1] [bins 10] )
  
  (define dir-path (path-only (path->complete-path file-path)))
  (define mutant-index (path->string (first (reverse (explode-path dir-path)))))
  (define dynamic-path (build-path dir-path (format "~a-dynamic.grift" mutant-index)))
  (define pos-path (build-path dir-path (format "~a-mutate-pos" mutant-index)))
  (define lattice
    (parameterize ([dynamizer-path "/usr/bin/dynamizer"])
      (with-handlers ([exn:dynamizer? (lambda (exn) (displayln (format "dynamizer error with ~a" (exn-message exn)))
                                       #f)])
        (run-dynamizer/v-clean file-path nconfig bins)
        (directory-list #:build? #t (build-path (path-only file-path)
                                                (path-replace-extension
                                                 (file-name-from-path file-path) #""))))))
  
  (values (if lattice
              (cons file-path  (cons dynamic-path lattice))
              (list))
          pos-path)
    )
(define (tmp-test/v3 exp-dir)
  (define glob-patterns (build-path exp-dir  "*/*/*/*-static.grift"))
  (define-values ( blame-label-counter true-positive-counter) 
    (for/fold ([blame-label-counter 0]
               [true-positive-counter 0])
              ([g (in-glob glob-patterns)])
      (displayln (format "For the file ~a" g))
      (let-values ([(files pos-file) (dynamize!-static-file/files-and-pos-file g)])
        (let-values ([(b-c t-c)
                      (for/fold ([b-c 0]
                                 [t-c 0])
                                ([f (in-list files)])
                        (let-values ([(ta tb) (static-blame-bug-detection-test f pos-file)])
                          (values (+ b-c ta) (+ t-c tb) ))
                        )])
          (displayln (format "[Info]current count: ~a, current true posi: ~a"
                             (+ blame-label-counter b-c)
                             (+ true-positive-counter t-c)
                             ) )
          (values (+ blame-label-counter b-c)
                  (+ true-positive-counter t-c))
          )
        )))
  (displayln (format "The count is ~a, The true-positive is ~a "
                     blame-label-counter
                     true-positive-counter)))

;; record the precision and recall of strict potential error and wrong dynamic types
;; check three different matchers.
;; each content is a pair of a MCase and a possible #f MLattice
(define (tmp-test/v4 exp-dir)
  (define unstable-list-of-cases (read-exp-ground exp-dir))
  (define number-of-strict 0)
  (define number-of-wrong-dynamic 0)
  (define number-of-matched-strict 0)
  (define number-of-matched-wrong-dynamic 0)
  (for ([2p unstable-list-of-cases])
    (match-define (cons (MCase fstatic fdynamic pos _ _) mlattice) 2p)
    (displayln (format "[Case] path: ~a"  (path->string fstatic)))
    
    ;; SB analyse the file
    (define list-of-files (append  (list fstatic fdynamic)
                                   (if mlattice
                                       (map GFile-path (MLattice-dfiles mlattice))
                                       (list))))
    (for ([f list-of-files])
      (define report (flow-analyse f))
      (define source-syntax (read-program-from-name f))
      (define sberror-strict (set->list (SolverReport-strict report)))
      (define sberror-wdn (set->list (SolverReport-dynamic report)))

      (define-values (nbug-strict mat-strict)
        (matched-bug-numbers source-syntax pos subtree-matcher (bug-detect sberror-strict naive-cluster source-syntax)))
      (define-values (nbug-wdn mat-wdn)
        (matched-bug-numbers source-syntax pos subtree-matcher (bug-detect sberror-wdn naive-cluster source-syntax)))
      (set! number-of-strict (+ number-of-strict nbug-strict))
      (set! number-of-wrong-dynamic (+ number-of-wrong-dynamic nbug-wdn))
      (set! number-of-matched-strict (+ number-of-matched-strict mat-strict))
      (set! number-of-matched-wrong-dynamic (+ number-of-matched-wrong-dynamic mat-wdn))   
      ))
  (displayln (format "[Now] strict :~a/~a wdn :~a/~a"
                       number-of-matched-strict number-of-strict
                       number-of-matched-wrong-dynamic number-of-wrong-dynamic)))


(define (collect-a-file f real-pos [out (current-output-port)])
    (define report (flow-analyse f))
    (define source-syntax (read-program-from-name f))
    (define sberror-strict (set->list (SolverReport-strict report)))
  (define sberror-wdn (set->list (SolverReport-dynamic report)))
  (define sberror-normal (set->list (SolverReport-normal report)))

    (define (tp? sb)
      (subtree-matcher source-syntax real-pos sb))

  (define (tp-spe? sb)
    (up-matcher source-syntax real-pos sb))
    
    (define (get-true-positive lbugs)
      (filter tp? lbugs))

    
    (define l-bugs-strict
      (bug-detect sberror-strict naive-cluster source-syntax))
    (define l-bugs-wdn
      (bug-detect sberror-wdn naive-cluster source-syntax))
  (define l-bugs-normal
    (bug-detect sberror-normal naive-cluster source-syntax))
    ;;list matched bugs
    (define tp-strict (filter tp-spe? l-bugs-strict))
  (define fp-strict (filter-not tp-spe? l-bugs-strict))
  (define tp-normal (filter tp-spe? l-bugs-normal))
  (define fp-normal (filter-not tp-spe? l-bugs-normal))
  
    (define tp-wdn (filter tp? l-bugs-wdn))
    (define fp-wdn (filter-not tp? l-bugs-wdn))
    
    ;; list all bugs
    (displayln (format "~a,~a,~a,~a,~a,~a,~a,~a,~a"
                       f
                       (length l-bugs-normal)
                       (length tp-normal)
                       
                       (length l-bugs-strict)
                       (length tp-strict)
                       (length l-bugs-wdn)
                       (length tp-wdn)
                       (lbugs->lseqs fp-strict)
                       (lbugs->lseqs fp-wdn)
                       
                       ) out))

(define (bug-detect-a-single-file/dynamized dfile real-pos [out (current-output-port)])
  (define f (GFile-path dfile))
  (define percentage (DFile-percentage dfile))
  (define report (flow-analyse  f))
  (define source-syntax (read-program-from-name f))
  (define sberror-strict (set->list (SolverReport-strict report)))
  (define sberror-wdn (set->list (SolverReport-dynamic report)))

  (define (tp? sb)
    (subtree-matcher source-syntax real-pos sb))
    
  (define (get-true-positive lbugs)
    (filter tp? lbugs))

    
  (define l-bugs-strict
    (bug-detect sberror-strict naive-cluster source-syntax))
  (define l-bugs-wdn
    (bug-detect sberror-wdn naive-cluster source-syntax))
  ;;list matched bugs
  (define tp-strict (filter tp? l-bugs-strict))
  (define fp-strict (filter-not tp? l-bugs-strict))
  (define tp-wdn (filter tp? l-bugs-wdn))
  (define fp-wdn (filter-not tp? l-bugs-wdn))
    
  ;; list all bugs
  (displayln (format "~a,~a,~a,~a,~a,~a,~a,~a"
                     f
                     percentage
                     (length l-bugs-strict)
                     (length tp-strict)
                     (length l-bugs-wdn)
                     (length tp-wdn)
                     (lbugs->lseqs fp-strict)
                     (lbugs->lseqs fp-wdn)
                     ) out))

(define (BUG-detect-data-collection exp-dir [outport (current-output-port)])
  (define unstable-list-of-cases (read-exp-ground exp-dir))
  ;; for each program:
  ;; record the file path
  ;; How many Strict BUG report? How many WDN bug report?
  ;; How many positive?
  ;; record each false positive
  ;; Is this bug detected?
  
  (displayln "path,npe-num,tp-npe,spe-num,tp-spe,wdn-num,tp-wdn,fp-spe,fp-wdn" outport)
  (for ([2p unstable-list-of-cases])
    (match-define (cons (MCase fstatic fdynamic pos _ _) mlattice) 2p)
    (displayln (format "[Case] path: ~a"  (path->string fstatic)))
    
    ;; SB analyse the file
    (define list-of-files (append  (list fstatic fdynamic)
                                   (if mlattice
                                       (map GFile-path (MLattice-dfiles mlattice))
                                       (list))))
    (for ([f list-of-files])
      (collect-a-file f pos outport))
    )
  
  )



(define (healthy-program-test/dynamize exp-dir)
  (define glob-pat (build-path exp-dir "*.grift"))
  (for ([f (in-glob glob-pat)])
    (displayln (format "dynamizing ~a" f))
    
    (parameterize ([dynamizer-path "/usr/bin/dynamizer"])
      (with-handlers ([exn:dynamizer? (lambda (exn) (displayln (format "dynamizer error with ~a" (exn-message exn)))
                                        #f)])
        (run-dynamizer/v-clean f 100 10)
        )) 
    ))

(define (healthy-program-test/run exp-dir)
  (define glob-pat (build-path exp-dir "*.grift"))
  (displayln "path,percentage,spe-num,tp-spe,wdn-num,tp-wdn,fp-spe,fp-wdn")
  (for ([f (in-glob glob-pat)])
    (define lattice-dir (path-replace-extension f #""))
    (define mltce (construct-mlattice f lattice-dir))
    ;; then, bug detect
    (for ([g  (MLattice-dfiles mltce)])
      (bug-detect-a-single-file/dynamized g #f)
      )))


;; (with-output-to-file #:exists 'replace "/exp/data-collection.csv"
;;   (lambda ()  
;;     (BUG-detect-data-collection "/exp")))

;; create 1000 dynamized file for each case
;; and then test it.

;; for each case, dynamize each file for 1000-file
(define (buggy-program-test/dynamize exp-dir)
  (define glob-patterns (build-path exp-dir  "*/*/*/*-static.grift"))
  (for ([g (in-glob glob-patterns)])
    (let-values ([(files pos-file) (dynamize!-static-file/files-and-pos-file g 100 10)])
      (displayln g)
      )))

;; for each case, read this case, and bug-detection
(define (buggy-program-test/run exp-dir [sample-file "sample_fp_wdn.txt" ] [outport (current-output-port)])
  (define lps (read-exp-ground exp-dir))
  ;; read-pre-from file
  (define file-names 
    (call-with-input-file sample-file
      (lambda (p)
        (for/list ([s (in-lines p)])
          (string-trim s))
        )))
  ;; (displayln file-names)
  (displayln "path,percentage,spe-num,tp-spe,wdn-num,tp-wdn,fp-spe,fp-wdn" outport)
  (for ([2p lps])
    (match-define (cons (MCase fstatic fdynamic pos _ _) mlattice) 2p)
    ;;(displayln (format "[Case] path: ~a"  (path->string fstatic)))
    ;;
    ;; SB analyse the file
    ;; first we analyse the dynamic file, and randomly choose some with false-positive.
    ;; (define list-of-dfiles (MLattice-dfiles mlattice))
    ;; (for ([f list-of-dfiles])
    ;;   (bug-detect-a-single-file/dynamized f pos outport))
    ;; (collect-a-file fdynamic pos outport)
    (when (member (path->string fdynamic) file-names)
      (displayln (format "[INFO] Now the file is: ~a, time is ~a" fstatic (date-format/my (current-date)) ) )
      (for ([f (MLattice-dfiles mlattice)])
        (bug-detect-a-single-file/dynamized f pos outport)))
    )
  )

;; scripts to read a report csv file:
;; first, read our ground, and for each line,
;; read it's all false positives, and calculate it's location, and real pos location
(define (read-from-string str)
  (read (open-input-string str)))
(define (BUG-detect-parse-line str)
  (string-split str ","))

(define (find-pos-by-path lps path)
  (define pos 
    (for/fold ([ret #f])
              ([2p lps]
               #:break ret)
      (match-define (cons (MCase fstatic fdynamic pos _ _) mlattice) 2p)
      (define list-of-files (append  (list fstatic fdynamic)
                                     (if mlattice
                                         (map GFile-path (MLattice-dfiles mlattice))
                                         (list))))
      (if (member (string->path path) list-of-files)
          pos
          #f)
      ))
  pos)


(define (analyse-fp-wdn exp-dir report-file [output-filepath "fp-wdns.txt"])
  (define lps (read-exp-ground exp-dir))

  
  (define (analyse-line l)
    ;; get it's path from the first.
    (define componets-line (BUG-detect-parse-line l))
    ;; the first is the path
    (define path (first componets-line))

    ;; BUG!!!: The seventh is the fp-wdn, while the sixth is the fp-spe
    ;; the sixth is the false positive locations
    
    
    (define fps  (read-from-string (seventh componets-line)))
    
    ;; get the case (by the static-file) from the playground
    ;; get the real-pos
    (define real-pos (find-pos-by-path lps path))

    ;; then, map the loc into srclocs.
    (define source-syntax (read-program-from-name path))

    (define true-bug-srcloc (seq->srcloc source-syntax real-pos))
    (define list-of-false-bug-srcloc (map  (lambda (seq) (seq->srcloc source-syntax seq)) fps))
    
    
    (displayln (format "~a,~a,~a, ~a"
                       path
                       true-bug-srcloc
                       (length list-of-false-bug-srcloc)
                       list-of-false-bug-srcloc))
    )
  (with-output-to-file output-filepath #:exists 'replace
    (lambda ()
      (call-with-input-file report-file
        (lambda (p)
          (for ([l (in-lines p)]
                [i (in-naturals)])
            
            (if (equal? i 0)
                (displayln "file-path,true-srcloc,number-of-false-positive,false-positive")
                (analyse-line l)))
          )))))

(define (analyse-fp-spe exp-dir report-file output-filepath )
  (define lps (read-exp-ground exp-dir))
    (define (analyse-line l)
    ;; get it's path from the first.
    (define componets-line (BUG-detect-parse-line l))
    ;; the first is the path
    (define path (first componets-line))

    ;; BUG!!!: The seventh is the fp-wdn, while the sixth is the fp-spe
    ;; the sixth is the false positive locations
    
    
    (define fps  (read-from-string (eighth componets-line)))
    
    ;; get the case (by the static-file) from the playground
    ;; get the real-pos
    (define real-pos (find-pos-by-path lps path))

    ;; then, map the loc into srclocs.
    (define source-syntax (read-program-from-name path))

    (define true-bug-srcloc (seq->srcloc source-syntax real-pos))
    (define list-of-false-bug-srcloc (map  (lambda (seq) (seq->srcloc source-syntax seq)) fps))
    
    
    (displayln (format "~a,~a,~a, ~a"
                       path
                       true-bug-srcloc
                       (length list-of-false-bug-srcloc)
                       list-of-false-bug-srcloc))
      )
  (with-output-to-file output-filepath #:exists 'replace
    (lambda ()
      (call-with-input-file report-file
        (lambda (p)
          (for ([l (in-lines p)]
                [i (in-naturals)])
            
            (if (equal? i 0)
                (displayln "file-path,true-srcloc,number-of-false-positive,false-positive")
                (analyse-line l)))
          ))))
  )

(define (analyse-fn exp-dir report-file [output-filepath "fn-transformed.csv"])
  (define lps (read-exp-ground exp-dir))
  (define (analyse-line l)
    ;; get it's path from the first.
    (define componets-line (BUG-detect-parse-line l))
    ;; the first is the path
    (define path (first componets-line))
    
    ;; get the case (by the static-file) from the playground
    ;; get the real-pos
    (define real-pos (find-pos-by-path lps path))

    ;; then, map the loc into srclocs.
    (define source-syntax (read-program-from-name path))

    (define true-bug-srcloc (seq->srcloc source-syntax real-pos))
    (displayln (format "~a,~a"
                       path
                       true-bug-srcloc
                       ))
    )
  (with-output-to-file output-filepath #:exists 'replace
    (lambda ()
      (call-with-input-file report-file
        (lambda (p)
          (for ([l (in-lines p)]
                [i (in-naturals)])
            (if (equal? i 0)
                (displayln "file-path,true-srcloc")
                (analyse-line l)))
          ))))
  )

(define (tmp-test/v5 base-path lattice-path pos [outport (current-output-port)])
  (define mlattice (construct-mlattice base-path lattice-path))
  (define pos-seq (file->seq pos) )
  (displayln "path,percentage,spe-num,tp-spe,wdn-num,tp-wdn,fp-spe,fp-wdn" outport)
  
  (for ([f (MLattice-dfiles mlattice)])
    (displayln (format "[Info] now is the file ~a" (GFile-path f)))
    (bug-detect-a-single-file/dynamized f pos-seq outport)))

(define (find-undynamized-cases exp-dir)
  (define lps (read-exp-ground exp-dir))
  (for ([2p lps])
    (match-define (cons (MCase fstatic fdynamic pos _ _) mlattice) 2p)
    ;;(displayln (format "[Case] path: ~a"  (path->string fstatic)))
    ;;
    ;; SB analyse the file
    ;; first we analyse the dynamic file, and randomly choose some with false-positive.
    ;; (define list-of-dfiles (MLattice-dfiles mlattice))
    ;; (for ([f list-of-dfiles])
    ;;   (bug-detect-a-single-file/dynamized f pos outport))
    ;; (collect-a-file fdynamic pos outport)
    (unless mlattice
      (displayln (format "~a" fstatic)))
  ))

;;(module+ test
;;   (define fail-prg "/home/sch/grift-exp/quicksort/arithmetic/mutant3/mutant3-dynamic.grift")
;;   (define output-filepath "/home/sch/grift-exp/quicksort/arithmetic/mutant3/dynamic-output.txt"  )
;;   (define error-msg (extract-error-message (port->string #:close? #t (open-input-file output-filepath))))
;;   (define report (flow-analyse fail-prg))
;;   (define solved-msgs (map Tyflow-blame-label (filter (lambda (x) (not (dummy? x))) (export-type-flow (SolverReport-solver report)))))

;;   (define solved-flows (filter (lambda (x) (not (dummy? x))) (export-type-flow (SolverReport-solver report))))

;;   (define error-flow-list (filter (lambda (x) (string=? (Tyflow-blame-label x) error-msg)) solved-flows))
  
;;   (define error-flow (first (filter (lambda (x) (string=? (Tyflow-blame-label x) error-msg)) solved-flows)))
;;   (define this-solver (SolverReport-solver report))
;; (define this-solver-inflow (CSolver-inflows this-solver))
;; (define this-solver-flows (set->list (CSolver-collection this-solver)))
  ;; test whether it is in
  ;;(member error-msg solved-msgs)
;; (sequence-length (SolverReport-normal report))
;; (filter (lambda (x) (string=? (Tyflow-blame-label x) error-msg)) solved-flows)
  ;; (hash-ref this-solver-inflow (Tyflow-from error-flow))
  ;; (filter (lambda (flow) (equal? (Tyflow-from error-flow) (Tyflow-from flow))) (set->list (SolverReport-normal report)))
;;  )



