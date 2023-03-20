#lang racket
(require "../type_flow_generation.rkt"
         "../type_flow.rkt"
         "../../grift/syntax-to-grift0.rkt"
         "./fake-insert-casts.rkt"
         "../../grift/type-check.rkt"
         "../../language/forms.rkt"
         "./interesting_filter.rkt"
         "../flow_analysis.rkt"
         "./mutate.rkt"
         )
(require (rename-in "../../grift/read.rkt"
                    (read grift-read))
         (rename-in "../../compile.rkt"
                    (compile grift-compiler-compile)))
(require racket/date)

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

(with-output-to-file #:exists 'replace configuration-report-path
    (lambda ()
      (fine-configuration-test fine-niubi-file "/home/sch/grift-configuration-test")))
(with-output-to-file #:exists 'replace size-report-path 
    (lambda ()
      (fine-size-test fine-niubi-file "/home/sch/grift-size-test")))


;;maybe just run
;;how many configuration?
;;maybe 12



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



