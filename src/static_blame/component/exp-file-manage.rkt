#lang racket
;; exp file manager, given a base directory of experiment files,
;; it will give us
;; 1. in-grift-files a list of all grift program files,
;;    with full static, full dynamic and possible migrated files.
;; 2. in-full-static/full-dynamic/migrated, give a files of functions
;; an experiment setup consists of:
;; cases
;; The bench consists of seven source files
;; each source files have four mutator applied in, and therefore multiple mutations
;; of each mutator type
;; each mutation consists of
;; a full-static version
;; a full-dynamic version
;; a pos-file
;; the migratory lattice of the full-static version
(require "./stx-seq-loc.rkt")
(provide (all-defined-out)
         (struct-out DFile)
         (struct-out GFile))
(define mutator-types '(position-swap constant-swap condition arithmetic))
(define source-cases  '(tak ray quicksort fft blackscholes matmult n_body))

(define case-static-suffix "-static.grift")
(define case-dynamic-suffix "-dynamic.grift")
(define case-pos-suffix "-mutate-pos")


;; top-down, the migratory lattice
;; A migratory lattice consists of:
;; a file which is the base of this lattice
;; a list of files, which consists of a path and a percentage


;; G for Grift
;; do not attach too many assumptions to a grift file
(struct GFile (path)
  #:transparent)

;; D for dynamized
(struct DFile GFile (percentage)
  #:transparent)

(define (normalize-gfile gfile)
  (cond [(GFile? gfile)
         (GFile (simple-form-path (GFile-path gfile)))]
        [(path-string? gfile)
         (GFile (simple-form-path gfile))]
        [else
         (error 'normalize-gfile (format "the object ~a cannot be identified as a grift source file" gfile))]))



;; construct a DFile with respect to a percentage
(define (construct-DFile gfile)
  (define gfile-obj (normalize-gfile gfile))
  (define ifile (GFile-path gfile-obj))
  (define percentage
    (call-with-input-file ifile (lambda (p)
                                  (for/first ([s (in-lines p)])
                                    (string->number (string-trim (string-trim s "%") ";; "))))))
  (unless percentage
    (error 'construct-DFile (format "the file ~a does not contains a percentage")))
  (DFile ifile percentage))


(struct MLattice (base dfiles)
  #:transparent)

(define (construct-mlattice base-path lattice-dir)
  (define gfile-obj (normalize-gfile base-path))
  ;; filter the directory with extension grift.
  (define dynamic-paths
    (filter (lambda (p) (path-has-extension? p #".grift"))
            (directory-list lattice-dir #:build? #t)))
  ;; map the paths into DFiles
  (define dfiles
    (map (lambda (p) (construct-DFile p))
         dynamic-paths))
  (MLattice gfile-obj dfiles))


;; then we need a data structure to represent one case.
;; a mutated case is a static file, a dynamic file, a pos-file
;; and a source, a mutator.
(struct MCase (fstatic fdynamic pos tsource tmutator)
  #:transparent)

;; the pos file will be translated into pos itself.
;; this function returns two values, one is a MCase
;; the other is a boolean indicates the lattice directory.
(define (read-a-case path tsource tmutator)
  (define normal-path (simple-form-path path))
  (define (path-index-suffix->file-path p index suffix)
    (let* ([filename (string-append index suffix)]
           [filepath (build-path p filename)])
      (unless (file-exists? filepath)
        (error 'read-a-case (format "files under path ~a is not a mutated case" path)))
      filepath))
  (define case-index (path->string (first (reverse (explode-path normal-path)))))
  ;; get the static file
  (define static-file (path-index-suffix->file-path path case-index case-static-suffix))
  (define dynamic-file (path-index-suffix->file-path path case-index case-dynamic-suffix))
  (define pos-file (path-index-suffix->file-path path case-index case-pos-suffix))
  (define pos-seq (file->seq pos-file))
  ;; the possible lattice: with static's name
  (MCase static-file dynamic-file pos-seq
         tsource tmutator))

;;(define lattice-dir
;;    (path-replace-extension static-file #""))
;; a playground consists of:
;; a list of pair of mcase and possible mlattice
(struct SBmutground (lps)
  #:transparent)




(define (read-exp-ground exp-dir)
  ;; a list of tsources
  ;; a list of tmutators
  ;; a list of cases
  (define (get-the-symbol-of-a-directory p)
    (let-values ([(base name m)
                  (split-path p)])
      (string->symbol (path->string name))))
  (define (list-dirs p)
    (filter
     directory-exists? 
     (directory-list p  #:build? #t)))
  (define (read-a-mutator p tsource tmutator)
    (define case-list (list-dirs p))
  ;; and ?
    (map (lambda (case-dir)
           (let [(mcase (read-a-case case-dir tsource tmutator))]
             (define lattice-dir
               (path-replace-extension (MCase-fstatic mcase) #""))
             (if (directory-exists? lattice-dir)
                 (cons mcase (construct-mlattice (MCase-fstatic mcase) lattice-dir))
                 (cons mcase #f))))
         case-list))
  (define (read-a-source p tsource)
    (define mutator-list (list-dirs p))
    (for/fold ([lps (list)])
              ([mut-subdir mutator-list])
      (let ([tmut (get-the-symbol-of-a-directory mut-subdir)])
        (append lps (read-a-mutator mut-subdir tsource tmut))
        )))
  
  (define work-dir (simple-form-path exp-dir))
  ;; 
  (define raw-list (list-dirs exp-dir))
  ;; get the name of these directories, as name of tsource
  ;; and we iterate this
  (for/fold ([lps (list)])
            ([source-subdir raw-list])
    (let ([tsource (get-the-symbol-of-a-directory source-subdir)])
      (append lps (read-a-source source-subdir tsource))))
  )


