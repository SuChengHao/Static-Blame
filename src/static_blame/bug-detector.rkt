#lang racket
#| a bug detector built on static blame, the core is how to translate a
solver-report to a bunch of bugs.
The static blame may produce plenty of potential errors, which is essential
wrong casts may occur in execution.
However, in software engineering and practical scenes, bugs are defined informally as
code element that cannot implement their function.

Therefore, we need to translate potential errors into bugs.

The naive translation, is use the inherent feature that textual locations as blame labels.
That is, every blame label is a textual location of the source file.
We can simply translate normal and strict potential errors into their monitoring blame labels.

And a wrong dynamic cast is translated into the program points it carries.

The other translation is needed to reduce false positives. For example, we can cluster near
locations into one.

The translator is a parameter of the whole bug detection process.
It consists of two parts, an error->location trans and a cluster process.
|#

;; error->location trans
(require "./component/stx-seq-loc.rkt")
(require "./component/blame-label.rkt")
(require "./flow_analysis.rkt")
(require "./refinement.rkt")
(require "./type_flow.rkt")
(provide (all-defined-out))

(define (potential-error->stx-loc source-syntax perr)
  (define blabel (Tyflow-blame-label perr) )
  (define ret 
    (syntax-search (blame-msg->srcloc-pred blabel)
                   source-syntax))
  (unless ret
    (error 'potential-error->stx-loc
           (format "I cannot find the blamed part in the source file, the blame message is ~a" blabel)))
  ret)



(define (wrong-dynamic-type->stx-loc source-syntax wdyn)
  (match-define (Ltype (Clabel (Ppoint wsrc) _) _) wdyn)
  (define ret
    (syntax-search/srcloc-line-column
     (srcloc-line wsrc)
     (srcloc-column wsrc)
     source-syntax))
  (unless ret
    (error 'wrong-dynamic-type->stx-loc (format "I cannot find the program point in the source file, the program point is ~a" wsrc)
           ))
  ret)


;; output: a sequence of bugs
;; what is a reported bug in our project?
;; Basically, it needs a syntax location, a source(reason/explanation), and/or others
;; Some auxiliary infomation, like file/path, source syntax, is not necessary.

;; it will be clustered into one bug, therefore, a source is a set(list) of reported errors.

;; report into wrong messages.
;; S for static blame
(struct SBug (location reasons source-syntax)
  #:transparent)

;; a raw bug is a SBug with single source. 
(define (mk-raw-bug
         sberror source-syntax)
  (define location 
    (cond [(Tyflow? sberror)
           (potential-error->stx-loc source-syntax sberror)]
          [(Ltype? sberror)
           (wrong-dynamic-type->stx-loc source-syntax sberror)]
          [else
           (error 'mk-raw-bug (format "wrong types of reported error :~a \n" sberror))]))
  
  (SBug location (set sberror)
        source-syntax))

;; bug matcher, detect whether a SBug match a syntax position in the source
;; note that we assume that there is one "real" bug in the source file.

;; naive-matcher, that the real-loc ``is'' exactly the location of the sbug.
(define (naive-matcher source-syntax real-loc sbug)
  (seq-equal? real-loc (SBug-location sbug)))

;;subtree-matcher, that the sbug is the subtree of the real-loc, that is, real-loc is the prefix of the sbug.
(define (subtree-matcher source-syntax real-loc sbug)
  (prefix?/seq real-loc (SBug-location sbug) ))

;;bisub-matcher, that is true if one is the subtree of the other.
(define (bisub-matcher source-syntax real-loc sbug)
  (or (prefix?/seq real-loc (SBug-location sbug))
      (prefix?/seq (SBug-location sbug) real-loc)))

;;up-matcher, that the sbug is the subtree of the immediate father of the real-loc
(define (up-matcher source-syntax real-loc sbug)
  (prefix?/seq (immediate-father real-loc) (SBug-location sbug)))


;; cluster, a cluster is a function which, given a source-syntax and a list of bugs
;; we return a single bug for every location.
;; return a list of new bugs.
(define (naive-cluster source-syntax sbugs)
  ;; first, allocate a mutate-hash, maps a seq into a set of sources
  (define loc-hash (make-hash))
  (for ([work-bug sbugs])
    (let ([loc (SBug-location work-bug)]
          [reas (SBug-reasons work-bug)])
      (hash-set! loc-hash loc (set-union (hash-ref loc-hash loc (set))
                                         reas))))
  ;; then, make new bugs from collected bugs
  (for/fold ([newbugs (list)])
            ([(key value) (in-hash loc-hash)])
    (cons (SBug key value source-syntax) newbugs)))

;; ;;simple cluster, cluster immediate father and son nodes, and return the lub.
;; (define (simple-cluster source-syntax sbugs)
;;   ;; for every sbug, look into its location,
;;   ;; find a immediate near location.
  
;;   )



;; main bug-detect procedure, what we need is a list of sberrors, a source-syntax and a cluster
;; translate static blame results into bug SBugs, and report the final bug-detection results.
;; I need to figure out a way to record the results.
;; result: reported bug
(define (bug-detect sberrors cluster source-syntax)
  (define list-of-raw-bugs 
    (map (lambda (sb)
           (mk-raw-bug sb source-syntax))
         sberrors))
  (cluster source-syntax list-of-raw-bugs))


;; how many bugs reported?
;; how many bugs matched?
(define (matched-bug-numbers source-syntax real-loc matcher lbugs)
  (define nbugs (length lbugs))
  (define (matched->number sb)
    (if real-loc 
        (if (matcher source-syntax real-loc sb)
            1
            0)
        0))
  (define matched
    (for/sum ([sb lbugs])
      (matched->number sb)))
  (values nbugs matched))

(define (errors->bugs->numbers source-syntax cluster matcher real-loc sberrors)
  (matched-bug-numbers source-syntax real-loc matcher (bug-detect sberrors cluster source-syntax)))

(define (lbugs->lseqs lbugs)
  (map SBug-location lbugs))
