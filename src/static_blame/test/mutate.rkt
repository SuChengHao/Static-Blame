#lang racket
(require syntax/parse
         racket/syntax
         mutate ; provides both mutate/define and mutate/quick
         racket/stream
         ;; syntax/to-string
         fmt
         syntax/stx
         file/glob)
(require (rename-in "./grift-read.rkt"
                    (read grift-read)))
(provide read-program-from-name
         size-expander
         syntax->string)


(define-syntax-class binding
  [pattern (var:id (~optional (~seq (~datum :) ty )) rhs)])

(define-splicing-syntax-class optional-colon-type
  [pattern (~optional (~seq (~datum :) ty) )])

(define-splicing-syntax-class optionally-annotated-id
  [pattern (~seq id:id oa:optional-colon-type) #:attr ty (attribute oa.ty)])

(define-syntax-class formal-parameter
  [pattern [var:id (~optional (~seq  (~datum :) ty))]]
  )
(define-syntax-class switch-clause
  [pattern [(case*:integer ...+) rhs]])
(define-syntax-class index-binding
    [pattern ((~var id id) (~var start) (~var stop))])
(define-syntax-class accumulator-binding
  #:datum-literals (:)
  [pattern ((~var id id)
            (~optional (~seq : (~var type)))
            (~var init))])

(define (syntax->string stxes)
  (program-format
   (let ([s (open-output-string)])
     (define lstx (syntax->list stxes))
     (map (lambda (stx) (fprintf s "~s\n" (syntax->datum stx))) lstx)
     (get-output-string s))))

(define special-forms-list
  '(let define letrec : lambda if repeat begin tuple tuple-proj box unbox box-set! make-vector vector-ref vector-set! vector-length))
(define ignore-tuple-proj
  (syntax-parser
    [({~datum tuple-proj} t i:integer)
     (list #'t
           (lambda (new-t) #`(tuple-proj #,new-t i))
           empty)]
    [other-e
     (list #'other-e
           (lambda (x) x)
           empty)]))
;; ignore type annotations
(define ignore-type-annotations
  (syntax-parser
    [({~datum define} v:optionally-annotated-id e:expr)
     (list #'e
           (lambda (new-e) #`(define v.id (~? (~@ : v.ty))  #,new-e))
           empty)]
    [({~datum define} (f:id f*:formal-parameter ...) r:optional-colon-type e*:expr ... e:expr)
     (list #'(begin-for-mutate e* ... e)
           (lambda (new-es)
             (syntax-parse new-es
               [({~datum begin-for-mutate} e ...)
                #`(define (f f* ...) (~? (~@ : r.ty) ) e ...)]))
           empty)]
    [({~or {~datum :} {~datum ann}} expr ty (~optional (~seq l:str)))
     (list #'expr
           (lambda (new-expr) #`(: #,new-expr ty (~? (~@ l))))
           empty)]
    [(bnd:binding ...)
     (list #'(begin-for-mutate bnd.rhs ...)
           (lambda (new-rhss)
             ;; first, transfrom the results into list
             ;; then, create new bindings
             ;; then, combining the result
             
             (with-syntax ([(_ new/rhs ...) (syntax->list new-rhss)])
               #`((bnd.var (~? (~@ : bnd.ty)) new/rhs) ...))
             )
           empty)]
    [({~datum repeat} i:index-binding a:accumulator-binding M)
     (list #'(begin i.start i.stop a.init M)
           (lambda (new-exps)
             (with-syntax ([(_ new-start new-stop new-init new-M) new-exps])
               #'(repeat (i.id new-start new-stop) (a.id (~? (~@ : a.type)) new-init) new-M)
               ))
           empty)]
    [other-e
     (list #'other-e
           (lambda (x) x)
           empty)]))

(define (weak-fmls fml*)
  (syntax-parse fml*
    [(f*:formal-parameter ...)
     (syntax/loc fml* ((f*.var : Dyn) ...))]))

(define (total-dynamizer stx)
  (syntax-parse stx
    [({~datum define} v:optionally-annotated-id e:expr)
     ((lambda (new-e) (quasisyntax/loc stx (define v.id : Dyn #,new-e))) (total-dynamizer #'e))]
    [({~datum define} (f:id f*:formal-parameter ...) r:optional-colon-type e*:expr ... e:expr)
     ((lambda (new-es)
        (with-syntax ([(new/e ...) new-es])
          (quasisyntax/loc stx (define (f #,@(weak-fmls #'(f* ...))) : Dyn new/e ...)))) (map total-dynamizer (syntax->list #'(e* ... e))))]
    [({~or {~datum :} {~datum ann}} expr ty (~optional (~seq l:str)))
     ((lambda (new-expr) (quasisyntax/loc stx (: #,new-expr Dyn (~? (~@ l))))) (total-dynamizer #'expr))]
    [(bnd:binding ...)
     ((lambda (new-rhss)
             ;; first, transfrom the results into list
             ;; then, create new bindings
             ;; then, combining the result
             
             (with-syntax ([(new/rhs ...) new-rhss])
               (quasisyntax/loc stx ((bnd.var : Dyn new/rhs) ...)))
        ) (map total-dynamizer (syntax->list #'(bnd.rhs ...))))]
    [({~datum repeat} i:index-binding a:accumulator-binding M)
     ((lambda (new-exps) (with-syntax ([(_ new-start new-stop new-init new-M) new-exps])
                           (syntax/loc stx (repeat (i.id new-start new-stop) (a.id : Dyn new-init) new-M))
                           ) ) (total-dynamizer #'(begin i.start i.stop a.init M)))]
    [other-e
     (if (stx-list? stx)
         (let ([stx* (map total-dynamizer (syntax->list stx))])
           (with-syntax ([(s ...) stx*])
             (syntax/loc stx  (s ...))))
         stx)]
    ))

(define (size-expander stx n)
  (syntax-parse stx
    [({~datum define} v:optionally-annotated-id e:expr)
     (cons stx
           (map (lambda (t)
                  (with-syntax ([new-id (format-id #'v.id "~a~a" (syntax-e #'v.id) t)])
                    #'(define new-id (~? (~@ : v.ty)) e))) (build-list n values)))]
    [({~datum define} (f:id f*:formal-parameter ...) r:optional-colon-type e*:expr ... e:expr)
     (cons stx
           (map
            (lambda (t) (with-syntax ([new-id (format-id #'f "~a~a" (syntax-e #'f) t)])
                          #'(define (new-id f* ...) (~? (~@ : r.ty) ) e* ... e)))
            (build-list n values)))]
    [_ (build-list (+ n 1) (lambda (n) stx))]
    ))

(define (read-program-from-name filepath)
  (let ([prg (grift-read filepath)])
    ;; (define lstx (syntax->list prg))
    (with-syntax ([(stx ...) prg])
      #'(stx ...))))

(define (cross-swap-iter lst n pre)
  (if (= n 0)
      (match lst
        [(list a b rest ...)
         (with-syntax ([as a]
                       [bs b]) 
           (append (reverse pre) (cons #'(: bs Dyn) (cons #'(: as Dyn) rest))))])
      (cross-swap-iter (cdr lst) (- n 1) (cons (car lst) pre) )))

(define (cross-swap lst n)
  (cross-swap-iter lst n '()))




;; swaps two sub-expressions
(define program-mutations-position-swap
  (build-mutation-engine
   #:mutators
   (define-simple-mutator (position-first stx)
     #:pattern (f arg ...)
     #:when (and (not (member (syntax->datum #'f) special-forms-list)) (> (length (syntax->list #'(arg ...))) 1))
     ;; arg bounded into a list of stx objects.
     (let* ([arglst (syntax->list #'(arg ...))]
            [len (length arglst)]
            [modified-lst (cross-swap arglst 0)])
       (with-syntax ([(arg/c* ...) modified-lst])
         #'(f arg/c* ...))))
   (define-simple-mutator (position-last stx)
     #:pattern (f arg ...)
     #:when (and (not (member (syntax->datum #'f) special-forms-list)) (> (length (syntax->list #'(arg ...))) 3))
     ;; arg bounded into a list of stx objects.
     (let* ([arglst (syntax->list #'(arg ...))]
            [len (length arglst)]
            [modified-lst (cross-swap arglst (- len 2))])
       (with-syntax ([(arg/c* ...) modified-lst])
         #'(f arg/c* ...))))
   (define-simple-mutator (position-middle stx)
     #:pattern (f arg ...)
     #:when (and (not (member (syntax->datum #'f) special-forms-list)) (> (length (syntax->list #'(arg ...))) 5))
     (let* ([arglst (syntax->list #'(arg ...))]
            [len (length arglst)]
            )
       ;; (display (format "cross-swap : arglst: ~a\n length :~a\n" arglst len ))
       (define modified-lst (cross-swap arglst (quotient len 2)) )
       
       (with-syntax ([(arg/c* ...) modified-lst])
         
         #'(f arg/c* ...)))
     )
   #:expression-selector ignore-type-annotations
   #:syntax-only
   #:streaming))



(define program-mutation-constant-swap
  (build-mutation-engine
   #:mutators
   (define-constant-mutator (number-constant-swap v)
     [(? number?)                 #:-> (- v)]
     [(? integer?)                #:-> (exact->inexact v)]
     [(and (? number?) (? zero?)) #:-> 1])
   #:syntax-only
   #:streaming
   ))
(define program-mutation-constant-swap-dynamic
  (build-mutation-engine
   #:mutators
   (define-simple-mutator (negation-swap stx)
     #:pattern v:number
     (with-syntax ([to-v (- (syntax-e #'v))])
       #'(: to-v Dyn)))
   (define-simple-mutator (exact->inexact-swap stx)
     #:pattern v:number
     #:when (integer? (syntax-e #'v))
     (with-syntax ([to-v (let ([inner (syntax-e #'v)])
                           (exact->inexact inner)
                           )])
       #'(: to-v Dyn)))
   (define-simple-mutator (zero->non-zero-swap stx)
     #:pattern v:number
     #:when (zero? (syntax-e #'v))
     (with-syntax ([to-v 1])
       #'(: to-v Dyn)))
   #:expression-selector ignore-tuple-proj
   #:syntax-only
   #:streaming
   ))

(define program-mutation-deletion
  (build-mutation-engine
   #:mutators
   (define-simple-mutator (deletion stx)
     #:pattern ({~literal begin} x ... e )
     #'(begin x ...))
   #:syntax-only
   #:streaming))
(define program-mutation-arithmetic
  (build-mutation-engine
   #:mutators
   (define-id-mutator arithmetic-op-swap
     [+ #:<-> -]
     [/ #:-> *]
     [fl+ #:<-> fl-]
     [fl/ #:-> fl*])
   #:syntax-only
   #:streaming))

(define program-mutation-arithmetic-dynamic
  (build-mutation-engine
   #:mutators
   (define-simple-mutator (int-plus->fl-plus stx)
     #:pattern ({~datum +} expr ...)
     #'(: (fl+ (: expr Dyn) ... ) Dyn )
     )
   (define-simple-mutator (fl-plus->int-plus stx)
     #:pattern ({~datum fl+} expr ...)
     #'(: (+ (: expr Dyn) ...) Dyn))
   (define-simple-mutator (int-minus->fl-minus stx)
     #:pattern ({~datum -} expr ...)
     #'(: (fl- (: expr Dyn) ...) Dyn))
   (define-simple-mutator (fl-minus->int-minus stx)
     #:pattern ({~datum fl-} expr ...)
     #'(: (- (: expr Dyn) ...) Dyn))
   (define-simple-mutator (mul->fl-mul stx)
     #:pattern ({~datum *} expr ...)
     #'(: (fl* (: expr Dyn) ...) Dyn))
   (define-simple-mutator (fl-mul->mul stx)
     #:pattern ({~datum fl*} expr ...)
     #'(: (* (: expr Dyn) ...) Dyn))
   ;; I don't know why there is no integer division in grift ...
   ;; (define-simple-mutator (div->fl-div stx)
   ;;   #:pattern ({~datum /} expr ...)
   ;;   #'(: (fl/ (: expr Dyn) ...) Dyn))
   ;; (define-simple-mutator (fl-div->div stx)
   ;;   #:pattern ({~datum fl/} expr ...)
   ;;   #'(: (/ (: expr Dyn) ...) Dyn))
   #:syntax-only
   #:streaming))




(define program-mutation-condition
  (build-mutation-engine
   #:mutators
   (define-id-mutator condition-swap
     [and #:<-> or]
     [>= #:<-> <=]
     [< #:<-> >])
   #:syntax-only
  #:streaming))

(define program-mutation-negate-cond
  (build-mutation-engine
   #:mutators
   (define-simple-mutator (if-swap stx)
     #:pattern ({~literal if} cond t e)
     #'(if (not cond) t e))
   #:syntax-only
   #:streaming
   ))

(define program-mutation-force-cond
  (build-mutation-engine
   #:mutators
   (define-simple-mutator (if-swap stx)
     #:pattern ({~literal if} cond t e)
     #'(if (= 1 1) t e))
   #:syntax-only
   #:streaming
   ))


(define program-mutations
  (build-mutation-engine
   #:mutators
   (define-simple-mutator (if-swap stx)
     #:pattern ({~literal if} cond t e)
     #'(if cond e t))
   (define-constant-mutator (constant-swap v)
     [(? number?) #:-> (- v)])
   #:syntax-only
   #:streaming))


(define mutator-list (list (cons "constant-swap" program-mutation-constant-swap-dynamic)
                           (cons "position-swap" program-mutations-position-swap)
                           (cons "arithmetic" program-mutation-arithmetic-dynamic)
                           (cons "deletion" program-mutation-deletion)
                           (cons "condition" program-mutation-condition)
                           (cons "negate" program-mutation-negate-cond)
                           (cons "force" program-mutation-force-cond)))


(define (mutate-file-and-log-by-mutator filename mutation output-path)
  (unless (directory-exists? output-path)
    (make-directory output-path))
  (for ([mutators (mutation (read-program-from-name filename))]
        [i (in-naturals)])
    (define mutant-name (format "mutant~v" i))
    (define output-path/mutant (build-path output-path mutant-name))
    (unless (directory-exists? output-path/mutant)
      (make-directory output-path/mutant))
    (define static-port (open-output-file (build-path output-path/mutant (format "~a-static.grift" mutant-name)) #:exists 'replace))
    (define dynamic-port (open-output-file (build-path output-path/mutant (format "~a-dynamic.grift" mutant-name)) #:exists 'replace))
    
    ;; (define mutant-name (format "mutant~v.grift" i))
    ;; (define output-filepath (build-path output-path mutant-name))
    ;; (define out-port (open-output-file output-filepath #:exists 'replace))
    (fprintf static-port "~a"  (syntax->string mutators))
    (fprintf dynamic-port "~a" (syntax->string (total-dynamizer mutators)))
    (close-output-port static-port)
    (close-output-port dynamic-port)))

(define (for-the-file in-path file-name out-path)
  (define folder (build-path out-path file-name))
  (unless (directory-exists? folder)
    (make-directory folder))
  (map (lambda (name-mutation)
         (match name-mutation
           [(cons name mutation)
            (define new-folder (build-path folder name))
            (define input-file (build-path in-path  file-name ))
            (mutate-file-and-log-by-mutator (path-add-extension input-file ".grift") mutation new-folder)
            ])) mutator-list))

(define (main-work in-path out-path)
  (for-each (lambda (x)
              (define relative-file (file-name-from-path x))
              (define file-without-extension (path-replace-extension relative-file #""))
              (display (format "mutate for file: ~a from ~a to ~a\n" file-without-extension in-path out-path))
              (for-the-file in-path file-without-extension out-path))
            (glob (build-path in-path "*.grift") )))
;; (main-work "/home/sch/code/Grift/src/static_blame/test/benchmark/src/" "/home/sch/grift-exp")


