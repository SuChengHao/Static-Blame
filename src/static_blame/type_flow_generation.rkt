#lang racket
(require
 "../language/forms.rkt"
 "../grift/type-check.rkt"
 "refinement.rkt"
 "type_flow.rkt"
 "../logging.rkt")

(module+ test
  (require rackunit))

;; given a solver, a flow generation process will take a program and
;; adds dummy type flow and blame type flow into the solver.

;; the code below is based on the standard cast insertation process in grift/insert-casts.rkt

(provide
 generate-type-flows)

(define Env/c hash?)
(define (env-extend* e x* v*)
  (for/fold ([e e]) ([x (in-list x*)] [v (in-list v*)])
    (hash-set e x v)))



(define-syntax-rule (th o ...)
  (lambda () o ...))

(define-syntax mk-label
  (syntax-rules ()
    [(_ pos src)
     (lambda ()
       (format "Implicit cast in ~a on expression at ~a\n"
               pos (srcloc->string src)))]
    [(_ pos sup-src sub-src)
     (mk-label (format "~a at ~a\n" pos (srcloc->string sup-src))
               sub-src)]))
;; I swear that I wanted to define the process on the cast calculus.
;; However, the cast calculus does not hold srcloc anymore.

;; An awkward situation: we must maintain the environment by ourself.
;; We may assume that every definition has a unique type.

(define (generate-type-flows prgm)
  (define who 'generate-type-flow)
  (match-define (Prog (list name unique type) tl*) prgm)
  ;; the first step: gathering point for each identifier.
  (define env (hash))
  ;;(define toplevel (mk-empty-clabel (srcloc->ppoint)))
  (define-values (x* ltype*)
    (for/lists (x* ltype*)
               ([tl (in-list  (filter Define? tl*))])
      (match tl
        [(Define _ id t2 (Ann _ (cons src t1)))
         (define toplevel (mk-empty-clabel (srcloc->ppoint src)))
         (define clabel (refine-a-clabel toplevel (Idref id)))
         (define ltype (mk-ltype clabel t2))
         (values id ltype)])))
  (define toplevel/extended (env-extend* env x* ltype*))
  (for/list ([tl (in-list tl*)])
    (match tl
      [(Define r? id t2 (and (Ann _ (cons s t1)) (app (gtf-expr toplevel/extended) ltype-e)))
       (define lbl (mk-label "Define" s))
       (cast-or-not lbl ltype-e (hash-ref toplevel/extended id))]
      [(Observe e t) ((gtf-expr toplevel/extended) e)])))

;; note that we don't need srcloc or expression anymore
(define (cast-or-not l-th lt1 lt2)
  (define who 'type-flow-generation/cast-or-not)
  (match-define (Ltype _ t1) lt1)
  (match-define (Ltype _ t2) lt2)
  (cond
    [(subtype-of? t1 t2)
     (add-dummy-flow lt1 lt2)]
    [else
     (add-blabel-flow lt1 lt2 (l-th))]))

  
(define ((gtf-expr env [refinement #f]) exp^ )
  (define (gtf-insert-cast body out-type lbl)
          (match body
            [(Ann _ (cons src _))
             (define inner-ltype ((gtf-expr env (Castref)) body))
             (define out-clabel (mk-empty-clabel (srcloc->ppoint src)))
             (define out-ltype (mk-ltype out-clabel out-type))
             (cast-or-not lbl inner-ltype out-ltype)
             out-ltype]))
  (match-define (Ann exp (cons src (app unfold-possible-mu type))) exp^)
  (define out-ppoint (srcloc->ppoint src))
  (define out-clabel
    (if refinement
        (refine-a-clabel
         (mk-empty-clabel out-ppoint) refinement)
        (mk-empty-clabel out-ppoint)))
  
  (match exp
    [(Lambda fml* (and (Ann _ (cons body-src body-type))
                       body))
     (define fn-range (or (and (Fn? type) (Fn-ret type))
                          (error 'gtf-expr "function type recieve non-function type")))
     (define ret-label (refine-a-clabel out-clabel (Franref)))
     (define ret-ltype (mk-ltype ret-label fn-range))
     ;; first, collect bindings for arguments
     (define-values (x* ltype*) 
       (for/lists (x* ltype*)
                  ([fml (in-list fml*)]
                   [n   (in-naturals)])
         (values (Fml-identifier fml) (mk-ltype (refine-a-clabel out-clabel (Fdomref n)) (Fml-type fml)))))
     (define body-ltype ((gtf-expr (env-extend* env x* ltype*)) body))
     (let ([lbl-th (mk-label "lambda" body-src)])
       (cast-or-not lbl-th body-ltype ret-ltype))
     (mk-ltype out-clabel type)]
    [(Let bnd* (and (Ann _ (cons src _)) body))
     (define env/extended (gtf-bnd* bnd* env out-clabel))
     (define let-ltype (mk-ltype out-clabel type))
     (cast-or-not (mk-label "let" src)  ((gtf-expr env/extended) body) let-ltype)
     let-ltype]
    [(Letrec bnd* (and (Ann _ (cons src _)) body))
     (define env/extended (gtf-bnd* bnd* env out-clabel))
     (define let-ltype (mk-ltype out-clabel type))
     (cast-or-not (mk-label "letrec" src)  ((gtf-expr env/extended) body) let-ltype)
     let-ltype]
    [(App rator rand*)
     ;;(display "Sorry, I'm in\n")
     (match-define (Ann _ (cons rator-src (app unfold-possible-mu rator-type))) rator)
     (define app-ltype (mk-ltype out-clabel type))
     (match rator-type
       [(Dyn)
        ;; rator need cast to a dynamic function type
        ;; each rand has a dummy cast.
        (define rator-inner-ltype ((gtf-expr env (Castref)) rator))
        (define rator-clabel (mk-empty-clabel (srcloc->ppoint rator-src)))
        (define rand-type*
          (for/list ([rand rand*]
                     [index (in-naturals)])
            (match-let ([(Ann _ (cons rand-src rand-type)) rand])
              (define rand-ltype ((gtf-expr env) rand))
              (define rand-type (Ltype-gtype rand-ltype))
              (define arg-ltype (mk-ltype
                                 (refine-a-clabel rator-clabel (Fdomref index))
                                 rand-type ) )
              (add-dummy-flow rand-ltype arg-ltype)
              rand-type))) ;; there is no cast to arg-type
        (define needed-rator-type (Fn (length rand-type*) rand-type* DYN-TYPE))
        ;; the original blame label generating sucks
        ;; 
        ;; (define lbl (mk-label "Application" src rator-src))
        (define lbl (mk-label "Application" src))
        (define rator-out-lype (mk-ltype rator-clabel needed-rator-type))
        (cast-or-not lbl rator-inner-ltype rator-out-lype)

        ;;missing flow, from the application to the ret
        (define rator-ret-ltype (mk-ltype (refine-a-clabel rator-clabel (Franref)) DYN-TYPE))
        (add-dummy-flow rator-ret-ltype  app-ltype)
        ;; (display ("Add dummy flow from ~a to ~a\n" rator-inner-ltype rator-out-lype ))
        ]
       [(Fn n dom ret-type)
        
        (define rator-ltype ((gtf-expr env) rator))
        ;;(display (format "rator-ltype is : ~a \n" rator-ltype))
        (define rator-clabel (Ltype-clabel rator-ltype))
        (for/list ([rand rand*]
                   [index (in-naturals)]
                   [dom-index dom])
          (match-let ([(Ann _ (cons rand-src rand-type)) rand])
            (define rand-ltype ((gtf-expr env (Castref)) rand))
            (define lbl (mk-label "application" src rand-src))
            (define arg-ltype (mk-ltype (refine-a-clabel rator-clabel (Fdomref index)) dom-index))
            ;; (display (format "add flow from ~a to ~a\n" rand-ltype arg-ltype))
            (cast-or-not lbl rand-ltype arg-ltype)))
        
        ;; add dummy type-flow,
        (define rator-ret-ltype (mk-ltype (refine-a-clabel rator-clabel (Franref)) ret-type))
        (add-dummy-flow rator-ret-ltype app-ltype)])
     app-ltype]
    [(Op (list prim rand-ty*) rand*) ;; operator is a black-box, however, a constant does not hold a srcloc, either.
     (define op-clabel (refine-a-clabel out-clabel (Constref prim)))
     (for/list ([rand rand*]
                [index (in-naturals)]
                [dom-type rand-ty*])
       (match-let ([(Ann _ (cons rand-src rand-type)) rand])
            (define rand-ltype ((gtf-expr env (Castref)) rand))
            (define lbl (mk-label "application" src rand-src))
            (define arg-ltype (mk-ltype (refine-a-clabel op-clabel (Fdomref index)) dom-type))
            (cast-or-not lbl rand-ltype arg-ltype)))
     (define this-ltype (mk-ltype out-clabel type))
     this-ltype]
    [(Ascribe exp t1 lbl?)
     (define lbl (if lbl? (th lbl?) (mk-label "ascription" src)))
     (define asc-ltype (mk-ltype out-clabel type))
     (define inner-ltype ((gtf-expr env) exp))
     (cast-or-not lbl inner-ltype asc-ltype)
     asc-ltype]
    [(If (and (Ann _ (cons tst-src tst-ty)) (app (gtf-expr env) tst-ltype))
         (and (Ann _ (cons csq-src csq-ty)) (app (gtf-expr env) csq-ltype))
         (and (Ann _ (cons alt-src alt-ty)) (app (gtf-expr env) alt-ltype)))
     (define if-ltype (mk-ltype out-clabel type))
     (cast-or-not (mk-label "if" tst-src) tst-ltype (mk-ltype (refine-a-clabel out-clabel (Constref "if condition")) BOOL-TYPE))
     (cast-or-not (mk-label "if" csq-src) csq-ltype if-ltype)
     (cast-or-not (mk-label "if" alt-src) alt-ltype if-ltype)
     if-ltype]
    [(Switch (and (Ann _ (cons es et)) (app (gtf-expr env) e-ltype))
             c*
             (and (Ann _ (cons ds dt)) (app (gtf-expr env) d-ltype)))
     (define target-clabel (refine-a-clabel out-clabel (Constref "switch target")))
     (define switch-ltype (mk-ltype out-clabel type))
     (cast-or-not (mk-label "switch" es) e-ltype (mk-ltype target-clabel INT-TYPE))
     (for/list ([c c*])
       (match-let ([(cons cl (and (Ann _ (cons cs ct))
                                  (app (gtf-expr env) c-ltype))) c])
         (cast-or-not (mk-label "switch" cs) c-ltype switch-ltype)))
     (cast-or-not (mk-label "switch" ds) d-ltype switch-ltype)
     switch-ltype]
    [(Var id)
     (hash-ref env id)]
    [(Quote lit)
     (mk-ltype out-clabel type)]
    [(Begin e* e)
     (map (gtf-expr env) e*)
     ((gtf-expr env) e)]
    [(Repeat index
             (and (Ann _ (cons s1 t1)) (app (gtf-expr env) e1-ltype))
             (and (Ann _ (cons s2 t2)) (app (gtf-expr env) e2-ltype))
             acc
             (and (Ann _ (cons s3 t3)) (app (gtf-expr env) e3-ltype))
             (and (Ann _ (cons s4 t4)) e4))
     ;; note that repeat will introduce an extra binding into e4
     (cast-or-not (mk-label "Repeat" s1) e1-ltype (mk-ltype (refine-a-clabel out-clabel (Constref "repeat from")) INT-TYPE))
     (cast-or-not (mk-label "Repeat" s2) e2-ltype (mk-ltype (refine-a-clabel out-clabel (Constref "repeat to")) INT-TYPE))
     ;; now create a binding
     (define repeat-ltype (mk-ltype out-clabel type))
     (define acc-ltype (mk-ltype (refine-a-clabel out-clabel (Idref acc)) type))
     (define index-ltype (mk-ltype (refine-a-clabel out-clabel (Idref index)) INT-TYPE))
     (add-dummy-flow acc-ltype repeat-ltype)
     (cast-or-not (mk-label "Repeat" s3) e3-ltype repeat-ltype)
     (let* ([env/extended (hash-set (hash-set env index index-ltype) acc acc-ltype)]
            [e4-ltype ((gtf-expr env/extended) e4)])
       (cast-or-not (mk-label "Repeat" s4) e4-ltype acc-ltype))
     repeat-ltype]
    [(Gbox e)
     (define inner-ltype ((gtf-expr env) e))
     (define inner-type (Ltype-gtype inner-ltype))
     (define dummy-ltype (mk-ltype (refine-a-clabel out-clabel (Boxref)) inner-type))
     (define gbox-ltype (mk-ltype out-clabel type))
     (add-dummy-flow inner-ltype dummy-ltype)
     gbox-ltype]
    [(Gunbox (and (Ann _ (cons e-src e-ty)) e-body))
     
     (define gunbox-ltype (mk-ltype out-clabel type))
     
     (cond
       [(Dyn? e-ty)
        (define inner-ltype ((gtf-expr env (Castref)) e-body))
        (define box-clabel (mk-empty-clabel (srcloc->ppoint e-src)))
        (define box-ltype  (mk-ltype box-clabel PBOX-DYN-TYPE))
        
        (define lbl (mk-label "guarded unbox" e-src))
        (cast-or-not lbl inner-ltype box-ltype)
        ;; the inner ltype will cast to a dynamic box
        ;;
        (define box-ref-clabel (refine-a-clabel box-clabel (Boxref)))
        
        (add-dummy-flow (mk-ltype box-ref-clabel DYN-TYPE) gunbox-ltype)
        ]
       [else
        (define inner-ltype ((gtf-expr env) e-body))
        (define inner-clabel (Ltype-clabel inner-ltype))
        (define inner-box-clabel (refine-a-clabel inner-clabel (Boxref)))
        (add-dummy-flow (mk-ltype inner-box-clabel type) gunbox-ltype)
        ])
     gunbox-ltype]
    [(Gbox-set! (and (Ann _ (cons e1-src (app unfold-possible-mu e1-ty))) e1-body)
                (and (Ann _ (cons e2-src e2-ty)) e2-body))
     (define lbl1 (mk-label "guarded box-set!" e1-src))
     (define lbl2 (mk-label "guarded box-set!" e2-src))
     (define gbox-set!-ltype (mk-ltype out-clabel type))
     (cond
       [(Dyn? e1-ty)
        (define e1-inner-ltype ((gtf-expr env (Castref)) e1-body))
        (define e2-inner-ltype ((gtf-expr env (Castref)) e2-body))

        (define e2-clabel (mk-empty-clabel (srcloc->ppoint e2-src)))
        (define e2-ltype (mk-ltype e2-clabel DYN-TYPE))
        (cast-or-not lbl2 e2-inner-ltype e2-ltype)

        (define e1-clabel (mk-empty-clabel (srcloc->ppoint e1-src)))
        (define e1-ltype (mk-ltype e1-clabel PBOX-DYN-TYPE))
        (cast-or-not lbl1 e1-inner-ltype e1-ltype)

        (add-dummy-flow e2-ltype (box-ltype->content-ltype e1-ltype))]
       [else
        ;; cast-or-not?
        (define e1-ltype ((gtf-expr env) e1-body))
        (define e2-inner-ltype ((gtf-expr env (Castref)) e2-body))
        (define e2-clabel (mk-empty-clabel (srcloc->ppoint e2-src)))
        (define e2-ltype (mk-ltype e2-clabel (GRef-arg e1-ty)))
        (cast-or-not lbl2 e2-inner-ltype e2-ltype)

        ;; more over, e2-ltype may flows into the content of e1
        (define content-ltype (box-ltype->content-ltype e1-ltype))
        (add-dummy-flow e2-ltype content-ltype)])
     gbox-set!-ltype]
    [(Gvector (and (Ann _ (cons size-src size-ty))
                    size-body)
              (app (gtf-expr env) e-ltype))
     (define gvector-ltype (mk-ltype out-clabel type))
     ;; size may be a dynamic value
     ;; e may flow into the content of the vector type
     (cond
       [(Dyn? size-ty)
        (define lbl (mk-label "gvector index" size-src))
        (define size-inner-ltype ((gtf-expr env (Castref)) size-body))
        (define size-clabel (mk-empty-clabel (srcloc->ppoint size-src)))
        
        (cast-or-not lbl size-inner-ltype (mk-ltype size-clabel INT-TYPE))]
       [else
        ((gtf-expr env) size-body)])
     (add-dummy-flow e-ltype (vector-ltype->content-ltype gvector-ltype))
     gvector-ltype]
    [(Gvector-ref (and (Ann _ (cons e-src e-ty))  e-body)
                  (and (Ann _ (cons i-src i-ty))  i-body))
     (define gvector-ref-ltype (mk-ltype out-clabel type))
     (cond
       [(Dyn? i-ty)
        (gtf-insert-cast i-body INT-TYPE (mk-label "gvector-ref index" i-src))]
       [else
        ((gtf-expr env) i-body)])
     ;; the content flows out
     (cond
       [(Dyn? e-ty)
        (define e-ltype (gtf-insert-cast e-body (GVect DYN-TYPE)  (mk-label "gvector-ref" e-src)))
        ;;then e-ltype may flows out
        (add-dummy-flow (vector-ltype->content-ltype e-ltype) gvector-ref-ltype)]
       [else
        (define e-ltype ((gtf-expr env) e-body))
        (add-dummy-flow (vector-ltype->content-ltype e-ltype) gvector-ref-ltype)])
     gvector-ref-ltype]
    [(Gvector-set! (and (Ann _ (cons e1-src (app unfold-possible-mu e1-ty)))
                         e1-body)
                   (and (Ann _ (cons i-src i-ty)) i-body)
                   (and (Ann _ (cons e2-src e2-ty)) e2-body))
     ;; i e1 or e2 can be dynamic, and e2-ltype may flows into e1's content
     (define gvector-set!-ltype (mk-ltype out-clabel type))
     (define lbl1 (mk-label "gvector-set!" e1-src))
     (define lbl2 (mk-label "gvector-set!" e2-src))
     (cond [(Dyn? i-ty)
            (define lbl (mk-label "gvector-ref index" i-src))
            (gtf-insert-cast i-body INT-TYPE lbl)]
           [else
            ((gtf-expr env) i-body)])
     (cond [(Dyn? e1-ty)
            ;; e1 need cast to GVect Dyn
            ;; e2 need cast to DYN
            (define e1-ltype (gtf-insert-cast e1-body (GVect DYN-TYPE) lbl1))
            (define e2-ltype (gtf-insert-cast e2-body DYN-TYPE lbl2))
            ;; and e2 may flows into the content of e1
            (add-dummy-flow e2-ltype (vector-ltype->content-ltype e1-ltype))]
           [else
            ;; e2 need cast to e1's content type
            (define e2-ltype (gtf-insert-cast e2-body (GVect-arg e1-ty) lbl2))
            (define e1-ltype ((gtf-expr env) e1-body))
            (add-dummy-flow e2-ltype (vector-ltype->content-ltype e1-ltype))])
     gvector-set!-ltype]
    [(Gvector-length (and (Ann _ (cons e-src e-ty)) e-body))
     (define gvector-length-ltype (mk-ltype out-clabel type))
     (cond
       [(Dyn? e-ty) ;; the e-body may translated into a vector
        (define l-th (mk-label "gvector-length" e-src))
        (define e-inner-ltype ((gtf-expr env (Castref)) e-body))
        (define e-clabel (mk-empty-clabel (srcloc->ppoint e-src)))
        (define e-ltype (mk-ltype e-clabel PVEC-DYN-TYPE))
        (cast-or-not l-th e-inner-ltype e-ltype)]
       [else
        ((gtf-expr env) e-body)])
     gvector-length-ltype]
    [(Create-tuple e*)
     (define create-tuple-ltype (mk-ltype out-clabel type))
     ;; for each ltype, it may flows into a dummy position of create-tuple-ltype
     (for/list ([e e*]
                [i (in-naturals)])
       (define pos-ltype ((gtf-expr env) e))
       (define pos-type (Ltype-gtype pos-ltype))
       (define pos-dummy-ltype (mk-ltype (refine-a-clabel out-clabel (Tupref i)) pos-type))
       (add-dummy-flow pos-ltype pos-dummy-ltype))
     create-tuple-ltype]
    [(Tuple-proj (and (Ann _ (cons e-src e-ty)) e-body) i)
     (define tuple-proj-ltype (mk-ltype out-clabel type))
     (cond
       [(Dyn? e-ty)
        (define l-th (mk-label "tuple-proj" e-src))
        ;; tuple itself will be translated into a dynamic tuple
        (define e-inner-ltype ((gtf-expr env (Castref)) e-body))
        (define n (add1 i))
        (define e-out-type (STuple n (make-list n DYN-TYPE)))
        (define e-out-clabel (mk-empty-clabel (srcloc->ppoint e-src)))
        (define e-ltype (mk-ltype e-out-clabel e-out-type))

        (cast-or-not l-th e-inner-ltype e-ltype)
        ;; more over, the i-th position of e-ltype will flow out
        (add-dummy-flow (tuple-ltype->content-ltype e-ltype i) tuple-proj-ltype)]
       [else
        (define e-ltype ((gtf-expr env) e-body))
        (add-dummy-flow (tuple-ltype->content-ltype e-ltype i) tuple-proj-ltype)])
     tuple-proj-ltype]
    [other (error 'type_flow_generation "unmatched ~a" other)]))

(define (extend-env/bnd* e bnd* clabel)
  (define-values (x* ltype*)
    (for/lists (id* cl*)
               ([bnd bnd*])
      (match-define (Bnd i t _) bnd)
      (values i (mk-ltype (refine-a-clabel clabel (Idref i)) t))))
  (env-extend* e x* ltype*))

(define (gtf-bnd* bnd* env clabel)
  (define env/extended (extend-env/bnd* env bnd* clabel))
  (for/list ([bnd bnd*])
    (match-define (Bnd i t (and rhs (Ann _ (cons rhs-src rhs-type))) ) bnd)
    (define lbl (mk-label "binding" rhs-src))
    (define rhs-ltype ((gtf-expr env/extended) rhs))
    (cast-or-not lbl rhs-ltype (hash-ref env/extended i)))
  env/extended)

(define (gtf-operand app-src env)
  (lambda (rand arg-ltype)
    (match-let ([(Ann _ (cons rand-src rand-type)) rand])
      (define rand-ltype ((gtf-expr env) rand))
      (define lbl (mk-label "application" app-src rand-src))
      (cast-or-not lbl rand-ltype arg-ltype))))

(module+ test
  (require "../grift/syntax-to-grift0.rkt"
           "../grift/type-check.rkt")
  (require (rename-in "../grift/read.rkt"
                      (read grift-read)))

  (define (prg->messages checked-prg)
                    (define solver (make-constraint-solver))
                    (parameterize ([current-solver solver])
                      (generate-type-flows checked-prg))
    (map Tyflow-blame-label (filter (lambda (x) (not (dummy? x))) (export-type-flow solver))))
  
  (define (list-grift-files-in path)
       (for/list ([f (in-directory path)] #:when (path-has-extension? f #".grift")) f))
  (define iteration-tests
    (test-suite
     "pass the core test-files"
     (let ([grift-files (list-grift-files-in "../../tests/suite/core")])
       (for/list ([p (in-list grift-files)])
         (test-case
             (format "test type flow generation for ~a" (path->string p))
           (parameterize ([current-solver (make-constraint-solver)])
             (check-not-exn (lambda () (generate-type-flows (type-check (syntax->grift0 (grift-read p))))))
             (for-each
              (lambda (elt)
                (check-pred legal-type-flow? elt))
              (export-type-flow (current-solver)))))))
     ))
  (require rackunit/text-ui)
  (run-tests iteration-tests))
;; debug script
;; (define (cast-stored->message c)
;;                     (match-define (cons _ e)  c)
;;                     (match e
;;                       [ (Cast _ (Twosome _ _ message)) message]
;;                       [(Dyn-GRef-Ref _ message) message]
;;                       [(Dyn-GRef-Set! _ _ _ message) message]
;;                       [(Dyn-GVector-Ref _ _ m) m]
;;                       [(Dyn-GVector-Set! _ _ _ _ m) m]
;;                       [(Dyn-GVector-Len _ (Quote m)) m]
;;                       [(Dyn-Tuple-Proj _ _ (Quote m)) m]
;;                       [(Dyn-Fn-App _ _ _ m) m]))
;; (define stored-messages (map cast-stored->message (unbox casts-inserted)))




