#lang racket/base
#|
Much of content is duplication of ../grift/type-check.rkt and ../grift/insert-casts.rkt
Since type flow analysis is a static simulation of runtime casts.

|#
(require
 racket/contract
 racket/contract/option
 racket/function
 racket/list
 racket/match
 racket/set
 "./refinement.rkt"
 "./type_flow.rkt"
 "../grift/type-check.rkt"
 "../configuration.rkt"
 "../language/forms.rkt"
 "../errors.rkt"
 "../logging.rkt")

;; shame copying codes, but I want to minimize the modification
;; to the original source code.

#|--------------------------------
The basic data structure, labeled type environment
--------------------------------|#

;; note that the environment maps
;; identifier to labeled types
(define Env/c hash?)

(define (env-extend* e x* v*) 
  (for/fold ([e e]) ([x (in-list x*)] [v (in-list v*)])
    (hash-set e x v)))


#|----------------
Type utilities
----------------|#
;; unfold-possible-mu :: takes a type and converts it to a equivalent type
;; where the outermost type is a concrete type constructor (like ->, Tuple, etc.) as
;; opposed to logical (like Rec).
;; NOTE: this should only be called on types that have been converted to normal form. 
(define/contract (unfold-possible-mu t)
  (option/c (-> type? type?) #:with-contract #t)
  (let rec ([t t])
    (match t
      [(Mu s) (unfold-possible-mu (grift-type-instantiate s t))]
      [t t])))


;; Checks to make sure Mu types obey the productivity check
;; Return the a version of type where superflouos mu are droped
;; and unrolled Mus are rerolled.
;(: validate-type : srcloc Grift-Type -> Grift-Type)
(define (validate-type src t)
  (define who 'validate-type)
  (debug who src t)

  (define/contract eqs
    (option/c (hash/c type? type?))
    (make-hash '()))

  (define/contract (vt pending)
    (option/c (-> (set/c Uid?) (-> type? type?)) #:with-contract #t)
    (define (rec t)
      (cond
        [(Mu? t)
         (match-define (Mu s0) t)
         (define rec-uvar (next-uid! 'rec-fvar))
         (define rec-fvar (FVar rec-uvar))
         (define t0 (grift-type-instantiate s0 rec-fvar))
         (define t1 ((vt (set-add pending rec-uvar)) t0))
         ;; If the inner type is a Mu then we merge the
         ;; Mu we are creating with the inner one.
         ;; This is because both Mu's variables point to
         ;; the same location in the type.
         (define t2
           (cond
             [(Mu? t1)
              (match-define (Mu s1) t1)
              (grift-type-instantiate s1 rec-fvar)]
             [else t1]))
         (define-values (s1 used?)
           (grift-type-abstract/used? rec-uvar t2))
         ;; if rec-uvar isn't abstracted then t1 doesn't contain
         ;; any occurences of it and we don't have to bind it.
         (define ret (if used? (Mu s1) t2))
         (hash-set! eqs (grift-type-instantiate s1 ret) ret)
         ret]
        [(FVar? t)
         (match-define (FVar u) t)
         (when (set-member? pending u)
           (error 'non-productive-variable
                  "recursive variable appears in non-productive position ~a"
                  src))
         t]
        [else
         ;; If the type constructor is for actual data then the mu is productive
         ;; and we can clear the pending recursive variables.
         (define vt/pending
           (if (structural-type? t) (vt (set)) rec))
         (define r (grift-type-map t vt/pending))
         (or (hash-ref eqs r #f) r)]))
    rec)
  (debug who src type ((vt (set)) t)))


;; Assumed to not validate types
;; (: synthesize-recursive-binding-type :
;;    (Option Grift-Type) G0-Ann-Expr -> (Values Grift-Type G0-Ann-Expr))
(define (synthesize-recursive-binding-type id-type? rhs)
  ;; Normally a binding construct assumes that the lack of type
  ;; annotation means to infer the type of the rhs, but recursive
  ;; binding constructs cannot be trivially infered.
  ;; We have arbitrarily made the following decisions.
  ;; (following inline comments)
  (cond
    ;; If the binding specifies a type always believe it.
    [id-type? (values id-type? rhs)]
    [else
     ;; If the user doesn't specify a binding type
     ;; use the type of the lambda.
     (match rhs
       [(Ann (Lambda (and f* (list (Fml _ _) ...)) (list b return-type?))
             s)
        (define t* (map Fml-type f*))
        (cond
          [return-type?
           (define id-type (Fn (length t*) t* return-type?))
           (values id-type rhs)]
          [else
           ;; Function without return-type annotatin gets dyn return.
           (define id-type (Fn (length t*) t* DYN-TYPE))
           (define rhs     (Ann (Lambda f* (list b DYN-TYPE)) s))
           (values id-type rhs)])]
       ;; If it isn't a function we use dynamic as the type
       [rhs (values DYN-TYPE rhs)])]))


(define (flow-analysis prgm)
  (define who 'flow-analysis)
  (match-define (Prog (list n c) top-level-form*) prgm)
  (define solver (make-constraint-solver))
  
  (define uc (make-unique-counter c))
  (define new-top-level*
    (parameterize ([current-unique-counter uc]
                   [current-solver solver])
      (flow-analyse-top* top-level-form* (hash))))
  (debug who
         (Prog (list n (unique-counter-next! uc) (INT-TYPE)) new-top-level*)))




(define (flow-analyse-top* t* env)
  (match t*
    [(cons (Ann2 (Define #f i t? e) s) t*-rest)
     (define-values (new-e e-type/labeled) (flow-analyse-expr e env))
     (define e-type (erase-type-label e-type/labeled))

     (debug t? e-type)
     (define vt? (and t? (validate-type s t?)))
     (define clabel (make-empty-context-label s))
     
     (define i-type/labeled
       (cond
         [(not vt?) e-type/labeled]
         [(consistent? vt? e-type) (refine-a-type clabel vt?)]
         [else (error 'static-type-error "~a: inconsistent typed ~a and ~a"
                      (srcloc->string s) vt? e-type)]))
     (if vt? (add-type-flow-to-a-solver (make-type-flow e-type/labeled i-type/labeled s  )  ) )
     (cons (Define #f i i-type/labeled new-e)
           (tc-top* t*-rest (hash-set env i i-type/labeled)))]
    [(and t* (cons (Ann2 (Define #t _ _ _) _) _))
     (define ((flow-analysis-rec-define env) d)
       (match-define (Ann2 (Define _ id valid-id-type/labeled expr) src) d)
       (define-values (new-expr expr-type/labeled) (flow-analyse-expr expr env))
       (debug valid-id-type/labeled expr-type/labeled)
       (define valid-id-type (erase-type-label valid-id-type/labeled))
       (define expr-type (erase-type-label expr-type/labeled))
       (unless (consistent? valid-id-type expr-type)
         (error 'static-type-error "~a: inconsistent typed ~a and ~a"
                (srcloc->string src) valid-id-type expr-type ))
       ;; (define valid-id-type/labeled (refine-a-type (make-empty-context-label s) valid-id-type))
       (add-type-flow-to-a-solver (make-type-flow expr-type/labeled valid-id-type/labeled))
       (Define #t id valid-id-type/labeled new-expr))
     (define (flow-analysis-rec-define* t* env i*)
       (match t*
         [(cons (Ann2 (Define #t id t? e) s) t*-rest)
          (define-values (ty new-e) (synthesize-recursive-binding-type t? e))
          (define valid-ty (validate-type s ty))
         
          (define valid-ty/labeled (refine-a-type (make-empty-context-label s) valid-ty))
          (define i (Ann2 (Define #t id valid-ty/labeled new-e) s))
          (flow-analysis-rec-define* t*-rest (hash-set env id valid-ty/labeled) (cons i i*))]
         [t*-rest
          (define c* (map (flow-analysis-rec-define env) i*))
          (define c*-rest (flow-analyse-top* t*-rest env))
          (foldl cons c*-rest c*)]))
     (flow-analysis-rec-define* t* env '())]
    [(cons (Ann2 (Observe expr #f) src) t*-rest)
     (define-values (new-expr type/labeled) (flow-analyse-expr expr env))
     (cons (Observe new-expr type/labeled) (flow-analyse-top* t*-rest env))]
    [(list) '()]
    [other (error 'flow-analyse-top* "unhandled case: ~a" other)]))

;;; Procedures that are used to throw errors
;; The error that occurs when a variable is not found. It is an internal
;; error because it is a syntax error to have an unbound variable.
(define-syntax-rule (lookup-failed src id)
  (lambda () (error 'variable-not-found "~a ~a" src id)))

#|
The type rules for core forms that have interesting type rules
|#

;; The type of a lambda that is annotated is the type of the annotation
;; as long as the annotation is consistent with the type of the
;; body

;; TODO, try to generate labeled type for lambda type rule
;; (: lambda-type-rule (-> Src Grift-Type* Grift-Type Grift-Type?
;; 			(Fn Index Grift-Type* Grift-Type)))
(define (lambda-type-rule src clabel ty-param/labeled* t-body/labeled return-ann?)
  (define t-body (erase-type-label t-body/labeled))
  (define arity (length ty-param/labeled*) )
  (cond
    [(not return-ann?) (Fn/labeled clabel arity ty-param/labeled* t-body/labeled)]
    [(consistent? t-body return-ann?)
     ;; here, we need to add a new constraint to the solver
     (define return-ann/labeled (refine-function-range-type clabel return-ann?))
     (define to-type/labeled (Fn/labeled clabel arity ty-param/labeled* return-ann/labeled))
     (add-type-flow-to-a-solver (make-type-flow t-body/labeled return-ann/labeled src) (current-solver))
     to-type]
    [else
     (error
      '|static type error|
      (string-append
       "Function return annotation inconsistent with the infered "
       "return type of the function.\n"
       "    location: " (or (srcloc->string src) "unkown location") "\n"
       "    annotated type: " (type->string return-ann?) "\n"
       "    inferred type: " (type->string t-body) "\n"))]))

;; now comes to hard part:
;; when a type flows into a part of a mu-type, what exactly it flows into?
;; 
(define (application-type-rule t-rator t-rand* src)
  )

(define (tuple-type-rule clabel t*)
  (STuple/labeled clabel (length t*) t*))

(define (tuple-proj-type-rule ty i)
  (define proj-arity (add1 i))
  (define proj-template (STuple proj-arity (make-list proj-arity DYN-TYPE))))

(define (flow-analyse-expr expr env)

  (debug 'flow-analyse-expr expr env)

  (define (env-extend/bnd b env)
    (match-let ([(Bnd i t _) b])
      (hash-set env i t)))

  (define ((letrec-synth-bnd-type/labeled src) bnd)
    (match-define (Bnd id id-type? rhs) bnd)
    (define-values (id-type new-rhs)
      (synthesize-recursive-binding-type id-type? rhs))
    ;; generate a labeled to each id
    (define clabel (make-binding-context-label src id))
    ;; then validate the type
    (define vt (validate-type src id-type))
    (define vt/labeled (refine-a-type clabel vt) )
    ;; (define id-type/labeled (refine-a-type clabel id-type))
    (Bnd id vt/labeled new-rhs))

  (define (map-letrec-synth-bnd-type/labeled src bnd*)
    (map (letrec-synth-bnd-type/labeled src) bnd*))

  ;; for/lists every for-clause will be executed, and then id will be bound
  (define (map-recur e*)
    (for/lists (e* t*) ([e e*])
      (flow-analyse-expr e env)))

  (define (map-switch-case2 f c)
    (define-values (r0 r1) (f (cdr c)))
    (values (cons (car c) r0) r1))

  (define (map-switch-case2* f a*)
    (for/lists (b* c*) ([a a*])
      (map-switch-case2 f a)))
  

  (define (recur-switch-case* c*)
    (map-switch-case2* recur c*))

  (define (recur e)
    ;; actually, we can use match-define here

    (match-define (Ann inner-expr src) e)
    ;; (define src (Ann-data e)))
    (define (validate t)
      (validate-type src t))
    (define (trace-type-error e)
      (printf "error while type-checking: ~a\n" (srcloc->string src)))
    (define clabel (make-empty-context-label src))
    
    (define-values (new-exp type/labeled)
      (with-handlers ([exn? trace-type-error])
        (match inner-expr
          ;; Lambda, fmls (list body type-annotation), where the type-annotation may
          ;; be a #f representing that no annotation provided in source code.
          ;; here is where we generate a context-label
          [(Lambda fml* (list b ret-type?))
           
           ;; And we need to get the annotation firstly
           (define i* (map Fml-identifier fml*))
           (define t* (map Fml-type fml*))

           (define vt* (map validate t*))
           (define v-ret-type? (and ret-type? (validate ret-type?)))
           ;; Due to design, we need to generated labeled type here.
           ;; Major change starts from here
           (define vt/labeled* (refine-function-domain-type clabel vt*))
           (define-values (body type-of-body/labeled) (flow-analyse-expr b (env-extend* env i* vt/labeled*)))
           (values (Lambda f* body)
                   (lambda-type-rule src clabel vt/labeled* type-of-body/labeled v-ret-type?))]
          [(Letrec (app (map-letrec-synth-bnd-type src) bnd*) body)
           ;; get a type for each binding, by query annotation and function annotation,
           ;; if neither is provided, then a dynamic will be generated.
           ;; here, the original code has a bug: before type-checking the body one needs 
           ;; to validate binding types at first.
           ;; this is a hidden bug since the logic of Letrec and let are slightly different
           (define recursive-env (foldr env-extend/bnd env bnd*))
           (define (rec/env e) (flow-analyse-expr e recursive-env))
           (define new-bnd* (map (flow-analyse-binding/validated src rec/env) bnd*))
           (define-values (new-body type/labeled)
             (rec/env body))
           (values (Letrec new-bnd* new-body) type/labeled)]
          [(Let bnd* body)
           ;; for every binding, validate it's type
           ;; generate label for every binding.
           (define new-bnd* (map (flow-analyse-binding src recur) bnd*))
           (define env0 (foldl env-extend/bnd env bnd*))
           (define-values (new-body type/labeled) (flow-analyse-expr body env0))
           (values (Let new-bnd* new-body) type/labeled)]
          [(App (app recur rator ty-rator)
                (app map-recur rand* ty-rand*))
           (values (App rator rand*)
                   (application-type-rule ty-rator ty-rand* src))]
          [(Op)]
          [(Ascribe)]
          [If]
          [Switch]
          [(Var)]
          [(Quote)]
          [(Repeat)]
          [])))
    
  
  
    ))

;; flow analyse binding, each type need to be validate at first.
(define ((flow-analyse-binding/validated src analyse-process) bnd)
  (match-define (Bnd id t0/labeled rhs) bnd)
  ;; analyse rhs first
  (define-values (new-rhs rhs-type/labeled) (analyse-process rhs))
  ;; then try to analyse the bound value, note that t0/labeled is validated first.
  (define t1/labeled (let-binding-type-rule/validated t0/labeled rhs-type/labeled id src) )
  (Bnd id t1/labeled new-rhs))

(define ((flow-analyse-binding src analyse-process) bnd)
  (match-define (Bnd id t0 rhs) bnd)
  (define-values (new-rhs rhs-type/labeled) (analyse-process rhs))
  (define clabel (make-binding-context-label src id))
  (define t1/labeled (let-binding-type-rule clabel (and t0 (validate-type src t0)) rhs-type/labeled id src))
  (Bnd id t1/labeled new-rhs))


(define (let-binding-type-rule clabel vt? rhs-type/labeled id src)
  (define rhs-type (erase-type-label rhs-type/labeled))
  (cond
    [(not vt?) rhs-type/labeled]
    [(consistent? vt? rhs-type)
     (define vt/labeled
       (refine-a-type clabel vt?))
     (add-type-flow-to-a-solver
      (make-type-flow rhs-type/labeled vt/labeled))
     vt/labeled]
    [else
     (error 'binding-inconsistent "~a ~a ~a ~a" src id vt? rhs-type)]))

(define (let-binding-type-rule/validated ann/labeled rhs-type/labeled id src)
  (define ann-type (erase-type-label ann/labeled) )
  (define rhs-type (erase-type-label rhs-type/labeled))
  (cond
    [(consistent? ann-type rhs-type)
      (add-type-flow-to-a-solver (make-type-flow rhs-type/labeled ann/labeled src) (current-solver))
     ann/labeled
     ]
    [else (error 'binding-inconsistent "~a ~a ~a ~a" src id ann-type rhs-type)]))
