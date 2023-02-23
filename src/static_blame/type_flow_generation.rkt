#lang racket
(require
 "../language/forms.rkt"
 "refinement.rkt"
 "type_flow.rkt")

(module+ test
  (require rackunit))

;; given a solver, a flow generation process will take a program and
;; adds dummy type flow and blame type flow into the solver.

;; the code below is based on the standard cast insertation process in grift/insert-casts.rkt

(provide
 generate-type-flow)

(define Env/c hash?)
(define (env-extend* e x* v*)
  (for/fold ([e e]) ([x (in-list x*)] [v (in-list v*)])
    (hash-set e x v)))

;; is `t1` a subtype of `t2`?
(define (subtype-of? t1 t2)
  (define (type=? a t1 t2)
    ;; I think this is a more optimized version of
    ;; (and (rec/a a t1 t2) (rec/a a t2 t1) a)
    ;; (rec/a (rec/a a t1 t2) t2 t1))
    ;; no, I don't think it is correct.
    (and (rec/a a t1 t2) (rec/a a t2 t1) a)
  ;; substitute `t` for variables bound to this Mu to get
  ;; rid of this Mu scope.
  (define (rec/a-fold a t1 t2)
    (cond
      [(not a) #f]
      [else
       (match* (t1 t2)
         [('() _) a]
         [(_ '()) a]
         [((cons a1 d1) (cons a2 d2))
          (rec/a-fold (rec/a a1 a2 a) d1 d2)]
         [(_ _) (error 'rec/a-fold)])]))
  (define (rec/a t1 t2 a)
    (define (rec t1 t2)
      (cond
        [(equal? t1 t2) a]
        [(not (or (Mu? t1) (Mu? t2)))
         (match* (t1 t2)
           [((STuple n a1*) (STuple m a2*))
            #:when (<= m n)
            (rec/a-fold a a1* a2*)]
           ;; Contravariently function arguments
           [((Fn n a1* r1) (Fn n a2* r2))
            (rec/a-fold (rec r1 r2) a2* a1*)]
           ;; Invarient Reference types
           [((or (GVect a1) (GRef a1) (MVect a1) (MRef a1))
             (or (GVect a2) (GRef a2) (MVect a2) (MRef a2)))
            #:when (or (and (GVect? t1) (GVect? t2))
                       (and (GRef?  t1) (GRef?  t2))
                       (and (MVect? t1) (MVect? t2))
                       (and (MRef?  t1) (MRef?  t2)))
            (type=? a a1 a2)]
           [(_ _) #f])]
        [else
         (define p (cons t1 t2))
         (cond
           [(set-member? a p) a]
           [(Mu? t1) (rec/a (unfold-mu t1) t2 (set-add a p))]
           [(Mu? t2) (rec/a t1 (unfold-mu t2) (set-add a p))]
           [else (error 'subtype-of?)])]))
    (rec t1 t2))
    (debug 'subtype-of? t1 t2 (rec/a t1 t2 (set)))))

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
  (define e (make-hash))
  (define toplevel (mk-empty-clabel (srcloc->ppoint)))
  (define-values (x* ltype*)
    (for/lists (x* ltype*)
               ([tl (in-list  (filter Define? tl*))])
      (match tl
        [(Define _ id t2 _)
         (define clabel (refine-a-clabel toplevel (Idref id)))
         (define ltype (mk-ltype clabel t2))
         (value id ltype)])))
  (define toplevel/extended (env-extend* toplevel x* ltype*))
  (for/list ([tl (in-list tl*)])
    (match tl
      [(Define r? id t2 (app (gtf-expr toplevel/extended) ltype-e))
       (add-dummy-flow ltype-e (hash-ref toplevel/extended id))]
      [(Observe e t) ((gtf-expr toplevel/extended) e)])))

;; note that we don't need srcloc or expression anymore
(define (cast-or-not l-th lt1 lt2)
  (define who 'type-flow-generation/cast-or-not)
  (match-define (Ltype _ t1) lt1)
  (match-define (Ltype _ t2) lt2)
  (cond
    [(subtype-of? t1 t2)
     (add-dummy-flow t1 t2)]
    [else
     (add-blabel-flow t1 t2 (l-th))]))

  
(define ((gtf-expr env) exp^)
  (match-define (Ann exp (cons src (app unfold-possible-mu type))) exp^)
  (define out-ppoint (srcloc->ppoint src))
  (define out-clabel (mk-empty-clabel out-ppoint))
  (match exp
    [(Lambda fml* (and (Ann _ (cons body-src body-type))
                       body))
     (define fn-range (or (and (Fn? type) (Fn-ret type))
                          (error 'gtf-expr "function type recieve non-function type")))
     (define ret-label (refine-a-clabel out-clabel (Franref)))
     (define ret-ltype (mk-ltype ret-label fn-range))
     ;; first, collect bindings for arguments
     (define-values (x* clabel*) 
       (for/lists (x* clabel*)
                  ([fml (in-list fml*)]
                   [n   (in-naturals)])
         (values (Fml-identifier fml) (refine-a-clabel out-clabel (Fdomref n)))))
     (define body-ltype ((gtf-expr (env-extend* env x* clabel*))))
     (let ([lbl-th (mk-label "lambda" body-src)])
       (cast-or-not body-src lbl-th body-ltype ret-ltype))
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
     (match-define (Ann _ (cons rator-src (app unfold-possible-mu rator-type))) rator)
     (define rator-ltype ((gtf-expr env) rator))
     (define rator-clabel (Ltype-clabel rator-ltype))
     (match rator-type
       [(Dyn)
        ]
       [(Fn n dom ret-type)
        (for/list ([rand rand*]
                   [index (in-naturals)]
                   [dom-index dom])
          (match-let ([(Ann _ (cons rand-src rand-type)) rand])
            (define rand-ltype ((gtf-expr env) rand))
            (define lbl (mk-label "application" src rand-src))
            (define arg-ltype (mk-ltype (refine-a-clabel rator-clabel (Fdomref index)) dom-index))
            (cast-or-not lbl rand-ltype arg-ltype)))
        (define app-ltype (mk-ltype out-clabel ret-type))
        ;; add dummy type-flow,
        (define rator-ret-ltype (mk-ltype (refine-a-clabel rator-clabel (Franref))))
        (add-dummy-flow rator-ret-ltype app-ltype)
        app-ltype])]
    ))

(define (extend-env/bnd* e bnd* clabel)
  (define-values (x* clabel*)
    (for/lists (id* cl*)
               ([bnd bnd*])
      (match-define (Bnd i t _) bnd)
      (values i (mk-ltype (refine-a-clabel clabel (Idref i)) t))))
  (env-extend* e x* clabel*))

(define (gtf-bnd* bnd* env clabel)
  (define env/extended (extend-env/bnd* env bnd* clabel))
  (for/list ([bnd bnd*])
    (match-define (Bnd i t (and rhs (Ann _ (cons rhs-src rhs-type))) ) bnd)
    (define lbl (mk-label "binding" rhs-src))
    (define rhs-ltype ((gtf-expr env-extend*) rhs))
    (cast-or-not lbl rhs-ltype (hash-ref env/extended i)))
  env/extended)

(define (gtf-operand app-src env)
  (lambda (rand arg-ltype)
    (match-let ([(Ann _ (cons rand-src rand-type)) rand])
      (define rand-ltype ((gtf-expr env) rand))
      (define lbl (mk-label "application" app-src rand-src))
      (cast-or-not lbl rand-ltype arg-ltype))))






