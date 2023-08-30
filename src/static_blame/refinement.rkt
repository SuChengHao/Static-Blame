#lang racket/base
(require
 "../language/forms.rkt"
 racket/match
 (for-syntax racket/syntax
             racket/base))

(module+ test
  (require rackunit))

(provide (except-out
          (all-defined-out)
          ))



; A context label is just a position and a list of context-refinements

;; however, not every textual object in AST have src attached,
;; and we need to do special optimization for it.

;; refinements we need:
;; functions: arg- one for each position and ret-value
;; tuples: numbered records, one for each number
;; box: for its content.
;; Vector: *One* for its content.

;; program point p point
(struct Ppoint (src)
  #:transparent)

;; (struct Bndpoint Ppoint (bnd-id)
;;   #:transparent)

(struct Clabel (ppoint ref*)
  #:transparent)

(struct Cref () #:transparent)

(define-syntax (define-struct-transparent stx)
  (syntax-case stx ()
    [(_ super (name* field** ...) ...)
     (begin
       #'(begin (struct name* super (field** ...) #:transparent) ...))]))
(define-struct-transparent Cref
  (Idref uid)
  (Constref c)
  (Fdomref index)
  (Franref)
  (Boxref)
  (Castref) ;; generated environment
  (Vecref)
  (Tupref index))




(define (refine-a-clabel clabel refinement) 
  (match-define (Clabel ppoint ref*) clabel)
  (Clabel ppoint (cons refinement  ref*)))

(define (mk-empty-clabel ppoint)
  (Clabel ppoint '()))

(define (srcloc->ppoint [src 'toplevel])
  (Ppoint src))
(define (check-refinements ref*)
  (for/and ([ref ref*])
    (Cref? ref)))
(define (check-clabel clabel)
  (and (Clabel? clabel)
       (check-refinements (Clabel-ref* clabel))))







#| 
(struct position-label (src)
  #:transparent)
(struct binding-position-label position-label (bnd-id)
  #:transparent)

(struct context-label (program-point list-of-refinement )
  #:transparent)


(struct context-refinement ()
  #:transparent)
(struct constant-refinement context-refinement ()
  #:transparent)
(struct function-refinement context-refinement ()
  #:transparent)
(struct function-domain-refinement context-refinement (index) #:transparent)
(struct function-range-refinement context-refinement ()
  #:transparent)
(struct reference-refinement context-refinement ()
  #:transparent)
(struct vector-refinement context-refinement ()
  #:transparent)
(struct tuple-refinement context-refinement (index)
  #:transparent)
(struct assoc-stack-refinement context-refinement ()
  #:transparent)

;; an src is an srcloc object
;; or a lists of special
;; (Union srcloc (cons srcloc ) )
(define (make-empty-context-label src)
  (context-label (position-label src) '()))
(define (make-binding-context-label bnd-src bnd-id)
  (context-label (binding-position-label bnd-src bnd-id)))
(define (add-refinement (clabel))
  ;;refine a context label.
  (match-define )
  )


(define-syntax (define-type/labeled stx)
  (syntax-case stx ()
    [(_ super (name* field** ...) ...)
     (begin
       (define (f name) (format-id stx "~a/labeled" name))
       (with-syntax ([(name/labeled* ...) (map f (syntax->list #'(name* ...)))])
         #'(begin (struct name/labeled* super (field** ...) #:transparent) ...)))]))

(struct type/labeled (context-label)
  #:transparent)

(define-type/labeled type/labeled
  (structural-type)
  (logical-type))

(define-type/labeled structural-type/labeled
  (base-type)
  (Dyn)
  (Fn arity fmls ret)
  (MRef arg)
  (MVect arg)
  (GRef arg)
  (GVect arg)
  (STuple num items))

(define-type/labeled base-type/labeled
  (Unit)
  (String)
  (Void)
  (Obj)
  (Assoc-Stack)
  (Bot)
  (Int)
  (Float)
  (Bool)
  (Character))
;; Not a type but abstraction enforcement
(struct Scope (open) #:transparent)
(struct Mu/labeled logical-type/labeled (body) #:transparent)
(struct TVar (index) #:transparent)
(struct FVar (name) #:transparent)

(define-syntax (match-base-type/labeled stx)
  (syntax-case stx ()
    [(_ type clabel base* ...)
     (begin
       (define (f name) (format-id stx "~a/labeled" name))
       (with-syntax ([(base/labeled* ...) (map f (syntax->list #'(base* ...)))])
         #'(match type
             [(base*) (base/labeled* clabel)] ...)))]))

(define (context-label/append-to-refine-list clabel new-refine)
  (match-define (context-label pp refine-list) clabel)
  (context-label pp (append refine-list (list new-refine))))

(define (refine-function-domain-type clabel domain-type*)
  (for/list ([domain-type domain-type* ]
             [i (in-naturals) ])
    (refine-a-type
     (context-label/append-to-refine-list clabel (function-domain-refinement i) )
     domain-type)))
(define (refine-function-range-type clabel range-type)
  (refine-a-type
     (context-label/append-to-refine-list clabel (function-range-refinement))
     range-type))

(define (refine-function-type clabel arity fmls ret)
  (define new-fmls (refine-function-domain-type clabel fmls))
  (define new-ret
    (refine-function-range-type clabel ret))
  (Fn/labeled clabel arity new-fmls new-ret));; return the labeled type

(define (refine-a-type clabel type)
  ;; (match-define (context-label pp refine-list) clabel); pp for program point
  ;; for a function type, the refined type will have the same arity, with
  ;; 1. each argument get a function-domain-refinement
  ;; 2. the return type get a function-range-refinement
  (match type
    [(Fn arity fmls ret) (refine-function-type clabel arity fmls ret )]
    [(MRef arg) (MRef/labeled clabel (refine-a-type
                               (context-label/append-to-refine-list clabel (reference-refinement))
                               arg))]
    [(MVect arg) (MVect/labeled clabel (refine-a-type
                                 (context-label/append-to-refine-list clabel (vector-refinement))
                                 arg))]
    [(GRef arg) (GRef/labeled clabel (refine-a-type
                               (context-label/append-to-refine-list clabel (reference-refinement))
                               arg))]
    [(GVect arg) (GVect/labeled clabel (refine-a-type
                                 (context-label/append-to-refine-list clabel (vector-refinement))
                                 arg))]
    [(STuple num type-list) (STuple/labeled clabel num
                                            (for/list ([content-type type-list]
                                                       [index (in-naturals)])
                                              (refine-a-type
                                               (context-label/append-to-refine-list clabel (tuple-refinement index ))
                                               content-type)))]
    [(and place-holder (TVar i)) place-holder];; a type variable is just equal to the whole type, so nothing needs to be done
    [(Mu (Scope Inner-type)) (Mu/labeled clabel (Scope (refine-a-type clabel Inner-type) )) ]
    [base (match-base-type/labeled base clabel Unit String Void Obj Assoc-Stack Bot Int Float Bool Character Dyn)  ]))

(define-syntax (erase-type-label/base stx)
  (syntax-case stx ()
    [(_ type base* ...)
     (begin
       (define (f name) (format-id stx "~a/labeled" name))
       (with-syntax ([(base/labeled* ...) (map f (syntax->list #'(base* ...)))])
         #'(match type
             [(base/labeled* clabel) (base*)] ...)))]))

(define (erase-type-label t/labeled)
  (match t/labeled
    [(Fn/labeled _ arity fmls ret) (Fn arity (map erase-type-label fmls) (erase-type-label ret) ) ]
    [(MRef/labeled _ arg) (MRef (erase-type-label arg))]
    [(GRef/labeled _ arg) (GRef (erase-type-label arg))]
    [(MVect/labeled _ arg) (MVect (erase-type-label arg))]
    [(GVect/labeled _ arg) (GVect (erase-type-label arg))]
    [(STuple/labeled _ num items) (STuple num (map erase-type-label items))]
    [(Mu/labeled _ (Scope inner-type)) (Mu (Scope (erase-type-label inner-type)))]
    [(and place-holder (TVar i)) place-holder]
    [base (erase-type-label/base base Unit String Void Obj Assoc-Stack Bot Int Float Bool Character Dyn)]))


(module+ test
  (define mu-dyn
    (Mu (Scope (STuple 2 (list DYN-TYPE (TVar 0))))))
  (define mu-int
    (Mu (Scope (STuple 2 (list INT-TYPE (TVar 0))))))
  (define  function-type
    (Fn 2 `(,(Dyn) ,(Dyn)) (Dyn)))) |#



