;; this file contains the core data structure of static blame: the type flow
;; conceptually, it consists of two parts: the type flow itself, and constraint
;; solvers

#lang racket
(require "./refinement.rkt"
         "../language/pprint.rkt"
         "../language/forms.rkt"
         racket/contract
         racket/contract/option
         racket/pretty
         )
(require "../logging.rkt")

(provide (all-defined-out))

;; Checks to make sure Mu types obey the productivity check
;; Return the a version of type where superflouos mu are droped
;; and unrolled Mus are rerolled.
;; Note that this definition is buggy
;(: validate-type : srcloc Grift-Type -> Grift-Type)
(define (validate-type t)
  (define who 'validate-type)
  (define eqs
    (make-hash '()))

  (define (vt pending)
    
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
                  ))
         t]
        [else
         ;; If the type constructor is for actual data then the mu is productive
         ;; and we can clear the pending recursive variables.
         (define vt/pending
           (if (structural-type? t) (vt (set)) rec))
         (define r (grift-type-map t vt/pending))
         (or (hash-ref eqs r #f) r)]))
    rec)
  (debug who type ((vt (set)) t)))
;; is `t1` a subtype of `t2`?
(define (subtype-of? t1 t2)
  (define (type=? a t1 t2)
    ;; I think this is a more optimized version of
    ;; (and (rec/a a t1 t2) (rec/a a t2 t1) a)
    ;; (rec/a (rec/a a t1 t2) t2 t1))
    ;; no, I don't think it is correct.
    (and (rec/a a t1 t2) (rec/a a t2 t1) a))
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
    (debug 'subtype-of? t1 t2 (rec/a t1 t2 (set))))

;; a flag, is a dummy flag, or just a string that stands for a blame message.
(define Dummy-Flag 'dummy)

(struct Ltype (clabel gtype) #:transparent)

(define (mk-ltype clabel gtype)
  (or 
   (Clabel? clabel)
   (error 'bad-clabel "call mk-ltype on an invalid label"))
  (or
   (type? gtype)
   error 'bad-gtype (format "the argument ~a is not a gtype" gtype))
  (Ltype clabel (validate-type gtype)))

;; A type-flow is just a pair of two labeled type
(struct Tyflow (from to blame-label)
  #:transparent)

(define (check-ltype ltype)
  (and (Ltype? ltype)
       (type? (Ltype-gtype ltype))
       (check-clabel (Ltype-clabel ltype))))

;; check whether from is a 
(define (legal-type-flow? flow)
  (and (Tyflow? flow) (check-ltype (Tyflow-from flow))
       (check-ltype (Tyflow-to flow))))



;; A labeled type, is just a pair of a gradual type and a Clabel
;; but, in our design, an expression only has one type, then the
;; gradual type becomes a redundancy.

;;(define (make-dummy-type-flow from to)
;;  (Tyflow from to Dummy-Flag))

;;(define (mk-dummy-type-flow from to blabel)
;;  (Tyflow from to blabel))

(define (box-ltype->content-ltype ltype)
  (match ltype
    [(Ltype clabel gtype)
     (cond
       [(Dyn? gtype)
        (mk-ltype (refine-a-clabel clabel (Boxref)) (GRef-arg gtype))]
       [else
        (mk-ltype (refine-a-clabel clabel (Boxref)) DYN-TYPE)])
     ]))

(define (tuple-ltype->content-ltype ltype i)
  (match ltype
    [(Ltype clabel (STuple n ty*))
     (mk-ltype (refine-a-clabel clabel (Tupref i)) (list-ref ty* i) )]))
(define (tuple-ltype->content-ltype* ltype)
  (match ltype
    [(Ltype clabel (STuple n ty*))
     (for/list ([ty ty*]
                [i (in-naturals)])
      (mk-ltype (refine-a-clabel clabel (Tupref i)) ty))]))

(define (vector-ltype->content-ltype ltype)
  (match ltype
    [(Ltype clabel (GVect ty ))
     (mk-ltype (refine-a-clabel clabel (Vecref)) ty)]))

(define (function-ltype->dom-ltype* ltype)
  (match ltype
    [(Ltype clabel (Fn _ dom* ran))
     (for/list ([dom dom*]
                [i (in-naturals)])
       (mk-ltype (refine-a-clabel clabel (Fdomref i)) dom))]))
(define (function-ltype->ran-ltype ltype)
  (match ltype
    [(Ltype clabel (Fn _ _ ran))
     (mk-ltype (refine-a-clabel clabel (Franref)) ran)]))



;; (define (make-type-flow from to src)
;;   (type-flow from to
;;              (format "type ~a flows into type ~b at source location: ~a/n"
;;                      (type->string (erase-type-label from))
;;                      (type->string (erase-type-label to))
;;                      (srcloc->string src))))

;; constraint solver:
;; a set, for all type flows
;; two hash set, for all in-flow and all out-flow

(struct CSolver (collection inflows outflows))

(define current-solver (make-parameter #f))

;; --A constraint-solver is a solver that can solve constraint --
;; Never mind, A constraint solver can add type flow, calculate closure, and
;; finally judge whether there exists potential error in the program.
(define (make-constraint-solver)
  (CSolver (mutable-set) (make-hash) (make-hash)))
(define (export-type-flow [solver (current-solver)])
  (set->list (CSolver-collection solver)))

(define (add-type-flow-to-a-solver new-flow [solver (current-solver)])
  (or (legal-type-flow? new-flow) (error 'bad-flow (format "flow ~a is bad" (pretty-format new-flow))))
  (set-add! (CSolver-collection solver) new-flow)
  (match-let ([(Tyflow from to _) new-flow])
    (let ([to-inflows (hash-ref! (CSolver-inflows solver) to (mutable-set))]
          [from-outflows (hash-ref! (CSolver-outflows solver) from (mutable-set))])
      (set-add! to-inflows new-flow )
      (set-add! from-outflows new-flow))))
(define (add-blabel-flow from to blabel [solver (current-solver)])
  (add-type-flow-to-a-solver (Tyflow from to blabel) solver ))
(define (add-dummy-flow from to [solver (current-solver)])
  (add-type-flow-to-a-solver (Tyflow from to Dummy-Flag) solver))

(define (dummy? flow)
  (equal? (Tyflow-blame-label flow) Dummy-Flag))

(define (up-cast? flow)
  (match-define (Tyflow from to _) flow)
  (and (not (Dyn? (Ltype-gtype from)))
       (Dyn? (Ltype-gtype to))))

(define (down-cast? flow)
  (match-define (Tyflow from to _) flow)
  (and (Dyn? (Ltype-gtype from))
       (not (Dyn? (Ltype-gtype to)))))

(define (trans-cast? flow)
  (match-define (Tyflow from to _) flow)
  (and (Dyn? (Ltype-gtype from))
       (Dyn? (Ltype-gtype to))))

(define ((cast-elimination? flow1) flow2)
  (match-define (Tyflow (Ltype _ t1) (Ltype _ (? Dyn?)) _ ) flow1)
  (match-define (Tyflow (Ltype _ (? Dyn?)) (Ltype _ t2) _ ) flow2)
  (subtype-of? t1 t2))
(define (flow-subtype-of? flow)
  (match-define (Tyflow (Ltype _ t1) (Ltype _ t2) _) flow)
  (subtype-of? t1 t2))

(define (flow-consistent? flow)
  (match-define (Tyflow (Ltype _ t1) (Ltype _ t2) _) flow)
  (consistent? t1 t2))


(define (function-flow? flow)
  (match-define (Tyflow (Ltype _ t1) (Ltype _ t2)  _) flow)
  (and (Fn? t1) (Fn? t2)))

(define (box-flow? flow)
  (match-define (Tyflow (Ltype _ t1) (Ltype _ t2)  _) flow)
  (and (Gbox? t1) (Gbox? t2)))

(define (vector-flow? flow)
  (match-define (Tyflow (Ltype _ t1) (Ltype _ t2)  _) flow)
  (and (Gvector? t1) (Gvector? t2)))
(define (tuple-flow? flow)
  (match-define (Tyflow (Ltype _ t1) (Ltype _ t2)  _) flow)
  (and (STuple? t1) (STuple? t2)))



(define (function-decomposition flow)
  (match-define (Tyflow (and lt1 (Ltype _ t1)) (and lt2 (Ltype _ t2))  flag) flow)
  (let ([lt1-dom* (function-ltype->dom-ltype* lt1)]
        [lt2-dom* (function-ltype->dom-ltype* lt2)]
        [lt1-ran (function-ltype->ran-ltype lt1)]
        [lt2-ran (function-ltype->ran-ltype lt2)])
    ;;for each in dom, add an reverse flow
    ;;and flow between ranges
    (define new-flow-dom* (map (lambda (from to)
                                 (Tyflow from to flag)) lt2-dom* lt1-dom*))
    (define new-flow-ran (Tyflow lt1-ran lt2-ran flag))
    (cons new-flow-ran new-flow-dom*)))

(define (box-decomposition flow)
  (match-define (Tyflow (and lt1 (Ltype _ t1)) (and lt2 (Ltype _ t2))  flag) flow)
  (let ([lt1-con (box-ltype->content-ltype lt1)]
        [lt2-con (box-ltype->content-ltype lt2)])
    (Tyflow lt1-con lt2-con flag)))

(define (vector-decomposition flow)
  (match-define (Tyflow (and lt1 (Ltype _ t1)) (and lt2 (Ltype _ t2))  flag) flow)
  (let ([lt1-con (vector-ltype->content-ltype lt1)]
        [lt2-con (vector-ltype->content-ltype lt2)])
    (Tyflow lt1-con lt2-con flag)))

(define (tuple-decomposition flow)
  (match-define (Tyflow (and lt1 (Ltype _ (STuple n _))) (and lt2 (Ltype _ t2))  flag) flow)
  (let ([lt1-con* (tuple-ltype->content-ltype* lt1)]
        [lt2-con* (tuple-ltype->content-ltype* lt2)])
    (for/list ([lt1-con lt1-con*]
               [lt2-con lt2-con*])
      (Tyflow lt1-con lt2-con flag))))

(define (add-lst-to-solver lst solver)
    (define mutset (CSolver-collection solver))
    (foldl (lambda (n res)
             (if (set-member? mutset n)
                 res
                 (begin
                   (add-type-flow-to-a-solver solver n)
                   #t))) #f lst))

(define (solve-a-solver solver)
  ;;forever loop
  
  (match-define (CSolver solver-set inflows outflows) solver)
  (define saturation-list
    (let ([work-list (set->list solver-set)])
      (for/fold ([new-flows-to-add (list)])
                ([flow work-list])
        (match-define (Tyflow from to flag) flow)
        (cond
          [(not (flow-consistent? flow))
           (error 'inner-logical-error (format "The flow ~a is not about consistent ltypes" (pretty-format flow)))]
          [(dummy? flow)
           ;; for all out-flow of the next
           (define pre-flows (hash-ref inflows from (set)))
           (define new-flows (map (lambda (flow)
                                    (match flow
                                      ([Tyflow new-from _ lth]
                                       (Tyflow new-from to lth))))
                                  (set->list pre-flows)))
           (append new-flows new-flows-to-add)]
          [(up-cast? flow)
           ;; for-each down cast, trans if consistency hold
           ;; otherwise, ignore it.
           ;; for-each trans-cast, trans it.
           (define next-flows (hash-ref outflows to (set)))
           (define next-flows-list (set->list next-flows))
           (let* ([down-casts (filter down-cast? next-flows-list)]
                  [trans-casts (filter trans-cast? next-flows-list)]
                  [down-cast-to-eli (filter (cast-elimination? flow) down-casts)])
             (define down-cast-elimination (map (lambda (flow)
                                                  (match flow
                                                    ([Tyflow _ new-to lth]
                                                     (Tyflow from new-to lth)))) down-cast-to-eli))
             (define trans-cast-elimination (map (lambda (flow)
                                                   (match flow
                                                     ([Tyflow _ new-to _]
                                                      (Tyflow from new-to flag)))) trans-casts))
             (append down-cast-elimination trans-cast-elimination new-flows-to-add))]
          [(function-flow? flow)
           (define new-flows (function-decomposition flow))
           (append new-flows new-flows-to-add)]
          [(box-flow? flow)
           (define new-flows (list (box-decomposition flow)))
           (append new-flows new-flows-to-add)]
          [(vector-flow? flow)
           (define new-flows (list (vector-decomposition flow)))
           (append new-flows new-flows-to-add)]
          [(tuple-flow? flow)
           (define new-flows (tuple-decomposition flow))
           (append new-flows new-flows-to-add)]))))
  (when (add-lst-to-solver saturation-list solver)
    (solve-a-solver solver)))


