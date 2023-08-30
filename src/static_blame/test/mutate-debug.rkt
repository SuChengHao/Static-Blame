#lang racket
(require syntax/parse)

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
(require syntax/parse/debug)
(define stx-test #'([swap
                     : Int
                     (let ([t : Int (vector-ref a i)])
                       1
                       )]))
(define stx-test-2 #'[swap
                       :
                       ((Vect Int) Int Int -> ())
                       (lambda ((a : (Vect Int)) (i : Int) (j (: Int Dyn) (: : Dyn)))
                               :
                         Unit
                         (if (= i j)
                             ()
                             (let ([t
                                    :
                                    Int
                                    (vector-ref a i)])
                               (begin
                                 (vector-set! a i (vector-ref a j))
                                 (vector-set! a j t)))))])
(define stx-test-3 #'([sort
                :
                ((Vect Int) Int Int -> ())
                (lambda ((a : (Vect Int)) (p : Int) (r : Int))
                  :
                  Unit
                  (if (< p r)
                      (let ([q
                             :
                             Int
                             (partition a p r)])
                        (begin
                          (sort a p (- q 1))
                          (sort a (+ q 1) r)))
                      ()))]
               [partition
                :
                ((Vect Int) Int Int -> Int)
                (lambda ((a : (Vect Int)) (p : Int) (r : Int))
                  :
                  Int
                  (let ([i
                         :
                         (Ref Int)
                         (box (- p 1))]
                        [x
                         :
                         Int
                         (vector-ref a r)])
                    (begin
                      (repeat (j p r)
                              (_ : Unit ())
                              (if (<= (vector-ref a j) x)
                                  (begin
                                    (box-set! i (+ (unbox i) 1))
                                    (swap a (unbox i) j))
                                  ()))
                      (swap a (+ (unbox i) 1) r)
                      (+ (unbox i) 1))))]
               [swap
                :
                ((Vect Int) Int Int -> ())
                (lambda ((a : (Vect Int)) (i : Int) (j (: Int Dyn) (: : Dyn)))
                  :
                  Unit
                  (if (= i j)
                      ()
                      (let ([t
                             :
                             Int
                             (vector-ref a i)])
                        (begin
                          (vector-set! a i (vector-ref a j))
                          (vector-set! a j t)))))]))
(displayln (debug-parse stx-test-3
                     (bnd:binding ...)  ))
