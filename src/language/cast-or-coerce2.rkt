#lang typed/racket/base
(require "forms.rkt")
(provide (all-defined-out)
         (all-from-out "forms.rkt"))
#|-----------------------------------------------------------------------------+
| Language/Cast2 created by lower-castable-references                          |
+-----------------------------------------------------------------------------|#

(define-type Cast-or-Coerce2-Lang
 (Prog (List String Natural Schml-Type) CoC2-Expr))

(define-type CoC2-Expr
  (Rec E (U ;; Code Labels
          (Code-Label Uid)
          (Labels CoC2-Bnd-Code* E)
          (App-Code E (Listof E))
          ;; Functions as an interface
          (Lambda Uid* (Castable (Option Uid) E))
          (Fn-Caster E)
          (App-Fn E (Listof E))
          ;; Our Lovely Function Proxy Representation
          (App/Fn-Proxy-Huh E (Listof E))
          (Fn-Proxy Index E E)
          (Fn-Proxy-Huh E)
          (Fn-Proxy-Closure E)
          (Fn-Proxy-Coercion E)
          ;; Coercions
          (Quote-Coercion Schml-Coercion)
          (Compose-Coercions E E)
          (Id-Coercion-Huh E)
          (Fn-Coercion (Listof E) E)
          (Fn-Coercion-Arg E E)
          (Fn-Coercion-Return E)
          (Ref-Coercion E E)
          (Ref-Coercion-Read E)
          (Ref-Coercion-Write E)
          ;; Binding Forms - Lambda
	  (Letrec CoC2-Bnd* E)
	  (Let CoC2-Bnd* E)
          (Var Uid)
          ;; Controll Flow
          (If E E E)
          (Begin CoC2-Expr* E)
          (Repeat Uid E E E)
          ;;Primitives
          (Op Schml-Primitive (Listof E))
          (Quote Cast-Literal)
          (Tag Tag-Symbol)
          ;; Casts with different ways of getting the same semantics
	  (Cast E (Twosome Schml-Type Schml-Type Blame-Label))
          (Cast E (Coercion Schml-Coercion))
          (Interpreted-Cast E (Twosome E E E))
          (Interpreted-Cast E (Coercion E))
          ;;Type operations
          (Type Schml-Type)
          (Type-Fn-arg E E)
          (Type-Fn-return E)
          (Type-Fn-arity E)
          (Type-Tag E)
          ;; Dynamic Representation
          (Dyn-tag E)
          (Dyn-immediate E)
          (Dyn-type E)
          (Dyn-value E)
          (Dyn-make E E)
          ;; Observations
          (Blame E)
          ;; Unguarded-Representation
          (Unguarded-Box E)
          (Unguarded-Box-Ref E)
          (Unguarded-Box-Set! E E)
          (Unguarded-Vect E E)
          (Unguarded-Vect-Ref E E)
          (Unguarded-Vect-Set! E E E)
          (Guarded-Proxy-Huh E)
          (Guarded-Proxy E (Twosome E E E))
          (Guarded-Proxy E (Coercion E))
          (Guarded-Proxy-Ref E)
          (Guarded-Proxy-Source E)
          (Guarded-Proxy-Target E)
          (Guarded-Proxy-Blames E)
          (Guarded-Proxy-Coercion E))))

(define-type CoC2-Code (Code Uid* CoC2-Expr))

(define-type CoC2-Expr* (Listof CoC2-Expr))
(define-type CoC2-Bnd (Pairof Uid CoC2-Expr))
(define-type CoC2-Bnd* (Listof CoC2-Bnd))
(define-type CoC2-Bnd-Code (Pairof Uid CoC2-Code))
(define-type CoC2-Bnd-Code* (Listof CoC2-Bnd-Code))

