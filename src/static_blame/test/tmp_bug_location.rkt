#lang racket
(require "../../grift/reduce-to-cast-calculus.rkt")
(require "../../casts/impose-cast-semantics.rkt")
;; BUG location track
;; phenomenon: compilation fail with "no such file or directory", but without imformation about which
;; file it tries to open
;; phenomenon: most test case fails, but few success.
;; phenomenon: by print and trace, we know the bug happens inside impose-semantics
;; what we need to do:
;; Try1: run by strace


