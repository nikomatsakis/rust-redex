;; -*- coding: utf-8; -*-

;; Cheat sheet for unicode, using M-x set-input-method as TeX:
;; \alpha -> α
;; \beta  -> β
;; \gamma -> γ
;; \cdot  -> ·
;; \ell   -> ℓ
;; \in    -> ∈
;; \notin -> ∉
;; and so on
;; lifetime-≤

#lang racket

;; the Rust core syntax 
;; ---------------------------------------------------------------------------------------------------

(provide
 ;; defined language
 ;; the core Rust syntax (?)
 Patina)

;; ---------------------------------------------------------------------------------------------------
;; implementation

(require redex rackunit)

(define-language Patina
  (prog (srs fns))
  ;; structures:
  (srs (sr ...))
  (sr (struct s ℓs (ty ...)))
  ;; lifetimes:
  (ℓs (ℓ ...))
  ;; function def'ns
  (fns (fn ...))
  (fn (fun g ℓs vdecls bk))
  ;; blocks:
  (bk (block ℓ vdecls sts))
  ;; variable decls
  (vdecls [vdecl ...])
  (vdecl (x ty))
  ;; statements:
  [sts (st ...)]
  (st (lv = rv)
      (lv := rv)
      (free lv)                    ;; shallow free
      (drop lv)                    ;; deep free
      (call g ℓs lvs)
      (match lv (Some mode x => bk) (None => bk))
      bk)
  ;; lvalues :
  ;; changing "field names" to be numbers
  (lvs (lv ...))
  (lv x                            ;; variable
      (lv · f)                     ;; field projection
      (lv @ lv)                    ;; indexing
      (* lv))                      ;; deref
  ;; rvalues :
  (rv lv                           ;; use lvalue
      (& ℓ mq lv)                  ;; take address of lvalue
      (struct s ℓs (lv ...))       ;; struct constant
      number                       ;; constant number
      (lv + lv)                    ;; sum
      (new lv)                     ;; allocate memory
      (Some lv)                    ;; create an Option with Some
      (None ty)                    ;; create an Option with None
      (vec ty lv ...)              ;; create a fixed-length vector
      (vec-len lv)                 ;; extract length of a vector
      (pack lv ty)                 ;; convert fixed-length to DST
      )
  (mode (ref ℓ mq) by-value)
  ;; types : 
  (tys (ty ...))
  (ty (struct s ℓs)             ;; s<'ℓ...>
      (~ ty)                       ;; ~t
      (& ℓ mq ty)                  ;; &'ℓ mq t
      int
      (Option ty)
      (vec ty olen))
  ;; mq : mutability qualifier
  (mq mut imm)
  (mqs [mq ...])
  ;; variables
  (x variable-not-otherwise-mentioned)
  ;; function names
  (g variable-not-otherwise-mentioned)
  ;; structure names
  (s variable-not-otherwise-mentioned)
  ;; labels
  (ℓ variable-not-otherwise-mentioned)
  ;; field "names"
  (f number)
  (fs [f ...])
  ;; z -- sizes, offsets
  [zs (z ...)]
  [z number]
  ;; l -- vector lengths
  [l number]
  ;; olen -- optional vector lengths
  [olen number erased]
  ;; hack for debugging
  (debug debug-me)
  )

(module+ test
  (check-not-false (redex-match Patina ty (term (vec int 3)))))

(module+ test
  (test-results))
