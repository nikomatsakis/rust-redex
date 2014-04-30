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

;; Rust's type system 
;; ---------------------------------------------------------------------------------------------------

(require redex rackunit "syntax.rkt" "machine.rkt")

;;;;
;;
;; TYPING RULES
;;
;;;;

;; MF: I consider it highly unusual that the type checking language extends
;; the machine evaluation language. Are you sure you want that? 

(define-extended-language Patina-typing Patina-machine
  ;; de-initialization: lists lvalues that have been de-initialized
  (Δ (lv ...))
  
  ;; lifetime declaration: lifetime ℓ is in scope, and it is a sublifetime
  ;; of ℓs
  (λ (ℓ ℓs))
  (λs (λ ...))
  
  ;; lifetime relation: what lifetimes are in scope; in future, what
  ;; is their relation to one another
  (Λ λs)
  
  ;; variable lifetimes: map of maps from variable name to lifetime of
  ;; block where it was defined
  (vl (x ℓ))
  (vls [vl ...])
  (VL [vls ...])
  
  ;; in-scope loans
  (loan (ℓ mq lv))
  (£ [loan ...])
  
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Testing constants
;;
;; Our test fn is roughly:
;;
;; fn foo<'p0, 'p1>() 'a: {
;;    let i: int;
;;    'b: {
;;      let r-imm-B: &'b B<'static>;
;;      let r-mut-B: &'b B<'static>;
;;      let owned-B: ~B<'static>;
;;      let owned-E: ~E;
;;      let r-mut-int: &'a mut int
;;      let opt-int: Option<int>
;;    }
;; }

(define test-ty-Λ (term [(p0 []) (p1 []) (a [p0 p1]) (b [a p0 p1])]))
(define test-ty-T (term [[;; block a
                          (i int)
                          ]
                         [;; block b
                          (r-imm-B (& b imm (struct B (static))))
                          (r-mut-B (& b mut (struct B (static))))
                          (owned-B (~ (struct B (static))))
                          (owned-E (~ (struct E ())))
                          (r-mut-int (& a mut int))
                          (opt-int (Option int))
                          ]
                         ]))
(define test-ty-VL (term [[;; block a
                           (i a)
                           ]
                          [;; block b
                           (r-imm-B b)
                           (r-mut-B b)
                           (owned-B b)
                           (owned-E b)
                           (r-mut-int b)
                           (opt-int b)
                           ]
                          ]))

(define test-ty-srs test-srs)
(define test-ty-fns
  (term [(fun drop-owned-B [l0] [(x (~ (struct B (l0))))]
              (block l1
                     []
                     [(drop x)]))
         ]))
(define test-ty-prog (term (,test-ty-srs ,test-ty-fns)))

(check-not-false (redex-match Patina-machine prog test-ty-prog))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lifetime-=, lifetime-≠

(define-metafunction Patina-typing
  lifetime-= : ℓ ℓ -> boolean
  
  [(lifetime-= ℓ_1 ℓ_1) #t]
  [(lifetime-= ℓ_1 ℓ_2) #f]
  )

(define-metafunction Patina-typing
  lifetime-≠ : ℓ ℓ -> boolean
  
  [(lifetime-≠ ℓ_1 ℓ_1) #f]
  [(lifetime-≠ ℓ_1 ℓ_2) #t]
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lifetime-≤

(define-judgment-form
  Patina-typing
  #:mode     (lifetime-≤ I I I)
  #:contract (lifetime-≤ Λ ℓ ℓ)
  
  [--------------------------------------------------
   (lifetime-≤ Λ ℓ ℓ)]
  
  [--------------------------------------------------
   (lifetime-≤ Λ ℓ static)]
  
  [(side-condition (has ℓ_a Λ))
   (where ℓs (get ℓ_a Λ))
   (side-condition (∈ ℓ_b ℓs))
   --------------------------------------------------
   (lifetime-≤ Λ ℓ_a ℓ_b)]
  
  )

(test-equal
 (judgment-holds (lifetime-≤ [(a [b c]) (b []) (c [])] a a))
 #t)

(test-equal
 (judgment-holds (lifetime-≤ [(a [b c]) (b []) (c [])] a b))
 #t)

(test-equal
 (judgment-holds (lifetime-≤ [(a [b c]) (b []) (c [])] a c))
 #t)

(test-equal
 (judgment-holds (lifetime-≤ [(a [b c]) (b []) (c [])] b b))
 #t)

(test-equal
 (judgment-holds (lifetime-≤ [(a [b c]) (b []) (c [])] b c))
 #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; subtype

(define-judgment-form
  Patina-typing
  #:mode     (subtype I I I)
  #:contract (subtype Λ ty ty)
  
  [;; FIXME model variance somehow
   --------------------------------------------------
   (subtype Λ (struct s ℓs) (struct s ℓs))]
  
  [(subtype Λ ty_1 ty_2)
   --------------------------------------------------
   (subtype Λ (~ ty_1) (~ ty_2))]
  
  [(lifetime-≤ Λ ℓ_2 ℓ_1)
   (subtype Λ ty_1 ty_2)
   --------------------------------------------------
   (subtype Λ (& ℓ_1 imm ty_1) (& ℓ_2 imm ty_2))]
  
  [(lifetime-≤ Λ ℓ_2 ℓ_1)
   --------------------------------------------------
   (subtype Λ (& ℓ_1 mut ty) (& ℓ_2 mut ty))]
  
  [--------------------------------------------------
   (subtype Λ int int)]
  
  [(subtype Λ ty_1 ty_2)
   --------------------------------------------------
   (subtype Λ (Option ty_1) (Option ty_2))]
  
  [(subtype Λ ty_1 ty_2)
   --------------------------------------------------
   (subtype Λ (vec ty_1 olen) (vec ty_2 olen))]
  
  )

(test-equal
 (judgment-holds (subtype ,test-ty-Λ int int))
 #t)

(test-equal
 (judgment-holds (subtype ,test-ty-Λ (& b mut int) (& a mut int)))
 #f)

(test-equal
 (judgment-holds (subtype ,test-ty-Λ (& static mut int) (& a mut int)))
 #t)

(test-equal
 (judgment-holds (subtype ,test-ty-Λ (& a mut int) (& b mut int)))
 #t)

(test-equal
 (judgment-holds (subtype ,test-ty-Λ (Option (& a mut int)) (Option (& b mut int))))
 #t)

(test-equal
 (judgment-holds (subtype ,test-ty-Λ (~ (& a mut int)) (~ (& b mut int))))
 #t)

(test-equal
 (judgment-holds (subtype ,test-ty-Λ (vec (& a mut int) 2) (vec (& b mut int) 2)))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ty-is-pod

(define-metafunction Patina-typing
  ty-is-pod : srs ty -> boolean
  
  [(ty-is-pod srs int) #t]
  
  [(ty-is-pod srs (& ℓ imm ty)) #t]
  
  [(ty-is-pod srs (& ℓ mut ty)) #f]
  
  [(ty-is-pod srs (~ ty)) #f]
  
  [(ty-is-pod srs (Option ty)) (ty-is-pod srs ty)]
  
  [(ty-is-pod srs (struct s ℓs))
   (∀ [(ty-is-pod srs ty_s) ...])
   (where [ty_s ...] (field-tys srs s ℓs))]
  
  )

(test-equal
 (term (ty-is-pod [] int))
 #t)

(test-equal
 (term (ty-is-pod [] (Option int)))
 #t)

(test-equal
 (term (ty-is-pod [] (~ int)))
 #f)

(test-equal
 (term (ty-is-pod [] (Option (~ int))))
 #f)

(test-equal
 (term (ty-is-pod [] (& b imm int)))
 #t)

(test-equal
 (term (ty-is-pod [] (& b mut int)))
 #f)

(test-equal
 (term (ty-is-pod ,test-srs (struct A [])))
 #t)

(test-equal
 (term (ty-is-pod ,test-srs (struct E [])))
 #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ty-needs-drop

(define-metafunction Patina-typing
  ty-needs-drop : srs ty -> boolean
  
  [(ty-needs-drop srs int) #f]
  
  [(ty-needs-drop srs (& ℓ imm ty)) #f]
  
  [(ty-needs-drop srs (& ℓ mut ty)) #f]
  
  [(ty-needs-drop srs (~ ty)) #t]
  
  [(ty-needs-drop srs (Option ty)) (ty-needs-drop srs ty)]
  
  [(ty-needs-drop srs (struct s ℓs))
   (∃ [(ty-needs-drop srs ty_s) ...])
   (where [ty_s ...] (field-tys srs s ℓs))]
  
  )

(test-equal
 (term (ty-needs-drop [] int))
 #f)

(test-equal
 (term (ty-needs-drop [] (Option int)))
 #f)

(test-equal
 (term (ty-needs-drop [] (~ int)))
 #t)

(test-equal
 (term (ty-needs-drop [] (Option (~ int))))
 #t)

(test-equal
 (term (ty-needs-drop [] (& b imm int)))
 #f)

(test-equal
 (term (ty-needs-drop [] (& b mut int)))
 #f)

(test-equal
 (term (ty-needs-drop ,test-srs (struct A [])))
 #f)

(test-equal
 (term (ty-needs-drop ,test-srs (struct E [])))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; in-scope-lifetimes
;;
;; Convert a Λ to a list ℓs of in-scope lifetimes

(define-metafunction Patina-typing
  in-scope-lifetimes : Λ -> ℓs
  
  [(in-scope-lifetimes ((ℓ ℓs) ...)) (ℓ ...)])

(test-equal
 (term (in-scope-lifetimes [(a [b c]) (d [e f])]))
 (term [a d]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; loaned-paths

(define-metafunction Patina-typing
  loaned-paths : £ -> lvs
  
  [(loaned-paths [(ℓ mq lv) ...]) (lv ...)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; owning-path srs ty lv -> lv
;;
;; Returns the largest owned prefix of `lv`. For example, if `lv` is
;; `x.f`, then it would return `x.f`. If `lv` were `(*x).f`, then the
;; result would either be `(*x).f` if `x` is an owned pointer (i.e.,
;; `~T`), or `x` if `x` is a reference (e.g., `&T`).

(define-metafunction Patina-typing
  owning-path : srs T lv -> lv
  
  [(owning-path srs T lv)
   (owning-path1 srs T lv lv)]
  
  )

;; Helper function. Second argument is the maximal owned path found so
;; far.
(define-metafunction Patina-typing
  owning-path1 : srs T lv lv -> lv
  
  [(owning-path1 srs T x lv_m) lv_m]
  
  [(owning-path1 srs T (lv_0 · f) lv_m)
   (owning-path1 srs T lv_0 lv_m)]
  
  [(owning-path1 srs T (lv_0 @ lv_1) lv_m)
   (owning-path1 srs T lv_0 lv_m)]
  
  [(owning-path1 srs T (* lv_0) lv_m)
   (owning-path1 srs T lv_0 lv_m)
   (where (~ ty) (lvtype srs T lv_0))]
  
  [(owning-path1 srs T (* lv_0) lv_m)
   (owning-path1 srs T lv_0 lv_0)
   (where (& ℓ mq ty) (lvtype srs T lv_0))]
  
  )

(test-equal
 (term (owning-path ,test-srs ,test-T (* (b · 1))))
 (term (b · 1)))

(test-equal
 (term (owning-path ,test-srs ,test-T (* r)))
 (term (* r)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; prefix-paths lv
;;
;; Given something like (*x).f, yields: [(*x).f, *x, x]

(define-metafunction Patina-typing
  prefix-paths : lv -> lvs
  
  [(prefix-paths x)
   [x]
   ]
  
  [(prefix-paths (lv · f))
   [(lv · f) lv_1 ...]
   (where [lv_1 ...] (prefix-paths lv))
   ]
  
  [(prefix-paths (lv_b @ lv_i))
   [(lv_b @ lv_i) lv_1 ...]
   (where [lv_1 ...] (prefix-paths lv))
   ]
  
  [(prefix-paths (* lv))
   [(* lv) lv_1 ...]
   (where [lv_1 ...] (prefix-paths lv))
   ]
  
  )

(test-equal
 (term (prefix-paths (* (b · 1))))
 (term [(* (b · 1)) (b · 1) b]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; mut-loans £

(define-metafunction Patina-typing
  mut-loans : £ -> £
  
  [(mut-loans [])
   []]
  
  [(mut-loans [(ℓ imm lv) loan ...])
   (mut-loans [loan ...])]
  
  [(mut-loans [(ℓ mut lv) loan ...])
   [(ℓ mut lv) loan_1 ...]
   (where [loan_1 ...] (mut-loans [loan ...]))]
  
  )

(test-equal
 (term (mut-loans [(a imm x) (b mut y) (c imm z) (d mut a)]))
 (term [(b mut y) (d mut a)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; paths-intersect lv lv
;;
;; We say that two paths intersect if one is a subpath of the other.
;; So, for example, x.y and x intersect, but x.y and x.z do not.

(define-metafunction Patina-typing
  paths-intersect : lv lv -> boolean
  
  [(paths-intersect lv_1 lv_2)
   (∨ (∈ lv_1 (prefix-paths lv_2))
      (∈ lv_2 (prefix-paths lv_1)))]
  )

(test-equal
 (term (paths-intersect (x · 0) (x · 1)))
 #f)

(test-equal
 (term (paths-intersect (x · 0) x))
 #t)

(test-equal
 (term (paths-intersect x (x · 0)))
 #t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; path-is-prefix-of lv_1 lv_2
;;
;; x is a prefix of x, x.y, and *x. Got it?

(define-metafunction Patina-typing
  path-is-prefix-of : lv lv -> boolean
  
  [(path-is-prefix-of lv_1 lv_2)
   (∈ lv_1 (prefix-paths lv_2))]
  )

(test-equal
 (term (path-is-prefix-of (x · 0) (x · 1)))
 #f)

(test-equal
 (term (path-is-prefix-of (x · 0) x))
 #f)

(test-equal
 (term (path-is-prefix-of x x))
 #t)

(test-equal
 (term (path-is-prefix-of x (* x)))
 #t)

(test-equal
 (term (path-is-prefix-of x (x · 1)))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lv-shallowly-initialized
;;
;; Holds if the lvalue lv is initialized, though some subpaths may not be

(define-metafunction Patina-typing
  lv-shallowly-initialized : Δ lv -> boolean
  
  [(lv-shallowly-initialized Δ lv)
   (∄ [(∈ lv_b Δ) ...])
   (where [lv_b ...] (prefix-paths lv))]
  )

(test-equal
 (term (lv-shallowly-initialized [] p))
 #t)

(test-equal
 (term (lv-shallowly-initialized [] (* p)))
 #t)

(test-equal
 (term (lv-shallowly-initialized [p] p))
 #f)

(test-equal
 (term (lv-shallowly-initialized [(* p)] p))
 #t)

(test-equal
 (term (lv-shallowly-initialized [p] (* p)))
 #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lv-deeply-initialized Δ lv
;;
;; Hold if the lvalue lv is fully initialized.

(define-metafunction Patina-typing
  lv-deeply-initialized : Δ lv -> boolean
  
  [(lv-deeply-initialized [lv_Δ ...] lv)
   (∄ [(paths-intersect lv lv_Δ) ...])]
  )

(test-equal
 (term (lv-deeply-initialized [] p))
 #t)

(test-equal
 (term (lv-deeply-initialized [] (* p)))
 #t)

(test-equal
 (term (lv-deeply-initialized [p] p))
 #f)

(test-equal
 (term (lv-deeply-initialized [(* p)] p))
 #f)

(test-equal
 (term (lv-deeply-initialized [p] (* p)))
 #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lv-dropped-if-necessary
;;
;; True if lv has been dropped or does not need to be dropped.

(define-judgment-form
  Patina-typing
  #:mode     (lv-dropped-if-necessary I   I I I )
  #:contract (lv-dropped-if-necessary srs T Δ lv)
  
  [(side-condition (∈ lv Δ))
   --------------------------------------------------
   (lv-dropped-if-necessary srs T Δ lv)]
  
  [(where (struct s ℓs) (lvtype srs T lv))
   (where [f ...] (field-names srs s ℓs))
   (lv-dropped-if-necessary srs T Δ (lv · f)) ...
   --------------------------------------------------
   (lv-dropped-if-necessary srs T Δ lv)]
  
  [(where ty (lvtype srs T lv))
   (side-condition (¬ (ty-needs-drop srs ty)))
   --------------------------------------------------
   (lv-dropped-if-necessary srs T Δ lv)]
  
  )

;; owned pointer and it is not dropped
(test-equal
 (judgment-holds (lv-dropped-if-necessary ,test-srs ,test-ty-T [] owned-B))
 #f)

;; this field has type int
(test-equal
 (judgment-holds (lv-dropped-if-necessary ,test-srs ,test-ty-T [] ((* owned-B) · 0)))
 #t)

;; none of the fields of struct B require drop
(test-equal
 (judgment-holds (lv-dropped-if-necessary ,test-srs ,test-ty-T [] (* owned-B)))
 #t)

;; but struct E's fields do
(test-equal
 (judgment-holds (lv-dropped-if-necessary ,test-srs ,test-ty-T [] (* owned-E)))
 #f)
(test-equal
 (judgment-holds (lv-dropped-if-necessary ,test-srs ,test-ty-T [((* owned-E) · 0)] (* owned-E)))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; initialize-lv Δ lv
;;
;; Returns a modified Δ in which lv is initialized

(define-metafunction Patina-typing
  initialize-lv : Δ lv -> Δ
  
  [(initialize-lv Δ lv)
   (if-true [lv_Δ ...]
            [(¬ (path-is-prefix-of lv lv_Δ)) ...])
   (where [lv_Δ ...] Δ)
   ]  
  
  )

(test-equal
 (term (initialize-lv [((* p) · 1)] p))
 (term []))

(test-equal
 (term (initialize-lv [((* p) · 1)] (* p)))
 (term []))

(test-equal
 (term (initialize-lv [((* p) · 1)] ((* p) · 2)))
 (term [((* p) · 1)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lifetime-in-scope Λ ℓ
;;
;; Holds if the lifetime ℓ is in scope

(define-judgment-form
  Patina-typing
  #:mode     (lifetime-in-scope I I)
  #:contract (lifetime-in-scope Λ ℓ)
  
  [--------------------------------------------------
   (lifetime-in-scope Λ static)]
  
  [(side-condition (∈ ℓ (in-scope-lifetimes Λ)))
   --------------------------------------------------
   (lifetime-in-scope Λ ℓ)]
  
  )

(test-equal
 (judgment-holds (lifetime-in-scope [(a []) (b [])] a))
 #t)

(test-equal
 (judgment-holds (lifetime-in-scope [(a []) (b [])] b))
 #t)

(test-equal
 (judgment-holds (lifetime-in-scope [(a []) (b [])] c))
 #f)

(test-equal
 (judgment-holds (lifetime-in-scope [] static))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ty-bound-by-lifetime Λ ℓ ty
;;
;; If this judgement holds, then the type `ty` is bound by the
;; lifetime ℓ.
;;
;; FIXME

(define-judgment-form
  Patina-typing
  #:mode     (ty-bound-by-lifetime I I I )
  #:contract (ty-bound-by-lifetime Λ ℓ ty)
  
  [--------------------------------------------------
   (ty-bound-by-lifetime Λ ℓ ty)]
  
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; unencumbered £ lv
;;
;; True if lv has not been loaned out.

(define-judgment-form
  Patina-typing
  #:mode     (unencumbered I I )
  #:contract (unencumbered £ lv)
  
  [(side-condition (∉ lv (loaned-paths £)))
   --------------------------------------------------
   (unencumbered £ lv)]
  
  )

(test-equal
 (judgment-holds (unencumbered [(a imm x)] y))
 #t)

(test-equal
 (judgment-holds (unencumbered [(a imm x)] x))
 #f)

(test-equal
 (judgment-holds (unencumbered [(a imm x)] (* x)))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; owned-path srs T lv
;;
;; Holds if the path `lv` is an *owned path*.

(define-judgment-form
  Patina-typing
  #:mode     (owned-path I   I I )
  #:contract (owned-path srs T lv)
  
  [(where lv (owning-path srs T lv))
   --------------------------------------------------
   (owned-path srs T lv)]
  
  )

(test-equal
 (judgment-holds (owned-path ,test-srs ,test-T (* (b · 1))))
 #f)

(test-equal
 (judgment-holds (owned-path ,test-srs ,test-T (b · 1)))
 #t)

(test-equal
 (judgment-holds (owned-path ,test-srs ,test-T (* r)))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; paths-restricted-by-loans
;;
;; If a loan affects the lvalue `lv`, this function returns a set of
;; paths for `lv` that are *restricted* as a result. A path is
;; restricted if accessing it would violate the terms of the loan.
;;
;; More concretely, for a mutable loan of `lv`, `restricted-paths lv`
;; yields the set of paths that cannot be read or written as a result.
;; This includes not only `lv` itself but base paths of `lv`, because
;; reading those paths would either copy `lv` (as part of a larger
;; copy) or else create a second path to the same memory that was
;; borrowed. Similar concerns hold for writing.

(define-metafunction Patina-typing
  paths-restricted-by-loans : srs T £ -> lvs
  
  [(paths-restricted-by-loans srs T [(ℓ mq lv) ...])
   ,(append* (term [(paths-restricted-by-loan-of srs T lv) ...]))])

(define-metafunction Patina-typing
  paths-restricted-by-loan-of : srs T lv -> lvs
  
  [(paths-restricted-by-loan-of srs T x)
   [x]
   ]
  
  [(paths-restricted-by-loan-of srs T (lv · f))
   [(lv · f) lv_1 ...]
   (where [lv_1 ...] (paths-restricted-by-loan-of srs T lv))
   ]
  
  [(paths-restricted-by-loan-of srs T (lv_a @ lv_i))
   [(lv_a @ lv_i) lv_1 ...]
   (where [lv_1 ...] (paths-restricted-by-loan-of srs T lv_a))
   ]
  
  [(paths-restricted-by-loan-of srs T (* lv))
   [(* lv) lv_1 ...]
   (where (~ ty) (lvtype srs T lv))
   (where [lv_1 ...] (paths-restricted-by-loan-of srs T lv))
   ]
  
  ;; If we borrowed `*x` and `x` is a `&T`, that need not prevent us
  ;; from reading (or writing) `x`. I would eventually like to extend
  ;; this rule to handle writes to &mut borrowed lvalues too, but that
  ;; needs a bit more infrastructure and for time being I want to
  ;; model what rustc currently allows (or should allow).
  [(paths-restricted-by-loan-of srs T (* lv))
   [(* lv)]
   (where (& ℓ imm ty) (lvtype srs T lv))
   ]
  
  [(paths-restricted-by-loan-of srs T (* lv))
   [(* lv) lv_1 ...]
   (where (& ℓ mut ty) (lvtype srs T lv))
   (where [lv_1 ...] (paths-restricted-by-loan-of srs T lv))
   ]
  
  )

(test-equal
 (term (paths-restricted-by-loan-of ,test-srs ,test-T (* (b · 1))))
 (term [(* (b · 1)) (b · 1) b]))

(test-equal
 (term (paths-restricted-by-loan-of ,test-srs ,test-T (* q)))
 (term [(* q)]))

(test-equal
 (term (paths-restricted-by-loans ,test-srs ,test-T [(a imm (* q))
                                                     (a mut (* (b · 1)))]))
 (term [(* q) (* (b · 1)) (b · 1) b]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; path-unique-for srs T Λ ℓ lv
;;
;; Holds if the path `lv` is a *unique path* during the lifetime ℓ.
;; This means that, during the lifetime ℓ, `lv` is the only
;; *accessible* path that would evaluate to that particular address.

(define-judgment-form
  Patina-typing
  #:mode     (reject-x I)
  #:contract (reject-x any)
  
  [--------------------------------------------------
   (reject-x debug-me)]
  
  )

(define-judgment-form
  Patina-typing
  #:mode     (path-unique-for I   I I I I )
  #:contract (path-unique-for srs T Λ ℓ lv)
  
  [--------------------------------------------------
   (path-unique-for srs T Λ ℓ x)]
  
  [(path-unique-for srs T Λ ℓ lv)
   --------------------------------------------------
   (path-unique-for srs T Λ ℓ (lv · f))]
  
  [(path-unique-for srs T Λ ℓ lv)
   --------------------------------------------------
   (path-unique-for srs T Λ ℓ (lv @ lv_1))]
  
  [(where (~ ty) (lvtype srs T lv))
   (path-unique-for srs T Λ ℓ lv)
   --------------------------------------------------
   (path-unique-for srs T Λ ℓ (* lv))]
  
  [(where (& ℓ_lv mut ty) (lvtype srs T lv))
   (lifetime-≤ Λ ℓ ℓ_lv)
   (path-unique-for srs T Λ ℓ lv)
   --------------------------------------------------
   (path-unique-for srs T Λ ℓ (* lv))]
  
  )

(test-equal
 (judgment-holds (path-unique-for ,test-srs ,test-ty-T ,test-ty-Λ
                                  b r-imm-B))
 #t)

(test-equal
 (judgment-holds (path-unique-for ,test-srs ,test-ty-T ,test-ty-Λ
                                  b (* ((* r-imm-B) · 1))))
 #f)

(test-equal
 (judgment-holds (path-unique-for ,test-srs ,test-ty-T ,test-ty-Λ
                                  b (* ((* r-mut-B) · 1))))
 #t)

(test-equal
 (judgment-holds (path-unique-for ,test-srs ,test-ty-T ,test-ty-Λ
                                  a (* ((* r-mut-B) · 1))))
 #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; path-freezable-for srs T Λ ℓ lv
;;
;; Holds if the path `lv` is a *freezable path* during the lifetime ℓ.
;; I am not quite sure how best to phrase this predicate in English.
;; Roughly speaking, the path-freezable-for predicte guarantees that the
;; memory which `lv` evaluates to will not be mutated during the
;; lifetime ℓ, assuming that the path `lv` is not itself assigned to
;; (if that is even possible). Often this corresponds to the underlying
;; memory referenced by `lv` but not always.
;;
;; Here are some interesting and representative examples:
;;
;; 1. `fn foo(x: &'a &'b mut T) -> &'a T { &**x }`
;;
;;     This example is legal because the path **x is freezable-for the
;;     lifetime 'a. If however the return type were `&'b T`, the
;;     example would be an error, because `**x` is not freezable-for
;;     'b. This is true *even though* we know that the memory will not yet
;;     be freed.
;;
;;     The reason is that, so long as the `&mut` *x is considered
;;     aliased, it cannot be changed. But that alias expires after 'a,
;;     and hence the memory in 'b would be considered mutable
;;     again.
;;
;; 2. `fn foo(x: &'a mut T) -> &'a T { &*x }`
;;
;;     In this case, the path `*x` is freezable-for the lifetime `'a`.
;;     The reason is that `x` is the only pointer that can mutate `*x`
;;     during the lifetime `'a`, and hence if we freeze `*x` we can be
;;     sure that the memory will not change until after `'a`.
;;
;; 3. `fn foo() -> &'a int { let x = 3; &x }`
;;
;;     Naturally, this case yields an error, but NOT because of
;;     freezable-for. This is crucial to the previous two examples, in
;;     fact. The idea here is that while the memory pointed at by `x`
;;     isn't valid for the entire lifetime 'a, if we ignore memory
;;     reuse, we can still say that it won't be assigned to. I'm not
;;     sure how best to express this part in English. Maybe this rule
;;     can be made more tidy. In any case, there is another predicate
;;     `path-outlives` that would catch this sort of error.

(define-judgment-form
  Patina-typing
  #:mode     (path-freezable-for I   I I I I )
  #:contract (path-freezable-for srs T Λ ℓ lv)
  
  [--------------------------------------------------
   (path-freezable-for srs T Λ ℓ x)]
  
  [(path-freezable-for srs T Λ ℓ lv)
   --------------------------------------------------
   (path-freezable-for srs T Λ ℓ (lv · f))]
  
  [(path-freezable-for srs T Λ ℓ lv)
   --------------------------------------------------
   (path-freezable-for srs T Λ ℓ (lv @ lv_1))]
  
  [(where (~ ty) (lvtype srs T lv))
   (path-freezable-for srs T Λ ℓ lv)
   --------------------------------------------------
   (path-freezable-for srs T Λ ℓ (* lv))]
  
  [(where (& ℓ_lv mut ty) (lvtype srs T lv))
   (lifetime-≤ Λ ℓ ℓ_lv)
   (path-freezable-for srs T Λ ℓ lv)
   --------------------------------------------------
   (path-freezable-for srs T Λ ℓ (* lv))]
  
  [(where (& ℓ_lv imm ty) (lvtype srs T lv))
   (lifetime-≤ Λ ℓ ℓ_lv)
   --------------------------------------------------
   (path-freezable-for srs T Λ ℓ (* lv))]
  
  )

(test-equal
 (judgment-holds (path-freezable-for ,test-srs ,test-ty-T ,test-ty-Λ
                                     b r-imm-B))
 #t)

(test-equal
 (judgment-holds (path-freezable-for ,test-srs ,test-ty-T ,test-ty-Λ
                                     b (* ((* r-imm-B) · 1))))
 #t)

(test-equal
 (judgment-holds (path-freezable-for ,test-srs ,test-ty-T ,test-ty-Λ
                                     b (* ((* r-mut-B) · 1))))
 #t)

(test-equal
 (judgment-holds (path-freezable-for ,test-srs ,test-ty-T ,test-ty-Λ
                                     a (* ((* r-mut-B) · 1))))
 #f)

(test-equal
 (judgment-holds (path-freezable-for ,test-srs ,test-ty-T ,test-ty-Λ
                                     a (* owned-B)))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; can-access

(define-judgment-form
  Patina-typing
  #:mode     (can-access I   I I I I I )
  #:contract (can-access srs T Λ £ Δ lv)
  
  [;; Data must be initialized:
   (side-condition (lv-deeply-initialized Δ lv))
   
   ;; The path lv cannot be restricted by a loan:
   ;;
   ;; This covers cases like these:
   ;;
   ;;    let x = &mut a.b.c; // restricts a, a.b, and a.b.c
   ;;    a.b = ...;          // would overwrite c as part
   ;;
   ;;    let x = &a.b.c;     // restricts a, a.b, and a.b.c
   ;;    a.b = ...;          // would overwrite c as part
   ;;
   ;;    let x = &mut a.b.c; // restricts a, a.b, and a.b.c
   ;;    let y = a.b;        // would read c as part
   (where [lv_r ...] (paths-restricted-by-loans srs T £_l))
   (side-condition (∉ lv [lv_r ...]))
   
   ;; Neither the path lv nor any base path of lv can be borrowed:
   ;;
   ;; This covers cases like this:
   ;;
   ;;    let x = &mut a;
   ;;    a.b = ...;          // would overwrite part of a
   ;;
   ;;    let x = &a;
   ;;    a.b = ...;          // would overwrite part of a
   ;;
   ;;    let x = &mut a;
   ;;    let y = a.b;        // would read part of a
   (where [lv_b ...] (prefix-paths lv))
   (unencumbered £_l lv_b) ...
   --------------------------------------------------
   (can-access srs T Λ £_l Δ lv)]
  
  )

;; can't access loaned variable
(test-equal
 (judgment-holds (can-access ,test-srs ,test-ty-T ,test-ty-Λ
                             [(a mut r-imm-B)] [] r-imm-B))
 #f)

;; can't access variable r-mut-B when (* r-mut-B) was loaned
(test-equal
 (judgment-holds (can-access ,test-srs ,test-ty-T ,test-ty-Λ
                             [(a mut (* r-mut-B))] [] r-mut-B))
 #f)

;; can't access variable (* r-mut-B) when r-mut-B was loaned
(test-equal
 (judgment-holds (can-access ,test-srs ,test-ty-T ,test-ty-Λ
                             [(a mut r-mut-B)] [] (* r-mut-B)))
 #f)

;; accessing (*r-mut-B).1 when (*r-mut-B).0 was loaned is ok
(test-equal
 (judgment-holds (can-access ,test-srs ,test-ty-T ,test-ty-Λ
                             [(a mut ((* r-mut-B) · 0))] []
                             ((* r-mut-B) · 1)))
 #t)

;; can't access uninitialized variable
(test-equal
 (judgment-holds (can-access ,test-srs ,test-ty-T ,test-ty-Λ
                             [(a mut r-imm-B)] [r-mut-B] r-mut-B))
 #f)

;; can't access uninitialized referent
(test-equal
 (judgment-holds (can-access ,test-srs ,test-ty-T ,test-ty-Λ
                             [] [(* owned-B)] (* owned-B)))
 #f)

;; can't access referent of uninitialized pointer
(test-equal
 (judgment-holds (can-access ,test-srs ,test-ty-T ,test-ty-Λ
                             [] [owned-B] (* owned-B)))
 #f)

;; otherwise ok
(test-equal
 (judgment-holds (can-access ,test-srs ,test-ty-T ,test-ty-Λ
                             [(a mut r-imm-B)] [] r-mut-B))
 #t)

(test-equal
 (judgment-holds (can-access ,test-srs ,test-ty-T ,test-ty-Λ
                             [] [] (* owned-B)))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; can-read-from

(define-judgment-form
  Patina-typing
  #:mode     (can-read-from I   I I I I I )
  #:contract (can-read-from srs T Λ £ Δ lv)
  
  [;; Only mutable loans prevent reads:
   (can-access srs T Λ (mut-loans £) Δ lv)
   --------------------------------------------------
   (can-read-from srs T Λ £ Δ lv)]
  
  )

;; imm loans do not prevent reads
(test-equal
 (judgment-holds (can-read-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [(a imm r-imm-B)] [] r-imm-B))
 #t)

;; but mut loans do
(test-equal
 (judgment-holds (can-read-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [(a mut r-imm-B)] [] r-imm-B))
 #f)

;; read from (* owned-B)
(test-equal
 (judgment-holds (can-read-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [] [] (* owned-B)))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; can-write-to

(define-judgment-form
  Patina-typing
  #:mode     (can-write-to I   I I I I I )
  #:contract (can-write-to srs T Λ £ Δ lv)
  
  [;; All loans prevent writes:
   (can-access srs T Λ £ Δ lv)
   --------------------------------------------------
   (can-write-to srs T Λ £ Δ lv)]
  
  )

;; imm loans do prevent writes
(test-equal
 (judgment-holds (can-write-to ,test-srs ,test-ty-T ,test-ty-Λ
                               [(a imm r-imm-B)] [] r-imm-B))
 #f)

;; as do mut loans
(test-equal
 (judgment-holds (can-write-to ,test-srs ,test-ty-T ,test-ty-Λ
                               [(a mut r-imm-B)] [] r-imm-B))
 #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; can-move-from

(define-judgment-form
  Patina-typing
  #:mode     (can-move-from I   I I I I I )
  #:contract (can-move-from srs T Λ £ Δ lv)
  
  [;; Can only move from things we own:
   (owned-path srs T lv)
   
   ;; Otherwise same as write:
   (can-write-to srs T Λ £ Δ lv) 
   --------------------------------------------------
   (can-move-from srs T Λ £ Δ lv)]
  
  )

;; imm loans prevent moves
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [(b imm r-imm-B)] [] r-imm-B))
 #f)
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [(b imm owned-B)] [] (* owned-B)))
 #f)
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [(b imm (* owned-B))] [] (* owned-B)))
 #f)
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [(b imm ((* owned-B) · 0))] [] (* owned-B)))
 #f)
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [(b imm owned-B)] [] (* owned-B)))
 #f)

;; as do mut loans
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [(b mut r-imm-B)] [] r-imm-B))
 #f)
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [(b mut owned-B)] [] (* owned-B)))
 #f)

;; otherwise ok
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [] [] r-imm-B))
 #t)
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [] [] owned-B))
 #t)

;; but can't move from deref of borrowed pointer
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [] [] (* r-imm-B)))
 #f)

;; can move from deref of owned pointer
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [] [] (* owned-B)))
 #t)

;; unless uninitialized
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [] [owned-B] (* owned-B)))
 #f)
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [] [(* owned-B)] (* owned-B)))
 #f)
(test-equal
 (judgment-holds (can-move-from ,test-srs ,test-ty-T ,test-ty-Λ
                                [] [((* owned-B) · 1)] (* owned-B)))
 #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; can-init

(define-judgment-form
  Patina-typing
  #:mode     (can-init I   I I I I )
  #:contract (can-init srs T Λ Δ lv)
  
  [(side-condition (∈ x Δ))
   --------------------------------------------------
   (can-init srs T Λ Δ x)]
  
  [(side-condition (lv-shallowly-initialized Δ lv))
   (side-condition (∈ (lv · f) Δ))
   --------------------------------------------------
   (can-init srs T Λ Δ (lv · f))]
  
  [(side-condition (lv-shallowly-initialized Δ lv))
   (side-condition (∈ (* lv) Δ))
   (where (~ ty) (lvtype srs T lv))
   --------------------------------------------------
   (can-init srs T Λ Δ (* lv))]
  
  )

;; cannot initiatialize something already written
(test-equal
 (judgment-holds (can-init ,test-srs ,test-ty-T ,test-ty-Λ
                           [] r-mut-B))
 #f)

;; cannot initiatialize borrowed data
(test-equal
 (judgment-holds (can-init ,test-srs ,test-ty-T ,test-ty-Λ
                           [] (* r-mut-B)))
 #f)

;; but can initialize something that is deinitialized
(test-equal
 (judgment-holds (can-init ,test-srs ,test-ty-T ,test-ty-Λ
                           [r-imm-B] r-imm-B))
 #t)

(test-equal
 (judgment-holds (can-init ,test-srs ,test-ty-T ,test-ty-Λ
                           [(* owned-B)] (* owned-B)))
 #t)

(test-equal
 (judgment-holds (can-init ,test-srs ,test-ty-T ,test-ty-Λ
                           [((* owned-B) · 1)] ((* owned-B) · 1)))
 #t)

;; as long as the base path is initialized

(test-equal
 (judgment-holds (can-init ,test-srs ,test-ty-T ,test-ty-Λ
                           [owned-B (* owned-B)] (* owned-B)))
 #f)

(test-equal
 (judgment-holds (can-init ,test-srs ,test-ty-T ,test-ty-Λ
                           [owned-B ((* owned-B) · 1)] ((* owned-B) · 1)))
 #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; path-valid-for-lifetime
;;
;; Holds if the memory directly referenced by `lv`
;; will outlive `ℓ`.

(define-judgment-form
  Patina-typing
  #:mode     (path-valid-for-lifetime I   I I I  I I )
  #:contract (path-valid-for-lifetime srs T Λ VL ℓ lv)
  
  [(where ℓ_x ,(get* (term x) (term VL)))
   (lifetime-≤ Λ ℓ ℓ_x)
   --------------------------------------------------
   (path-valid-for-lifetime srs T Λ VL ℓ x)]
  
  [(path-valid-for-lifetime srs T Λ VL ℓ lv)
   --------------------------------------------------
   (path-valid-for-lifetime srs T Λ VL ℓ (lv · f))]
  
  [(path-valid-for-lifetime srs T Λ VL ℓ lv)
   --------------------------------------------------
   (path-valid-for-lifetime srs T Λ VL ℓ (lv @ lv_i))]
  
  [(where (~ ty) (lvtype srs T lv))
   (path-valid-for-lifetime srs T Λ VL ℓ lv)
   --------------------------------------------------
   (path-valid-for-lifetime srs T Λ VL ℓ (* lv))]
  
  [(where (& ℓ_lv mq ty) (lvtype srs T lv))
   (lifetime-≤ Λ ℓ ℓ_lv)
   --------------------------------------------------
   (path-valid-for-lifetime srs T Λ VL ℓ (* lv))]
  
  )

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  static (* ((* r-mut-B) · 1))))
 #t)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  static r-mut-B))
 #f)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  a (* ((* r-mut-B) · 1))))
 #t)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  static (* r-mut-B)))
 #f)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  a (* r-mut-B)))
 #f)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  b (* r-mut-B)))
 #t)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  b owned-B))
 #t)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  b (* owned-B)))
 #t)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  b ((* owned-B) · 0)))
 #t)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  p0 (* owned-B)))
 #f)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  p0 (* owned-B)))
 #f)

(test-equal
 (judgment-holds (path-valid-for-lifetime
                  ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                  p0 ((* owned-B) · 0)))
 #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; path-outlives

(define-judgment-form
  Patina-typing
  #:mode     (path-outlives I   I I I  I I )
  #:contract (path-outlives srs T Λ VL ℓ lv)
  
  [;; At present, we require that the borrow be for some lifetime that
   ;; is in scope. I'd like to lift this requirement in the future,
   ;; though I can't recall just what gets more complicated as a
   ;; result!
   (lifetime-in-scope Λ ℓ)
   
   ;; Determine from the path whether we be sure that the path outlives ℓ.
   (path-valid-for-lifetime srs T Λ VL ℓ lv)
   
   ;; Data cannot have a lifetime shorter than the loan ℓ.
   ;;
   ;; FIXME I feel like this check is unnecessary and implied by other
   ;; requirements. In other words, the memory has an ultimate local
   ;; variable in a block with lifetime ℓ, and presumably we wouldn't
   ;; allow that owner to gain access to data with some lifetime less
   ;; than ℓ. (Ah, perhaps this is what becomes complicated if we want
   ;; to allow data to be borrowed for a lifetime not currently in
   ;; scope, actually.)
   (where ty (lvtype srs T lv))
   (ty-bound-by-lifetime Λ ℓ ty)
   --------------------------------------------------
   (path-outlives srs T Λ VL ℓ lv)]
  
  )

(test-equal
 (judgment-holds (path-outlives ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                                b (* owned-B)))
 #t)

(test-equal
 (judgment-holds (path-outlives ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL
                                a (* owned-B)))
 #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; use-lv-ok and use-lvs-ok

(define-judgment-form
  Patina-typing
  #:mode     (use-lv-ok I   I I I I I  O  O)
  #:contract (use-lv-ok srs T Λ £ Δ lv ty Δ)
  
  ;; If `lv` is POD, it is not moved but rather copied.
  [(where ty (lvtype srs T lv))
   (can-read-from srs T Λ £ Δ lv)
   (side-condition (ty-is-pod srs ty))
   --------------------------------------------------
   (use-lv-ok srs T Λ £ Δ lv ty Δ)]
  
  ;; Otherwise, each use deinitializes the value:
  [(where ty (lvtype srs T lv))
   (can-move-from srs T Λ £ Δ lv)
   (side-condition (¬ (ty-is-pod srs ty)))
   --------------------------------------------------
   (use-lv-ok srs T Λ £ Δ lv ty (∪ Δ [lv]))]
  
  )

;; using a ~ or &mut pointer kills that pointer (resp. referent)
(test-equal
 (judgment-holds (use-lv-ok ,test-srs ,test-ty-T ,test-ty-Λ []
                            []
                            owned-B ty Δ)
                 (ty / Δ))
 (term [((~ (struct B (static))) / [owned-B])]))
(test-equal
 (judgment-holds (use-lv-ok ,test-srs ,test-ty-T ,test-ty-Λ []
                            []
                            (* owned-B) ty Δ)
                 (ty / Δ))
 (term [((struct B (static)) / [(* owned-B)])]))
(test-equal
 (judgment-holds (use-lv-ok ,test-srs ,test-ty-T ,test-ty-Λ []
                            []
                            ((* owned-B) · 1) ty Δ)
                 (ty / Δ))
 (term [((& static mut int) / [((* owned-B) · 1)])]))

;; naturally it must be initialized
(test-equal
 (judgment-holds (use-lv-ok ,test-srs ,test-ty-T ,test-ty-Λ []
                            [owned-B]
                            owned-B ty Δ)
                 (ty / Δ))
 (term []))

;; using an int doesn't kill anything
(test-equal
 (judgment-holds (use-lv-ok ,test-srs ,test-ty-T ,test-ty-Λ []
                            []
                            ((* owned-B) · 0) ty Δ)
                 (ty / Δ))
 (term [(int / [])]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; use-lvs-ok -- uses a sequence of lvalues in order

(define-judgment-form
  Patina-typing
  #:mode     (use-lvs-ok I   I I I I I   O   O)
  #:contract (use-lvs-ok srs T Λ £ Δ lvs tys Δ)
  
  [--------------------------------------------------
   (use-lvs-ok srs T Λ £ Δ [] [] Δ)]
  
  [(use-lv-ok srs T Λ £ Δ lv_0 ty_0 Δ_0)
   (use-lvs-ok srs T Λ £ Δ_0 [lv_1 ...] [ty_1 ...] Δ_1)
   --------------------------------------------------
   (use-lvs-ok srs T Λ £ Δ [lv_0 lv_1 ...] [ty_0 ty_1 ...] Δ_1)]
  
  )

(test-equal
 (judgment-holds (use-lvs-ok ,test-srs ,test-ty-T ,test-ty-Λ []
                             []
                             [owned-B] tys Δ)
                 (tys / Δ))
 (term [([(~ (struct B (static)))] / [owned-B])]))

(test-equal
 (judgment-holds (use-lvs-ok ,test-srs ,test-ty-T ,test-ty-Λ []
                             []
                             [owned-B r-imm-B] tys Δ)
                 (tys / Δ))
 (term [([(~ (struct B (static)))
          (& b imm (struct B (static)))]
         / [owned-B])]))

;; using a ~ pointer kills both that pointer and any owned subpaths
(test-equal
 (judgment-holds (use-lvs-ok ,test-srs ,test-ty-T ,test-ty-Λ []
                             []
                             [owned-B (* owned-B)] tys Δ)
                 (tys / Δ))
 (term []))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; expire-loans

(define-metafunction Patina-typing
  expire-loans : ℓ £ -> £
  
  [(expire-loans ℓ_e [(ℓ mq lv) ...])
   (if-true [(ℓ mq lv) ...]
            [(lifetime-≠ ℓ ℓ_e) ...])]
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; expire-paths

(define-metafunction Patina-typing
  expire-paths : lvs Δ -> Δ
  
  [(expire-paths lvs [lv_Δ ...])
   (if-true [lv_Δ ...]
            [(should-expire-path lvs lv_Δ) ...])]
  )

(define-metafunction Patina-typing
  should-expire-path : lvs lv -> boolean
  
  [(should-expire-path [lv_e ...] lv)
   (∄ [(path-is-prefix-of lv_e lv) ...])]
  )

(test-equal
 (term (expire-paths [x] [(* x) x (* y) y]))
 (term [(* y) y]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rv-ok

(define-judgment-form
  Patina-typing
  #:mode     (rv-ok I   I I I  I I I  O  O O)
  #:contract (rv-ok srs T Λ VL £ Δ rv ty £ Δ)
  
  ;; lv
  [(use-lv-ok srs T Λ £ Δ lv ty_out Δ_out)
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ lv ty_out £ Δ_out)]
  
  ;; & ℓ imm lv
  [(where ty (lvtype srs T lv))
   (can-read-from srs T Λ £ Δ lv)
   (path-freezable-for srs T Λ ℓ lv)
   (path-outlives srs T Λ VL ℓ lv)
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ (& ℓ imm lv) (& ℓ imm ty) (∪ £ [(ℓ imm lv)]) Δ)]
  
  ;; & ℓ mut lv
  [(where ty (lvtype srs T lv))
   (can-write-to srs T Λ £ Δ lv)
   (path-unique-for srs T Λ ℓ lv)
   (path-outlives srs T Λ VL ℓ lv)
   (where ty_rv (& ℓ mut ty))
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ (& ℓ mut lv) ty_rv (∪ £ [(ℓ mut lv)]) Δ)]
  
  ;; struct s ℓs [lv ...]
  [(where [ty_f ...] (field-tys srs s [ℓ ...]))
   (use-lvs-ok srs T Λ £ Δ [lv ...] [ty_a ...] Δ_a)
   (lifetime-in-scope Λ ℓ) ...
   (subtype Λ ty_a ty_f) ...
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ (struct s [ℓ ...] [lv ...]) (struct s [ℓ ...]) £ Δ_a)]
  
  ;; int
  [--------------------------------------------------
   (rv-ok srs T Λ VL £ Δ number int £ Δ)]
  
  ;; lv + lv
  [(use-lvs-ok srs T Λ £ Δ [lv_1 lv_2] [int int] Δ)
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ (lv_1 + lv_2) int £ Δ)]
  
  ;; (new lv)
  [(use-lv-ok srs T Λ £ Δ lv ty Δ_1)
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ (new lv) (~ ty) £ Δ_1)]
  
  ;; (Some lv)
  [(use-lv-ok srs T Λ £ Δ lv ty Δ_1)
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ (Some lv) (Option ty) £ Δ_1)]
  
  ;; (None ty)
  [;; check ty well-formed
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ (None ty) (Option ty) £ Δ)]
  
  ;; (vec ty lv ...)
  [;; check ty well-formed
   (where l (size [lv ...]))
   (use-lvs-ok srs T Λ £ Δ [lv ...] [ty_lv ...] Δ_1)
   (subtype Λ ty_lv ty) ...
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ (vec ty lv ...) (vec ty l) £ Δ_1)]
  
  ;; (vec-len lv ...)
  [(where (& ℓ imm (vec ty olen)) (lvtype srs T lv))
   (can-read-from srs T Λ £ Δ lv)
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ (vec-len lv) int £ Δ)]
  
  ;; (pack lv ty)
  [(use-lv-ok srs T Λ £ Δ lv ty Δ_1)
   --------------------------------------------------
   (rv-ok srs T Λ VL £ Δ (pack lv ty) ty £ Δ_1)]
  
  )

; Referencing a ~ pointer is a move
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [] [] owned-B ty £ Δ)
  (ty £ Δ))
 (term [((~ (struct B [static])) [] [owned-B])]))

; And illegal if it is borrowed.
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [(a imm owned-B)] [] owned-B ty £ Δ)
  (ty £ Δ))
 (term []))

; Test a simple, well-typed struct expression: `A { i }`
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [] [] (struct A [] [i]) ty £ Δ)
  (ty £ Δ))
 (term [((struct A []) [] [])]))

; Like previous, but with an invalid type for the field.
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [] [] (struct A [] [r-imm-B]) ty £ Δ)
  (ty £ Δ))
 (term []))

; Like previous, but with uninitialized i
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [] [i] (struct A [] [i]) ty £ Δ)
  (ty £ Δ))
 (term []))

; Struct B<'a> { i r-mut-int } -- consumes the r-mut-int
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (struct B [a] [i r-mut-int]) ty £ Δ)
  (ty £ Δ))
 (term [( (struct B [a]) [] [r-mut-int] )]))

; Struct B<'b> { i r-mut-int } -- same as previous
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (struct B [b] [i r-mut-int]) ty £ Δ)
  (ty £ Δ))
 (term [( (struct B [b]) [] [r-mut-int] )]))

; Struct B<'static> { i r-mut-int } -- lifetime error, 'static > 'a
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (struct B [static] [i r-mut-int]) ty £ Δ)
  (ty £ Δ))
 (term []))

;; test borrowing immutably when already borrowed
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [(a imm i)] []
         (& a imm i) ty £ Δ)
  (ty £ Δ))
 (term [((& a imm int) [(a imm i)] [])]))

;; test borrowing of deref of owned pointer
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (& b imm (* owned-B)) ty £ Δ)
  (ty £ Δ))
 (term [( (& b imm (struct B (static))) [(b imm (* owned-B))] [] )]))

;; test borrowing of deref of owned pointer when already borrowed
(test-equal
 (judgment-holds
  (rv-ok ,test-srs ,test-ty-T ,test-ty-Λ ,test-ty-VL [(b imm (* owned-B))] []
         (& b imm (* owned-B)) ty £ Δ)
  (ty £ Δ))
 (term [( (& b imm (struct B (static))) [(b imm (* owned-B))] [] )]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; join-after-match
;;
;; Given the state after the some and none branch of a match, produces
;; the final state in terms of what loans and deinitializations have
;; occured. Checks that both states are consistent in that they have
;; deinitialized the same paths.

(define-judgment-form
  Patina-typing
  ;                            initial   some    none    out
  ;                            +-----+   +---+   +---+   +-+
  ;                            |     |   |   |   |   |   | |
  #:mode     (join-after-match I   I I   I I I   I I I   O O)
  #:contract (join-after-match srs T x   T £ Δ   T £ Δ   £ Δ)
  
  [;; check that the some block drops x if necessary
   (lv-dropped-if-necessary srs T_some Δ_some x)
   
   ;; filter out x from the list of deinitialized paths
   ;; since it is out of scope after match
   (where Δ_some1 (expire-paths [x] Δ_some))
   
   ;; loans from both sides are still in scope
   (where £_match (∪ £_some £_none))
   
   ;; anything dropped on either side must be considered dropped afterwards
   (where Δ_match (∪ Δ_some1 Δ_none))
   
   ;; check that anything dropped afterwards is dropped on *both* sides
   (where [lv_match ...] Δ_match)
   (lv-dropped-if-necessary srs T Δ_some1 lv_match) ...
   (lv-dropped-if-necessary srs T Δ_none lv_match) ...
   --------------------------------------------------
   (join-after-match srs T x
                     T_some £_some Δ_some
                     T_none £_none Δ_none
                     £_match Δ_match)
   ])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; st-ok

(define-judgment-form
  Patina-typing
  #:mode     (st-ok I    I I I  I I I  O O)
  #:contract (st-ok prog T Λ VL £ Δ st £ Δ)
  
  [(rv-ok srs T Λ VL £ Δ rv ty_rv £_rv Δ_rv)
   (can-init srs T Λ Δ_rv lv)
   (subtype Λ ty_rv (lvtype srs T lv))
   (where Δ_lv (initialize-lv Δ_rv lv))
   --------------------------------------------------
   (st-ok (srs fns) T Λ VL £ Δ (lv = rv) £_rv Δ_lv)]
  
  [(rv-ok srs T Λ VL £ Δ rv ty_rv £_rv Δ_rv)
   (can-write-to srs T Λ £_rv Δ_rv lv)
   (subtype Λ ty_rv (lvtype srs T lv))
   --------------------------------------------------
   (st-ok (srs fns) T Λ VL £ Δ (lv := rv) £_rv Δ_rv)]
  
  [(where (~ ty) (lvtype srs T lv))
   (lv-dropped-if-necessary srs T Δ (* lv))
   --------------------------------------------------
   (st-ok (srs fns) T Λ VL £ Δ (free lv) £ (∪ Δ [lv]))]
  
  [(use-lv-ok srs T Λ £ Δ lv ty Δ_1)
   --------------------------------------------------
   (st-ok (srs fns) T Λ VL £ Δ (drop lv) £ Δ_1)]
  
  [;; lookup the fun def'n (FIXME s/ℓs_f/ℓs_a/):
   (where (fun g [ℓ_f ...] [(x_f ty_f) ...] bk_f) (fun-defn fns g))
   ;; subst from formal lifetime to actual lifetimes
   (where θ [(ℓ_f ℓ_a) ...])
   ;; evaluate actual arguments provided
   (use-lvs-ok srs T Λ £ Δ lvs_a [ty_a ...] Δ_a)
   ;; check that each argument is a subtype of the expected type
   (subtype Λ ty_a (subst-ty θ ty_f)) ...
   --------------------------------------------------
   (st-ok (srs fns) T Λ VL £ Δ (call g [ℓ_a ...] lvs_a) £ Δ_a)]
  
  [(use-lv-ok srs T Λ £ Δ lv_discr ty_discr Δ_discr)
   (where (Option ty_x) ty_discr)
   
   (where (block ℓ_some vdecls_some sts_some) bk_some)
   
   ;; check the some block with x in scope
   (where [vdecls ...] T)
   (where [vls ...] VL)
   (where T_some [[(x ty_x)] vdecls ...])
   (where VL_some [[(x ℓ_some)] vls ...])
   (bk-ok (srs fns) T_some Λ VL_some £ Δ_discr bk_some £_some Δ_some)
   
   ;; check the none block without x in scope
   (bk-ok (srs fns) T Λ VL £ Δ_discr bk_none £_none Δ_none)
   
   (join-after-match srs T x                 ;; initial state
                     T_some £_some Δ_some    ;; state after some
                     T £_none Δ_none         ;; state after none
                     £_match Δ_match)        ;; outputs
   --------------------------------------------------
   (st-ok (srs fns) T Λ VL £ Δ (match
                                   lv_discr
                                 (Some by-value x => bk_some)
                                 (None => bk_none))
          £_match Δ_match)]
  
  [;; check that we can borrow the Option<T>
   (rv-ok srs T Λ VL £ Δ (& ℓ mq lv_discr) ty_discr £_discr Δ_discr)
   (where (& ℓ mq (Option ty_*x)) ty_discr)
   
   (where (block ℓ_some vdecls_some sts_some) bk_some)
   
   ;; check the some block with x in scope
   (where [vdecls ...] T)
   (where [vls ...] VL)
   (where T_some [[(x (& ℓ mq ty_*x))] vdecls ...])
   (where VL_some [[(x ℓ_some)] vls ...])
   (bk-ok (srs fns) T_some Λ VL_some £_discr Δ_discr bk_some £_some Δ_some)
   
   ;; check the none block without x in scope
   (bk-ok (srs fns) T Λ VL £ Δ_discr bk_none £_none Δ_none)
   
   (join-after-match srs T x                 ;; initial state
                     T_some £_some Δ_some    ;; state after some
                     T £_none Δ_none         ;; state after none
                     £_match Δ_match)        ;; outputs
   --------------------------------------------------
   (st-ok (srs fns) T Λ VL £ Δ (match
                                   lv_discr
                                 (Some (ref ℓ mq) x => bk_some)
                                 (None => bk_none))
          £_match Δ_match)]
  
  [(bk-ok prog T Λ VL £ Δ bk £_1 Δ_1)
   --------------------------------------------------
   (st-ok prog T Λ VL £ Δ bk £_1 Δ_1)]
  
  )

;; test initializing an uninitialized i with a constant
(test-equal
 (judgment-holds
  (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] [i]
         (i = 3) £ Δ)
  (£ Δ))
 (term [([] [])]))

;; can only initialize if uninitialized
(test-equal
 (judgment-holds
  (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (i = 3) £ Δ)
  (£ Δ))
 (term []))

;; test overwriting i with a new value
(test-equal
 (judgment-holds
  (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (i := 3) £ Δ)
  (£ Δ))
 (term [([] [])]))

;; test overwriting i with a new value of wrong type
(test-equal
 (judgment-holds
  (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (i := (struct A [] [i])) £ Δ)
  (£ Δ))
 (term []))

;; test borrowing i
#;(test-equal
   (judgment-holds
    (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] [r-mut-int]
           (r-mut-int = (& a mut i)) £ Δ)
    (£ Δ))
   (term [([(a mut i)] [])]))

;; test freeing owned-B; since contents do not need drop, should be legal
(test-equal
 (judgment-holds
  (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (free owned-B) £ Δ)
  (£ Δ))
 (term [([] [owned-B])]))

;; test dropping owned-B
(test-equal
 (judgment-holds
  (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (drop owned-B) £ Δ)
  (£ Δ))
 (term [([] [owned-B])]))

;; test freeing owned-E with and without having dropped contents first
(test-equal
 (judgment-holds
  (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] [((* owned-E) · 0)]
         (free owned-E) £ Δ)
  (£ Δ))
 (term [(() [((* owned-E) · 0) owned-E])]))
(test-equal
 (judgment-holds
  (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (free owned-E) £ Δ)
  (£ Δ))
 (term []))

;; test dropping owned-E when fully/partially initialized
(test-equal
 (judgment-holds
  (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (drop owned-E) £ Δ)
  (£ Δ))
 (term [([] [owned-E])]))
(test-equal
 (judgment-holds
  (st-ok (,test-srs []) ,test-ty-T ,test-ty-Λ ,test-ty-VL [] [((* owned-E) · 1)]
         (drop owned-E) £ Δ)
  (£ Δ))
 (term []))

;; test calls to a function
(test-equal
 (judgment-holds
  (st-ok ,test-ty-prog ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (call drop-owned-B [static] [owned-B])
         £ Δ)
  (£ Δ))
 (term [([] [owned-B])]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sts-ok

(define-judgment-form
  Patina-typing
  #:mode     (sts-ok I    I I I  I I I   O O)
  #:contract (sts-ok prog T Λ VL £ Δ sts £ Δ)
  
  [--------------------------------------------------
   (sts-ok prog T Λ VL £ Δ [] £ Δ)]
  
  [(st-ok prog T Λ VL £_0 Δ_0 st_1 £_1 Δ_1)
   (sts-ok prog T Λ VL £_1 Δ_1 [st_2 ...] £_2 Δ_2)
   --------------------------------------------------
   (sts-ok prog T Λ VL £_0 Δ_0 [st_1 st_2 ...] £_2 Δ_2)]
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; bk-ok

(define-judgment-form
  Patina-typing
  #:mode     (bk-ok I    I I I  I I I  O O)
  #:contract (bk-ok prog T Λ VL £ Δ bk £ Δ)
  
  [(where (block ℓ_b [(x_b ty_b) ...] sts_b) bk)
   
   ;; variables types for new block:
   (where [vdecls ...] T)
   (where T_b [[(x_b ty_b) ...] vdecls ...])
   
   ;; add block lifetime ℓ_b, make it a sublifetime of all others in scope:
   (where Λ_b (∪ Λ [(ℓ_b (in-scope-lifetimes Λ))]))
   
   ;; lifetime of block variables is always ℓ_b:
   (where [vls ...] VL)
   (where VL_b [[(x_b ℓ_b) ...] vls ...])
   
   ;; all block variables initially uninitialized:
   (where Δ_b (∪ Δ [x_b ...]))
   
   (sts-ok (srs fns) T_b Λ_b VL_b £ Δ_b sts_b £_sts Δ_sts)
   
   ;; all local variables must be dropped by user (if needed)
   (lv-dropped-if-necessary srs T_b Δ_sts x_b) ...
   
   ;; remove loans and paths that are specific to this block
   (where Δ_bk (expire-paths [x_b ...] Δ_sts))
   (where £_bk (expire-loans ℓ_b £_sts))
   --------------------------------------------------
   (bk-ok (srs fns) T Λ VL £ Δ bk £_bk Δ_bk)]
  
  )

(test-equal
 (judgment-holds
  (bk-ok [,test-srs []] [] [] [] [] []
         (block l0
                [(r int)]
                [(r = 3)
                 (r := 4)])
         £ Δ)
  (£ Δ))
 (term [([] [])]))

(test-equal
 (judgment-holds
  (bk-ok [,test-srs []] [] [] [] [] []
         (block l0
                [(r int)
                 (s int)]
                [(r = 3)
                 (r := s)])
         £ Δ)
  (£ Δ))
 (term []))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test for statements that involve blocks

; test match where one side drops more than the other
(test-equal
 (judgment-holds
  (st-ok ,test-ty-prog ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (match opt-int
           (Some by-value x => (block l1
                                      []
                                      [(drop owned-B)]))
           (None => (block l2
                           []
                           [])))
         £ Δ)
  (£ Δ))
 (term []))

;; test match where both sides drop the same
(test-equal
 (judgment-holds
  (st-ok ,test-ty-prog ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
         (match opt-int
           (Some by-value x => (block l1
                                      [(y int)]
                                      [(y = x)
                                       (drop owned-B)]))
           (None => (block l2
                           []
                           [(drop owned-B)])))
         £ Δ)
  (£ Δ))
 (term [([] [owned-B])]))

;; test match with a by-ref check
#;(test-equal
   (judgment-holds
    (st-ok ,test-ty-prog ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
           (match opt-int
             (Some (ref b imm) x => (block l1
                                           [(y int)]
                                           [(y = (* x))]))
             (None => (block l2
                             []
                             [])))
           £ Δ)
    (£ Δ))
   (term [([(b imm opt-int)]
           [])]))

;; test match with a by-ref check and a type error
#;(test-equal
   (judgment-holds
    (st-ok ,test-ty-prog ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
           (match opt-int
             (Some (ref b imm) x => (block l1
                                           [(y int)]
                                           [(y = x)])) ;; should be (* x)
             (None => (block l2
                             []
                             [])))
           £ Δ)
    (£ Δ))
   (term []))

;; test recursive match with a by-ref mut check
#;(test-equal
   (judgment-holds
    (st-ok ,test-ty-prog ,test-ty-T ,test-ty-Λ ,test-ty-VL [] []
           (match opt-int
             (Some (ref b mut) x => (block l1
                                           []
                                           [(match opt-int
                                              (Some (ref b mut) y => (block l2 [] []))
                                              (None => (block l2 [] [])))]))
             (None => (block l2 [] [])))
           £ Δ)
    (£ Δ))
   (term []))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; fn-ok

(define-judgment-form
  Patina-typing
  #:mode     (fn-ok I    I )
  #:contract (fn-ok prog fn)
  
  [;; check the block with an initial environment that assumes
   ;; parameters are initialized and not borrowed
   (where (block ℓ_bk vdecls_bk sts_bk) bk)
   (where T  [[(x ty) ...]])
   (where Λ  [(ℓ []) ...])    ;; FIXME - establish initial relations between lifetimes
   (where VL [[(x ℓ_bk)] ...])
   (bk-ok (srs fns) T Λ VL [] [] bk £ Δ)
   
   ;; all parameters must be dropped
   (lv-dropped-if-necessary srs T Δ x) ...
   --------------------------------------------------
   (fn-ok (srs fns) (fun g [ℓ ...] [(x ty) ...] bk))]
  )

;; borrow same value twice immutably
(test-equal
 (judgment-holds (fn-ok
                  ,test-ty-prog
                  (fun test-fn [l0] [(x (~ (struct B (l0))))]
                       (block l1
                              []
                              [(block l2
                                      [(y (& l2 imm (struct B (l0))))
                                       (z (& l2 imm (struct B (l0))))
                                       ]
                                      [(y = (& l2 imm (* x)))
                                       (z = (& l2 imm (* x)))
                                       ])
                               (drop x)]))))
 #t)

(test-equal
 (judgment-holds (fn-ok
                  ,test-ty-prog
                  (fun drop-owned-B [l0] [(x (~ (struct B (l0))))]
                       (block l1
                              []
                              [(drop x)]))))
 #t)

;; can't type check if I forget to (drop x)
(test-equal
 (judgment-holds (fn-ok
                  ,test-ty-prog
                  (fun drop-owned-B [l0] [(x (~ (struct B (l0))))]
                       (block l1
                              []
                              []))))
 #f)

;; but it's ok if we don't own `x`
(test-equal
 (judgment-holds (fn-ok
                  ,test-ty-prog
                  (fun drop-owned-B [l0] [(x (& l0 imm (struct B (l0))))]
                       (block l1
                              []
                              []))))
 #t)

;; test call to drop-owned-B where data is borrowed
(test-equal
 (judgment-holds (fn-ok
                  ,test-ty-prog
                  (fun test-fn [l0] [(x (~ (struct B (l0))))]
                       (block l1
                              [(y (& l1 imm (struct B (l0))))]
                              [(y = (& l1 imm (* x)))
                               (call drop-owned-B [l0] [x])
                               ]))))
 #f)

;; confine borrow to a subblock
(test-equal
 (judgment-holds (fn-ok
                  ,test-ty-prog
                  (fun test-fn [l0] [(x (~ (struct B (l0))))]
                       (block l1
                              []
                              [(block l2
                                      [(y (& l2 imm (struct B (l0))))]
                                      [(y = (& l2 imm (* x)))
                                       ])
                               (call drop-owned-B [l0] [x])
                               ]))))
 #t)

;; take and a linear subfield then try to drop
(test-equal
 (judgment-holds (fn-ok
                  ,test-ty-prog
                  (fun test-fn [l0] [(x (~ (struct B (l0))))]
                       (block l1
                              [(y (& l0 mut int))]
                              [(y = ((* x) · 1))
                               (call drop-owned-B [l0] [x])
                               ]))))
 #f)

;; take and a linear subfield, replace it, then drop
(test-equal
 (judgment-holds (fn-ok
                  ,test-ty-prog
                  (fun test-fn [l0] [(x (~ (struct B (l0))))]
                       (block l1
                              [(y (& l0 mut int))]
                              [(y = ((* x) · 1))
                               (((* x) · 1) = y)
                               (call drop-owned-B [l0] [x])
                               ]))))
 #t)

(test-equal
 (judgment-holds (fn-ok ,sum-prog
                        ,sum-main))
 #t)

(test-equal
 (judgment-holds (fn-ok ,sum-prog
                        (fun sum-list [a b] [(inp (& a imm (struct List [])))
                                             (outp (& b mut int))]
                             (block l0
                                    [(r int)]
                                    [(r = ((* inp) · 0))
                                     (match ((* inp) · 1)
                                       (Some (ref l0 imm) next1 =>
                                             (block l1
                                                    [(next2 (& l1 imm (struct List [])))
                                                     (b int)]
                                                    [(next2 = (& l1 imm (* (* next1))))
                                                     (b = 0)
                                                     (block l3
                                                            [(c (& l3 mut int))]
                                                            [(c = (& l3 mut b))
                                                             (call sum-list [l1 l3] [next2 c])])
                                                     ((* outp) := (r + b))]))
                                       (None =>
                                             (block l1
                                                    []
                                                    [((* outp) := r)])))]))))
 #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; prog-ok

(define-judgment-form
  Patina-typing
  #:mode     (prog-ok I   )
  #:contract (prog-ok prog)
  
  [(where (srs [fn ...]) prog)
   (fn-ok prog fn) ...
   --------------------------------------------------
   (prog-ok prog)]
  
  )
