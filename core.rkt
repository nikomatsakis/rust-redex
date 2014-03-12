#lang racket
(require redex)

(define-language patina
  ;;;; names for things
  ;; α-convertible
  ; variables
  (x variable-not-otherwise-mentioned)
  ;; non α-convertible

  ;; types
  (τ int      ; integers
     )

  ;;;; declarations
  ;; variables
  (vd (x : τ))
  (vds (vd ...))

  ;;;; values
  (ℤ integer)


  ;; lvalues - assignable places
  (lv x       ; variable
      )

  ;; rvalues - result producing expressions
  (rv ℤ           ; integer constants
      (lv + lv)   ; addition
      )

  ;; statements - things that only alter the heap
  (st (lv = rv)      ; assignment
      (st >> st)     ; sequence statements
      (delete lv)    ; shallow destruction
      (block vds st) ; extend context and make fresh lifetime (TODO lifetimes)
      )

  ;;;; contexts for type checking
  (Γ ∅ (x : τ  Γ))

  )

'Γ-extend
(define-metafunction
  patina
  Γ-extend : Γ vd -> Γ
  [(Γ-extend Γ (x : τ)) (x : τ Γ)]
  )

(test-equal
  (term (Γ-extend ∅ (x : int)))
  (term (x : int ∅)))
(test-results)

'Γ-extend-many
(define-metafunction
  patina
  Γ-extend-many : Γ vds -> Γ
  [(Γ-extend-many Γ ()) Γ]
  [(Γ-extend-many Γ (vd_0 vd_1 ...)) (Γ-extend-many (Γ-extend Γ vd_0) (vd_1 ...))]
  )

(test-equal
  (term (Γ-extend-many ∅ ((x : int) (y : int) (z : int) (x : int))))
  (term (x : int (z : int (y : int (x : int ∅))))))
(test-results)

'Γ-use
(define-metafunction
  patina
  Γ-use : Γ x -> Γ
  [(Γ-use (x_0 : τ Γ) x_0) Γ]
  [(Γ-use (x_0 : τ Γ) x_1) (x_0 : τ (Γ-use Γ x_1))]
  )

(test-equal
  (term (Γ-use (x : int ∅) x))
  (term ∅))
(test-equal
  (term (Γ-use (x : int (x : int ∅)) x))
  (term (x : int ∅)))
(test-results)

'Γ-get
(define-metafunction 
  patina
  Γ-get : Γ x -> τ
  [(Γ-get (x_0 : τ Γ) x_0) τ]
  [(Γ-get (x_0 : τ Γ) x_1) (Γ-get Γ x_1)]
  )

(test-equal 
  (term (Γ-get (x : int ∅) x)) 
  (term int))
(test-equal 
  (term (Γ-get (y : int (x : int ∅)) x)) 
  (term int))
(test-results)

'τ-=
(define-metafunction
  patina
  [(τ-= int int) #t]
  )

(test-equal
  (term (τ-= int int))
  (term #t))
(test-results)

; I think this is ok
'Γ-⊆
(define-metafunction
  patina
  [(Γ-⊆ ∅ Γ) #t]
  [(Γ-⊆ (x : τ Γ) ∅) #f]
  [(Γ-⊆ (x : τ Γ_0) Γ_1)
   (Γ-⊆ Γ_0 (Γ-use Γ_1 x))
   (side-condition (term (τ-= τ (Γ-get Γ_1 x))))])

(test-equal
  (term (Γ-⊆ ∅ ∅))
  (term #t))
(test-equal
  (term (Γ-⊆ ∅ (x : int (y : int ∅))))
  (term #t))
(test-equal
  (term (Γ-⊆ (x : int ∅) ∅))
  (term #f))
(test-equal
  (term (Γ-⊆ (x : int ∅) (y : int (x : int ∅))))
  (term #t))
(test-equal
  (term (Γ-⊆ (x : int (x : int ∅)) (x : int ∅)))
  (term #f))
(test-equal
  (term (Γ-⊆ (x : int (x : int ∅)) (x : int (x : int ∅))))
  (term #t))
(test-results)

'τ-lv
(define-judgment-form 
 patina
 #:mode (τ-lv I I O)
 #:contract (τ-lv Γ lv τ)
 [(where τ  (Γ-get Γ x))
  ---------------------------- "τ-lv-var"
  (τ-lv Γ x τ) ; TODO this may need to be adjusted for linear types
  ]
 )

(test-equal
 (judgment-holds 
   (τ-lv (y : int (x : int (z : int ∅))) x τ)
   τ) 
 '(int))
(test-results)

'τ-rv
(define-judgment-form 
 patina
 #:mode (τ-rv I I O O)
 #:contract (τ-rv Γ rv τ Γ)
 [ ---------------- "τ-rv-ℤ"
   (τ-rv Γ ℤ int Γ)
  ]
 [(τ-lv Γ lv_0 int) (τ-lv Γ lv_1 int)
  ----------------------------------- "τ-rv-+"
  (τ-rv Γ (lv_0 + lv_1) int Γ)
  ]
 )

(test-equal
 (judgment-holds
   (τ-rv ∅ 0 τ Γ)
   (τ Γ))
 '((int ∅)))
(test-equal
 (judgment-holds
   (τ-rv (x : int (y : int ∅)) (x + y) τ Γ)
   (τ Γ))
 '((int (x : int (y : int ∅)))))
(test-results)

'τ-st
(define-judgment-form
  patina
  #:mode (τ-st I I O)
  #:contract (τ-st Γ st Γ)
  [(τ-lv Γ_0 lv τ_0) (τ-rv Γ_0 rv τ_0 Γ_1)
   --------------------------------------- "τ-st-="
   (τ-st Γ_0 (lv = rv) Γ_1)
   ]
  [(τ-st Γ_0 st_0 Γ_1) (τ-st Γ_1 st_1 Γ_2)
   --------------------------------------- "τ-st->>"
   (τ-st Γ_0 (st_0 >> st_1) Γ_2)
   ]
  [(where Γ_1 (Γ-use Γ_0 x))
   ------------------------- "τ-st-delete-var"
   (τ-st Γ_0 (delete x) Γ_1)
   ]
  ; TODO delete non-variables somehow
  [(τ-st (Γ-extend-many Γ_0 vds) st Γ_1) 
   (side-condition (Γ-⊆ Γ_1 Γ_0))
   ------------------------------------- "τ-st-bk"
   (τ-st Γ_0 (block vds st) Γ_1)
   ]
  )

(test-equal
  (judgment-holds
    (τ-st (x : int ∅) (x = 1) Γ)
    Γ)
  '((x : int ∅)))
(test-equal
  (judgment-holds
    (τ-st (x : int ∅) ((x = 1) >> (x = 2)) Γ)
    Γ)
  '((x : int ∅)))
(test-equal
  (judgment-holds
    (τ-st (x : int ∅) (delete x) Γ)
    Γ)
  '(∅))
(test-equal
  (judgment-holds
    (τ-st ∅ (block ((x : int)) ((x = 1) >> (delete x))) Γ)
    Γ)
  '(∅))
(test-equal
  (judgment-holds
    (τ-st (x : int ∅) (block () (delete x)) Γ)
    Γ)
  '(∅))
(test-equal
  (judgment-holds
    (τ-st ∅ (block ((x : int)) (x = 1)) Γ)
    Γ)
  '())
(test-results)
