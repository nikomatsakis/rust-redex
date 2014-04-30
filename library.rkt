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

;; basic library functions (that Redex should probably provide already)
;; ---------------------------------------------------------------------------------------------------

(provide
 ;; some generally useful metafunctions and functions; should be 'purposed'
 ∈
 ∉
 
 ¬ ∨ ∧ size if-true ∀ ∃ ∄ ∪ ⊆ ⊎ \\ has get
 
 len
 sum
 prefix-sum
 
 ;; X [Listof [Listof [Cons X Y]]] -> [Maybe Y]
 ;; search for X through multiple association lists 
 get* 
 )

;; ---------------------------------------------------------------------------------------------------
;; implementation 

(require redex rackunit)

(define-language AnyL
  [zs (z ...)]
  [z number])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ∈, ∉ -- a metafunction like member

(define-metafunction AnyL
  ∈ : any [any ...] -> any
  
  [(∈ any_0 [any_1 ...])
   ,(not (not (member (term any_0) (term [any_1 ...]))))])

(define-metafunction AnyL
  ∉ : any [any ...] -> any
  
  [(∉ any_0 [any_1 ...])
   ,(not (member (term any_0) (term [any_1 ...])))])

(module+ test 
  (test-equal (term (∈ 1 [1 2 3])) (term #t))
  (test-equal (term (∈ 4 [1 2 3])) (term #f))
  (test-equal (term (∉ 1 [1 2 3])) (term #f))
  (test-equal (term (∉ 4 [1 2 3])) (term #t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; get* -- search through multiple assoc lists

(define (get* key lists)
  (let ([v (assoc key (car lists))])
    (if (not v)
        (get* key (cdr lists))
        (cadr v))))

(module+ test
  (test-equal (get* (term a) (term (((a 1) (b 2)) ((c 3))))) 1)
  (test-equal (get* (term c) (term (((a 1) (b 2)) ((c 3))))) 3)
  (test-equal (get* (term e) (term (((a 1) (b 2)) ((c 3)) ((d 4) (e 5))))) 5))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; len

(define-metafunction AnyL
  len : [any ...] -> number
  
  [(len [any ...])
   ,(length (term [any ...]))])

(module+ test 
  (test-equal (term (len [1 2 3])) (term 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sum

(define-metafunction AnyL
  sum : zs -> z
  
  [(sum []) 0]
  [(sum [z_0 z_1 ...])
   ,(+ (term z_0) (term (sum [z_1 ...])))]
  )

(module+ test 
  (test-equal (term (sum [1 2 3])) (term 6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; prefix sum

(define-metafunction AnyL
  prefix-sum : z zs -> zs
  
  [(prefix-sum z_a ()) ()]
  [(prefix-sum z_a (z_b z_c ...))
   [z_d z_e ...]
   (where z_d (sum [z_a z_b]))
   (where [z_e ...] (prefix-sum z_d [z_c ...]))]
  )

(module+ test
  (test-equal (term (prefix-sum 0 ())) (term ()))
  (test-equal (term (prefix-sum 0 (1 2 3))) (term (1 3 6))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; common logic functions in term form



(define-metafunction AnyL
  ¬ : boolean -> boolean
  
  [(¬ #t) #f]
  [(¬ #f) #t])

(define-metafunction AnyL
  ∨ : boolean boolean -> boolean
  
  [(∨ #f #f) #f]
  [(∨ boolean_1 boolean_2) #t])

(define-metafunction AnyL
  ∧ : boolean boolean -> boolean
  
  [(∧ #t #t) #t]
  [(∧ boolean_1 boolean_2) #f])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; size

(define-metafunction AnyL
  size : [any ...] -> number
  
  [(size [any ...]) ,(length (term [any ...]))]
  )

(module+ test
  (test-equal (term (size [1 2 3])) (term 3))
  (test-equal (term (size [])) (term 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; if-true list bools -- like filter but takes a list of booleans

(define-metafunction AnyL
  if-true : [any ...] [boolean ...] -> [any ...]
  
  [(if-true any_0 any_1)
   ,(map car (filter cadr (map list (term any_0) (term any_1))))])

(module+ test 
  (test-equal (term (if-true [1 2 3 4 5] [#f #t #f #t #f])) (term [2 4])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ∀, ∃ -- useful functions for operating over vectors of booleans.
;; Particularly useful in combination with macros and maps.

(define-metafunction AnyL
  ∀ : [any ...] -> boolean
  
  [(∀ []) #t]
  [(∀ [#f any ...]) #f]
  [(∀ [#t any ...]) (∀ [any ...])]
  )

(define-metafunction AnyL
  ∃ : [any ...] -> boolean
  
  [(∃ []) #f]
  [(∃ [#t any ...]) #t]
  [(∃ [#f any ...]) (∃ [any ...])]
  )

(define-metafunction AnyL
  ∄ : [any ...] -> boolean
  
  [(∄ any) (¬ (∃ any))]
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ∪ -- a metafunction for set union

(define-metafunction AnyL
  ∪ : [any ...] [any ...] -> [any ...]
  
  [(∪ [any_0 any_1 ...] [any_2 ...])
   (∪ [any_1 ...] [any_2 ...])
   (side-condition (term (∈ any_0 [any_2 ...])))]
  
  [(∪ [any_0 any_1 ...] [any_2 ...])
   (∪ [any_1 ...] [any_0 any_2 ...])]
  
  [(∪ [] [any_1 ...])
   [any_1 ...]]
  
  )

(module+ test
  (test-equal (term (∪ [1 4] [1 2 3])) (term [4 1 2 3])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ⊆ -- a metafunction for subseteq comparison

(define-metafunction AnyL
  ⊆ : [any ...] [any ...] -> boolean
  
  [(⊆ [] [any ...]) #t]
  
  [(⊆ [any_0 any_1 ...] [any_2 ...])
   (and (∀ [∃ any_0 [any_2 ...]])
        (⊆ [any_1 ...] [any_2 ...]))]
  
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ⊎ -- a metafunction for disjoint set union

(define-metafunction AnyL
  ⊎ : [any ...] [any ...] -> [any ...]
  
  [(⊎ [any_0 ...] [any_1 ...])
   ([any_0 ...] [any_1 ...])]
  
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; \\ -- a metafunction for set difference

(define-metafunction AnyL
  \\ : [any ...] [any ...] -> [any ...]
  
  [(\\ any_0 any_1)
   ,(remove* (term any_1) (term any_0))])

(module+ test 
  (test-equal (term (\\ [1 2 3] [2])) (term [1 3]))
  (test-equal (term (\\ [1 2 3] [4])) (term [1 2 3])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; has -- a metafunction like assoc that works on lists like '((k v) (k1 v1))

(define-metafunction AnyL
  has : any [(any any) ...] -> any
  
  [(has any_k0 [(any_k0 any_v0) (any_k1 any_v1) ...])
   #t]
  
  [(has any_k0 [])
   #f]
  
  [(has any_k0 [(any_k1 any_v1) (any_k2 any_v2) ...])
   (has any_k0 [(any_k2 any_v2) ...])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; get -- a metafunction like assoc that works on lists like '((k v) (k1 v1))

(define-metafunction AnyL
  get : any [(any any) ...] -> any
  
  [(get any_k0 [(any_k0 any_v0) (any_k1 any_v1) ...])
   any_v0]
  
  [(get any_k0 [(any_k1 any_v1) (any_k2 any_v2) ...])
   (get any_k0 [(any_k2 any_v2) ...])])


;; ---------------------------------------------------------------------------------------------------
(module+ test
  (test-results))
