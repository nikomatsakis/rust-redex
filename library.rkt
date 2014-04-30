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

;; ---------------------------------------------------------------------------------------------------
(module+ test
  (test-results))
