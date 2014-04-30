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

;; the machine evaluator for Rust's core
;; ---------------------------------------------------------------------------------------------------

(provide
 ;; extended language, inherits from Patina
 ;; syntax needed to specify evaluation on machine 
 Patina-machine
 
 test-srs
 test-T
 
 get*
 sum-prog
 sum-main
 )

;; ---------------------------------------------------------------------------------------------------
;; implementation

(require redex rackunit "syntax.rkt" "library.rkt")

;;;;
;;
;; EVALUATION
;;
;;;;

(define-extended-language Patina-machine Patina
  ;; a configuration of the machine
  [C (prog H V T S)]
  ;; H (heap) : maps addresses to heap values
  [H ((α hv) ...)]
  ;; hv (heap values)
  [hv (ptr α) (int number) void]
  ;; V: maps variable names to addresses
  [V (vmap ...)]
  [vmap ((x α) ...)]
  ;; T : a map from names to types
  [T (vdecls ...)]
  ;; θ : a substitution (from to)
  [θ [(ℓ ℓ) ...]]
  ;; S (stack) : stack-frames contain pending statements
  [S (sf ...)]
  [sf (ℓ sts)]
  [(αs βs γs) (number ...)]
  [(α β γ) number]
  )

;; unit test setup for helper fns

(define test-srs
  (term [(struct A () (int))
         (struct B (l0) (int (& l0 mut int)))
         (struct C (l0) ((struct A ())
                         (struct B (l0))))
         (struct D (l0) ((struct C (l0))
                         (struct A ())
                         (struct C (l0))
                         (struct B (l0))))
         (struct E () [(~ int)])
         ]))

(define test-T (term [[(i int)
                       (p (~ int))]
                      [(a (struct A ()))
                       (b (struct B (static)))
                       (c (struct C (static)))
                       (q (& b1 imm int))
                       (r (~ int))
                       (s (Option (~ int)))
                       (ints3 (vec int 3))
                       (i0 int)
                       (i1 int)
                       (i2 int)
                       (i3 int)
                       (ints3p (& b1 imm (vec int 3)))
                       (intsp (& b1 imm (vec int erased)))
                       ]]))

(define test-V (term (((i 10)
                       (p 11))
                      ((a 12)
                       (b 13)
                       (c 15)
                       (q 18)
                       (r 19)
                       (s 20)
                       (ints3 22)
                       (i0 25)
                       (i1 26)
                       (i2 27)
                       (i3 28)
                       (ints3p 29)
                       (intsp 30)))))

(define test-H (term [(10 (int 22)) ;; i == 22
                      (11 (ptr 99)) ;; p == 99
                      (12 (int 23)) ;; a:0
                      (13 (int 24)) ;; b:0
                      (14 (ptr 98)) ;; b:1
                      (15 (int 25)) ;; c:1:0
                      (16 (int 26)) ;; c:1:0
                      (17 (ptr 97)) ;; c:1:1
                      (18 (ptr 98)) ;; q
                      (19 (ptr 96)) ;; r
                      (20 (int 1))  ;; s – discriminant
                      (21 (ptr 95)) ;; s – payload
                      (22 (int 10)) ;; ints3 @ 0
                      (23 (int 11)) ;; ints3 @ 1
                      (24 (int 12)) ;; ints3 @ 2
                      (25 (int 0))  ;; i0
                      (26 (int 1))  ;; i1
                      (27 (int 2))  ;; i2
                      (28 (int 3))  ;; i3
                      (29 (ptr 22)) ;; ints3p
                      (30 (ptr 22)) ;; intsp ptr
                      (31 (int 3))  ;; intsp dst
                      (95 (int 31))   ;; *payload(s)
                      (96 (int 30))   ;; *c:1:1
                      (97 (int 29))   ;; *c:1:1
                      (98 (int 28))   ;; *b:1
                      (99 (int 27))])) ;; *p

(define test-dst-srs
  (term [(struct RCDataInt3 () [int (vec int 3)])
         (struct RCInt3 (l0) [(& l0 imm (struct RCDataInt3 []))])
         (struct RCDataIntN () (int (vec int erased)))
         (struct RCIntN (l0) [(& l0 imm (struct RCDataIntN []))])
         (struct Cycle1 () [(Option (~ (struct Cycle []))) (vec int erased)])
         (struct Cycle2 () [(Option (~ (struct Cycle [])))])
         ]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; simple test prog that assigns to the result pointer

(define twentytwo-main
  (term (fun main [a] [(outp (& a mut int))]
             (block l0 [] [((* outp) = 22)]))))

(define twentytwo-fns (term [,twentytwo-main]))

(define twentytwo-prog
  (term (,test-srs ,twentytwo-fns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test prog that creates a linked list and counts down

(define sum-srs
  (term [(struct List () (int
                          (Option (~ (struct List [])))))]))

(define sum-main
  (term (fun main [a] [(outp (& a mut int))]
             (block l0
                    [(i int)
                     (n (Option (~ (struct List []))))
                     (s (struct List []))
                     (l (~ (struct List [])))]
                    [(i = 22)
                     (n = (None (~ (struct List []))))
                     (s = (struct List [] (i n)))
                     (l = (new s))
                     (i := 44)
                     (n = (Some l))
                     (s = (struct List [] (i n)))
                     (l = (new s))
                     (block l1
                            [(p (& l1 imm (struct List [])))]
                            [(p = (& l1 imm (* l)))
                             (call sum-list [l1 a] [p outp])
                             ])
                     (drop l)
                     ]))))

;; fn sum-list<'a,'b>(inp: &'a List, outp: &'b mut int) {
;;     let r: int = inp.0;
;;     match inp.1 {
;;         Some(ref next1) => { // next1: &~List
;;             let next2 = &**next1;
;;             let b = 0;
;;             {
;;                 let c = &mut b;
;;                 sum-list(next2, c);
;;             }
;;             *outp = r + b;
;;         }
;;         None => {
;;             *outp = r + b;
;;         }
;;     }
;; }
(define sum-sum-list
  (term (fun sum-list [a b] [(inp (& a imm (struct List [])))
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

(define sum-fns
  (term (,sum-main ,sum-sum-list)))

(define sum-prog
  (term (,sum-srs ,sum-fns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test prog that creates an RC vector, casts it to DST, and then
;; accesses it

(define dst-srs
  (term [(struct RCDataInt3 () [int (vec int 3)])
         (struct RCInt3 (l0) [(& l0 imm (struct RCDataInt3 []))])
         (struct RCDataIntN () (int (vec int erased)))
         (struct RCIntN (l0) [(& l0 imm (struct RCDataIntN []))])
         ]))

;; gonna be super tedious...
(define dst-main
  (term (fun main [a] [(outp (& a mut int))]
             (block l0 [(i1 int)
                        (i2 int)
                        (i3 int)
                        (v (vec int 3))
                        (rd3 (struct RCDataInt3 []))
                        (rd3p (& l0 imm (struct RCDataInt3 [])))
                        (rdNp (& l0 imm (struct RCDataIntN [])))
                        ]
                    [(i1 = 22)
                     (i2 = 23)
                     (i3 = 24)
                     (v = (vec int i1 i2 i3))
                     (i1 = 1)
                     (rd3 = (struct RCDataInt3 [] (i1 v)))
                     (rd3p = (& l0 imm rd3))
                     (rdNp = (pack rd3p (& l0 imm (struct RCDataIntN []))))
                     (i1 = 0)
                     (i2 = 0)
                     (i2 = ((((* rdNp) · 1) @ i1) + i2))
                     (i1 = 1)
                     (i2 = ((((* rdNp) · 1) @ i1) + i2))
                     (i1 = 2)
                     (i2 = ((((* rdNp) · 1) @ i1) + i2))
                     ((* outp) = i2)
                     ]))))

(define dst-prog
  (term (,dst-srs [,dst-main])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; initial -- the initial state of the machine

(define initial-H (term [(0 (int 0))       ;; static value for result code
                         (1 (ptr 0))]))    ;; pointer to result code


(define initial-V (term [[(resultp 1)]]))

(define initial-T (term [[(resultp (& l0 mut int))]]))

(define initial-S (term [(l0 [(call main (l0) (resultp))])]))

;; ---------------------------------------------------------------------------------------------------

(module+ test
  (define-syntax-rule
    (syntactically-correct alternative phrase)
    (check-not-false (redex-match Patina-machine alternative phrase)))
  
  (syntactically-correct srs test-srs)
  (syntactically-correct T test-T)
  (syntactically-correct V test-V)
  (syntactically-correct H test-H)
  (syntactically-correct srs test-dst-srs)
  (syntactically-correct fn twentytwo-main)
  (syntactically-correct fns twentytwo-fns)
  (syntactically-correct prog twentytwo-prog)
  (syntactically-correct srs sum-srs)
  (syntactically-correct fn sum-main)
  (syntactically-correct fn sum-sum-list)
  (syntactically-correct prog sum-prog)
  (syntactically-correct fn dst-main)
  (syntactically-correct prog dst-prog)
  (syntactically-correct H initial-H)
  (syntactically-correct V initial-V)
  (syntactically-correct T initial-T)
  (syntactically-correct S initial-S))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sort-heap -- sort heap address in ascending order

(define (sort-heap heap)
  (sort heap < #:key first #;(λ (pair1 pair2) (< (car pair1) (car pair2)))))

;; useful heap predicates

(define (in-range addr base size)
  (and (>= addr base)
       (< addr (+ base size))))

(define (select H α z)
  (let* [(matching (filter (λ (pair) (in-range (car pair) α z)) H))
         (sorted (sort-heap matching))
         (values (map cadr sorted))]
    values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reject – useful for debugging since it causes contract errors

(define-metafunction Patina-machine
  reject : debug -> number
  
  [(reject debug) 0])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; offset, inc, and dec

(define-metafunction Patina-machine
  offset : α z -> α
  
  [(offset α z) ,(+ (term α) (term z))])

(define-metafunction Patina-machine
  inc : α -> α
  
  [(inc z) ,(add1 (term z))])

(define-metafunction Patina-machine
  dec : α -> α
  
  [(dec z) ,(sub1 (term z))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; deref function -- search a heap for a given address.

(define-metafunction Patina-machine
  deref : H α -> hv
  
  [(deref H α)
   (get α H)])

(module+ test 
  (test-equal (term (deref [(1 (ptr 22))] 1)) (term (ptr 22)))
  (test-equal (term (deref [(2 (ptr 23)) (1 (int 22))] 1)) (term (int 22))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; fun-defn -- 

(define-metafunction Patina-machine
  fun-defn : fns g -> fn
  
  [(fun-defn (fn_0 fn_1 ...) g)
   fn_0
   (where (fun g ℓs ((x ty) ...) bk) fn_0)]
  
  [(fun-defn (fn_0 fn_1 ...) g)
   (fun-defn (fn_1 ...) g)])

(module+ test 
  (test-equal (term (fun-defn ,twentytwo-fns main)) (term ,twentytwo-main)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; update -- replaces value for α

(define-metafunction Patina-machine
  update : H α hv -> H
  
  [(update ((α_0 hv_0) (α_1 hv_1) ...) α_0 hv_2)
   ((α_0 hv_2) (α_1 hv_1) ...)]
  
  [(update ((α_0 hv_0) (α_1 hv_1) ...) α_2 hv_2)
   ,(append (term ((α_0 hv_0))) (term (update ((α_1 hv_1) ...) α_2 hv_2)))])

(module+ test 
  (test-equal (term (update [(2 (ptr 23)) (1 (int 22))] 1 (int 23)))
              (term ((2 (ptr 23)) (1 (int 23)))))
  
  (test-equal (term (update [(2 (ptr 23)) (1 (int 22))] 2 (int 23)))
              (term ((2 (int 23)) (1 (int 22))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; extend -- grows a heap with z contiguous new addresses 

(define-metafunction Patina-machine
  extend : H α z -> H
  
  [(extend H α 0) H]
  
  [(extend ((β hv) ...) α z)
   (extend ((α void) (β hv) ...)
           ,(add1 (term α))
           ,(sub1 (term z)))])

(module+ test
  (test-equal (term (extend [(10 (ptr 1))
                             (11 (int 2))
                             (12 (ptr 3))]
                            13
                            3))
              (term [(15 void)
                     (14 void)
                     (13 void)
                     (10 (ptr 1))
                     (11 (int 2))
                     (12 (ptr 3))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; shrink -- removes z contiguous addresses from domain of heap

(define-metafunction Patina-machine
  shrink : H α z -> H
  
  [(shrink H α z)
   ,(filter (λ (pair) (not (in-range (car pair) (term α) (term z))))
            (term H))])

(module+ test 
  (test-equal (term (shrink [(10 (ptr 1))
                             (11 (int 2))
                             (12 (ptr 3))
                             (13 (ptr 4))
                             (14 (ptr 5))]
                            11
                            3))
              (term [(10 (ptr 1))
                     (14 (ptr 5))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; subst-ℓ

(define-metafunction Patina-machine
  subst-ℓ : θ ℓ -> ℓ
  
  [(subst-ℓ θ static) static]
  [(subst-ℓ θ ℓ) (get ℓ θ)]
  )

(module+ test
  (test-equal (term (subst-ℓ [] static)) (term static))
  (test-equal (term (subst-ℓ [(a b)] a)) (term b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; subst-ty

(define-metafunction Patina-machine
  subst-ty : θ ty -> ty
  
  [(subst-ty θ (struct s [ℓ ...]))
   (struct s [(subst-ℓ θ ℓ) ...])]
  
  [(subst-ty θ (~ ty))
   (~ (subst-ty θ ty))]
  
  [(subst-ty θ (& ℓ mq ty))
   (& (subst-ℓ θ ℓ) mq (subst-ty θ ty))]
  
  [(subst-ty θ int)
   int]
  
  [(subst-ty θ (Option ty))
   (Option (subst-ty θ ty))]
  
  [(subst-ty θ (vec ty olen))
   (vec (subst-ty θ ty) olen)]
  )

(module+ test
  (test-equal (term (subst-ty [(a b) (b c)] (struct s [a b])))
              (term (struct s [b c])))
  
  (test-equal (term (subst-ty [(a b) (b c)] (~ (struct s [a b]))))
              (term (~ (struct s [b c]))))
  
  (test-equal (term (subst-ty [(a b) (b c)] (& a mut (struct s [a b]))))
              (term (& b mut (struct s [b c]))))
  
  (test-equal (term (subst-ty [(a b) (b c)] int))
              (term int))
  
  (test-equal (term (subst-ty [(a b) (b c)] (Option (& a mut int))))
              (term (Option (& b mut int))))
  
  (test-equal (term (subst-ty [(a b) (b c)] (vec (& a mut int) erased)))
              (term (vec (& b mut int) erased))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; field-tys

(define-metafunction Patina-machine
  field-tys : srs s ℓs -> (ty ...)
  
  [(field-tys ((struct s_0 (ℓ_0 ...) (ty_0 ...)) sr ...) s_0 [ℓ_1 ...])
   ((subst-ty θ ty_0) ...)
   (where θ [(ℓ_0 ℓ_1) ...])]
  
  [(field-tys ((struct s_0 (ℓ_0 ...) (ty_0 ...)) sr ...) s_1 ℓs_1)
   (field-tys (sr ...) s_1 ℓs_1)])

(module+ test 
  (test-equal (term (field-tys ,test-srs A ()))
              (term (int))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; is-DST

(define-metafunction Patina-machine
  is-DST : srs ty -> boolean
  
  [(is-DST srs ty) (is-DST-1 [] srs ty)])

(define-metafunction Patina-machine
  is-DST-1 : [s ...] srs ty -> boolean
  
  [(is-DST-1 [s_a ...] srs (struct s ℓs))
   #false
   (side-condition (member (term s) (term [s_a ...])))]
  [(is-DST-1 [s_a ...] srs (struct s ℓs))
   (is-DST-1 [s s_a ...] srs ty_z)
   (where (ty_a ... ty_z) (field-tys srs s ℓs))]
  [(is-DST-1 [s ...] srs (~ ty)) #false]
  [(is-DST-1 [s ...] srs (& ℓ mq ty)) #false]
  [(is-DST-1 [s ...] srs int) #false]
  [(is-DST-1 [s ...] srs (Option ty)) (is-DST-1 [s ...] srs ty)]
  [(is-DST-1 [s ...] srs (vec ty erased)) #true]
  [(is-DST-1 [s ...] srs (vec ty l)) #false])

(module+ test
  (test-equal (term (is-DST ,test-dst-srs (~ (vec int erased))))
              #false)
  
  (test-equal (term (is-DST ,test-dst-srs (vec int erased)))
              #true)
  
  (test-equal (term (is-DST ,test-dst-srs (struct RCDataInt3 [])))
              #false)
  
  (test-equal (term (is-DST ,test-dst-srs (struct RCInt3 [a])))
              #false)
  
  (test-equal (term (is-DST ,test-dst-srs (struct RCDataIntN [])))
              #true)
  
  (test-equal (term (is-DST ,test-dst-srs (struct RCIntN [a])))
              #false)
  
  (test-equal (term (is-DST ,test-dst-srs (struct Cycle1 [])))
              #true)
  
  (test-equal (term (is-DST ,test-dst-srs (struct Cycle2 [])))
              #false))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sizeof

(define-metafunction Patina-machine
  sizeof : srs ty -> z
  
  [(sizeof srs int) 
   1]
  
  [(sizeof srs (~ ty))
   1
   (side-condition (not (term (is-DST srs ty))))]
  
  [(sizeof srs (~ ty))
   2
   (side-condition (term (is-DST srs ty)))]
  
  [(sizeof srs (& ℓ mq ty))
   1
   (side-condition (not (term (is-DST srs ty))))]
  
  [(sizeof srs (& ℓ mq ty))
   2
   (side-condition (term (is-DST srs ty)))]
  
  [(sizeof srs (struct s ℓs))
   (sum [(sizeof srs ty) ...])
   (where [ty ...] (field-tys srs s ℓs))]
  
  [(sizeof srs (vec ty l))
   ,(* (term (sizeof srs ty)) (term l))]
  
  [(sizeof srs (Option ty))
   ,(add1 (term (sizeof srs ty)))]
  
  )

(module+ test
  (test-equal (term (sizeof ,test-srs (struct A ())))
              (term 1))
  
  (test-equal (term (sizeof ,test-srs (struct B (static))))
              (term 2))
  
  (test-equal (term (sizeof ,test-srs (struct C (static))))
              (term 3))
  
  (test-equal (term (sizeof ,test-srs (Option (struct C (static)))))
              (term 4))
  
  (test-equal (term (sizeof ,test-srs (vec int 3)))
              (term 3))
  
  (test-equal (term (sizeof ,test-srs (& b1 imm (vec int 3))))
              (term 1))
  
  (test-equal (term (sizeof ,test-srs (& b1 imm (vec int erased))))
              (term 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sizeof-dst

(define-metafunction Patina-machine
  sizeof-dst : srs ty hv -> z
  
  [(sizeof-dst srs (vec ty erased) (int l))
   ,(* (term (sizeof srs ty)) (term l))]
  
  [(sizeof-dst srs (struct s ℓs) hv)
   (sum [z_a z_z])
   (where [ty_a ... ty_z] (field-tys srs s ℓs))
   (where z_a (sum [(sizeof srs ty_a) ...]))
   (where z_z (sizeof-dst srs ty_z hv))]
  
  )

(module+ test 
  (test-equal (term (sizeof ,test-srs (struct A ())))
              (term 1))
  
  (test-equal (term (sizeof ,test-srs (struct B (static))))
              (term 2))
  
  (test-equal (term (sizeof ,test-srs (struct C (static))))
              (term 3))
  
  (test-equal (term (sizeof ,test-srs (Option (struct C (static)))))
              (term 4))
  
  (test-equal (term (sizeof ,test-srs (vec int 3)))
              (term 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; memcopy -- copies memory from one address to another

(define-metafunction Patina-machine
  memcopy : H α β z -> H
  
  [(memcopy H α β 0) H]
  
  [(memcopy H α β z)
   (memcopy (update H α (deref H β))
            ,(add1 (term α))
            ,(add1 (term β))
            ,(sub1 (term z)))])

(module+ test
  (test-equal (term (memcopy [(10 (ptr 1))
                              (11 (int 2))
                              (12 (ptr 3))
                              (20 (ptr 4))
                              (21 (int 5))
                              (22 (ptr 6))]
                             20
                             10
                             3))
              (term [(10 (ptr 1))
                     (11 (int 2))
                     (12 (ptr 3))
                     (20 (ptr 1))
                     (21 (int 2))
                     (22 (ptr 3))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; vaddr -- lookup addr of variable in V

(define-metafunction Patina-machine
  vaddr : V x -> α
  
  [(vaddr V x_0)
   ,(get* (term x_0) (term V))])

(module+ test 
  (test-equal (term (vaddr (((a 0) (b 1)) ((c 2))) a))
              (term 0))
  (test-equal (term (vaddr (((a 0) (b 1)) ((c 2))) b))
              (term 1))
  (test-equal (term (vaddr (((a 0) (b 1)) ((c 2))) c))
              (term 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; vtype -- lookup type of variable in V

(define-metafunction Patina-machine
  vtype : T x -> ty
  
  [(vtype T x_0)
   ,(get* (term x_0) (term T))])

(module+ test 
  (test-equal (term (vtype ,test-T i)) (term int))
  (test-equal (term (vtype ,test-T c)) (term (struct C (static)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; field-names -- determines the offsets of each field of a struct

(define-metafunction Patina-machine
  field-names : srs s ℓs -> fs
  
  [(field-names srs s ℓs)
   ,(range (term z))
   (where tys (field-tys srs s ℓs))
   (where z (len tys))]
  
  )

(module+ test 
  (test-equal (term (field-names ,test-srs C (static))) (term [0 1])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; field-offsets -- determines the offsets of each field of a struct

(define-metafunction Patina-machine
  field-offsets : srs s ℓs -> zs
  
  [(field-offsets srs s ℓs)
   (0 z ...) ;; FIXME need a prefix sum!
   (where (ty_a ... ty_z) (field-tys srs s ℓs))
   (where (z ...) [(sizeof srs ty_a) ...])]
  
  )

(module+ test
  (test-equal (term (field-offsets ,test-srs C (static))) (term (0 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; vec-offsets -- determines the offsets of each element of a vector

(define-metafunction Patina-machine
  vec-offsets : srs ty l -> zs
  
  [(vec-offsets srs ty 0)
   []]
  
  [(vec-offsets srs ty 1)
   [0]]
  
  [(vec-offsets srs ty l) ;; really, really inefficient. 
   (z_a ... z_y (offset z_y (sizeof srs ty)))
   (where [z_a ... z_y] (vec-offsets srs ty (dec l)))]
  
  )

(module+ test 
  (test-equal (term (vec-offsets ,test-srs int 3)) (term (0 1 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; vec-tys -- returns the types of each element in a vector,
;; which is just the vector element type repeated N times

(define-metafunction Patina-machine
  vec-tys : srs ty l -> tys
  
  [(vec-tys srs ty 0)
   []]
  
  [(vec-tys srs ty 1)
   [ty]]
  
  [(vec-tys srs ty l)
   (ty ty_a ...)
   (where [ty_a ...] (vec-tys srs ty (dec l)))]
  
  )

(module+ test
  (test-equal (term (vec-tys ,test-srs int 3)) (term (int int int))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; offsetof

(define-metafunction Patina-machine
  offsetof : srs s ℓs f -> z
  
  [(offsetof srs s ℓs f)
   ,(foldl + 0 (map (λ (t) (term (sizeof srs ,t)))
                    (take (term (field-tys srs s ℓs))
                          (term f))))])

(module+ test 
  (test-equal (term (offsetof ,test-srs C (static) 0)) (term 0))
  (test-equal (term (offsetof ,test-srs C (static) 1)) (term 1))
  (test-equal (term (offsetof ,test-srs D (static) 1)) (term 3))
  (test-equal (term (offsetof ,test-srs D (static) 3)) (term 7)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lvtype -- compute type of an lvalue

(define-metafunction Patina-machine
  dereftype : ty -> ty
  
  [(dereftype (~ ty)) ty]
  [(dereftype (& ℓ mq ty)) ty])

(define-metafunction Patina-machine
  fieldtype : srs ty f -> ty
  
  [(fieldtype srs (struct s ℓs) f)
   ,(car (drop (term (field-tys srs s ℓs)) (term f)))]) ; fixme--surely a better way

(define-metafunction Patina-machine
  lvtype : srs T lv -> ty
  
  [(lvtype srs T x)
   (vtype T x)]
  
  [(lvtype srs T (* lv))
   (dereftype (lvtype srs T lv))]
  
  [(lvtype srs T (lv · f))
   (fieldtype srs (lvtype srs T lv) f)])

(module+ test 
  (test-equal (term (lvtype ,test-srs ,test-T (* p))) (term int))
  (test-equal (term (lvtype ,test-srs ,test-T (c · 1))) (term (struct B (static)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lvaddr -- lookup addr of variable in V

(define-metafunction Patina-machine
  lvaddr-elem : srs H V T ty l lv lv -> z
  
  [(lvaddr-elem srs H V T ty_e l_v lv_v lv_i)
   (offset (lvaddr srs H V T lv_v) z_e)
   (where α_i (lvaddr srs H V T lv_i))
   (where (int l_i) (deref H α_i))
   (where z_e ,(* (term l_i) (term (sizeof srs ty_e))))
   (side-condition (>= (term l_i) 0))
   (side-condition (< (term l_i) (term l_v)))]
  
  )

(define-metafunction Patina-machine
  lvaddr : srs H V T lv -> α
  
  [(lvaddr srs H V T x)
   (vaddr V x)]
  
  [(lvaddr srs H V T (* lv))
   α
   (where (ptr α) (deref H (lvaddr srs H V T lv)))]
  
  [(lvaddr srs H V T (lv · f))
   (offset (lvaddr srs H V T lv)
           (offsetof srs s ℓs f))
   (where (struct s ℓs) (lvtype srs T lv))]
  
  ;; indexing into a fixed-length vector
  [(lvaddr srs H V T (lv_v @ lv_i))
   (lvaddr-elem srs H V T ty_e l_v lv_v lv_i)
   (where (vec ty_e l_v) (lvtype srs T lv_v))]
  
  ;; indexing into a dynamically sized vector
  [(lvaddr srs H V T (lv_v @ lv_i))
   (lvaddr-elem srs H V T ty_e l_v lv_v lv_i)
   (where (vec ty_e erased) (lvtype srs T lv_v))
   (where (int l_v) (reified srs H V T lv_v))]
  
  )

(module+ test 
  (test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T (c · 1))) (term 16))
  (test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T ((c · 1) · 1))) (term 17))
  (test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T (* ((c · 1) · 1)))) (term 97))
  (test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T (ints3 @ i1))) (term 23))
  #;
  (test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T (ints3 @ i4))) (term 23)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reified -- given a LV of DST type, identifies and returns the "reified"
;; portion (i.e., the length). Must be behind the most recent pointer.

(define-metafunction Patina-machine
  reified : srs H V T lv -> hv
  
  [(reified srs H V T (* lv))
   (deref H (inc α))
   (where α (lvaddr srs H V T lv))]
  
  [(reified srs H V T (lv_o · f))
   (reified srs H V T lv_o)]
  
  [(reified srs H V T (lv_v @ lv_i))
   (reified srs H V T lv_v)]
  
  )

(module+ test
  (test-equal (term (reified ,test-srs ,test-H ,test-V ,test-T ((* intsp) @ i2)))
              (term (int 3)))
  
  (test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T ((* intsp) @ i1)))
              (term 23)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; malloc -- extend heap z contiguous addresses and retun starting address

(define-metafunction Patina-machine
  malloc : H z -> (H α)
  
  [(malloc H z)
   (H_1 β)
   (where ((α hv) ...) H)
   (where β ,(add1 (apply max (term (-1 α ...)))))
   (where H_1 (extend H β z))])

(module+ test
  (test-equal (cadr (term (malloc ,test-H 2))) 100)
  (test-equal (cadr (term (malloc () 2))) 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; copymany -- like memcopy but for a series of regions

(define-metafunction Patina-machine
  copymany : H zs αs βs -> H
  
  [(copymany H () () ())
   H]
  
  [(copymany H (z_0 z_1 ...) (α_0 α_1 ...) (β_0 β_1 ...))
   (copymany (memcopy H α_0 β_0 z_0)
             (z_1 ...)
             (α_1 ...)
             (β_1 ...))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reify-pack -- extract out the static part of some type that is to be
;; packed and reify into a heap value

(define-metafunction Patina-machine
  reify-pack : srs ty ty -> hv
  
  [(reify-pack srs (vec ty l) (vec ty erased))
   (int l)]
  
  [(reify-pack srs (struct s_s ℓs_s) (struct s_d ℓs_d))
   (reify-pack srs ty_s^z ty_d^z)
   (where (ty_s^a ... ty_s^z) (field-tys srs s_s ℓs_s))
   (where (ty_d^a ... ty_d^z) (field-tys srs s_d ℓs_d))]
  
  )

(module+ test
  (test-equal (term (reify-pack ,test-dst-srs (vec int 22) (vec int erased)))
              (term (int 22)))
  
  (test-equal (term (reify-pack ,test-dst-srs (struct RCDataInt3 []) (struct RCDataIntN [])))
              (term (int 3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rveval -- evaluate an rvalue and store it into the heap at address α

(define-metafunction Patina-machine
  rveval : srs H V T α rv -> H
  
  [(rveval srs H V T α lv)
   H_1
   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where β (lvaddr srs H V T lv))
   (where H_1 (memcopy H α β z))]
  
  [(rveval srs H V T α (& ℓ mq lv))
   H_1
   (where β (lvaddr srs H V T lv))
   (where ty (lvtype srs T lv))
   (where H_1 (update H α (ptr β)))
   (side-condition (not (term (is-DST srs ty))))]
  
  [(rveval srs H V T α (& ℓ mq lv))
   H_2
   (where β (lvaddr srs H V T lv))
   (where ty (lvtype srs T lv))
   (where (int l) (reified srs H V T lv))
   (where H_1 (update H α (ptr β)))
   (where H_2 (update H_1 (inc α) (int l)))
   (side-condition (term (is-DST srs ty)))]
  
  [(rveval srs H V T α (struct s ℓs lvs))
   (copymany H zs_0 βs αs)
   
   ;; types of each field:
   (where tys (field-tys srs s ℓs))
   ;; sizes of each field's type:
   (where zs_0 ,(map (λ (t) (term (sizeof srs ,t))) (term tys)))
   ;; offset of each field:
   (where zs_1 (field-offsets srs s ℓs))
   ;; source address of value for each field:
   (where αs ,(map (λ (lv) (term (lvaddr srs H V T ,lv))) (term lvs)))
   ;; target address for each field relative to base address α;
   (where βs ,(map (λ (z) (+ (term α) z)) (term zs_1)))]
  
  [(rveval srs H V T α (new lv))
   (update H_2 α (ptr γ))
   
   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where β (lvaddr srs H V T lv))
   (where (H_1 γ) (malloc H z))
   (where H_2 (memcopy H_1 γ β z))]
  
  [(rveval srs H V T α number)
   (update H α (int number))]
  
  [(rveval srs H V T α (lv_l + lv_r))
   (update H α (int number_s))
   
   (where α_l (lvaddr srs H V T lv_l))
   (where α_r (lvaddr srs H V T lv_r))
   (where (int number_l) (deref H α_l))
   (where (int number_r) (deref H α_r))
   (where number_s (offset number_l number_r))]
  
  [(rveval srs H V T α (Some lv))
   H_2
   
   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where β (lvaddr srs H V T lv))
   (where α_p ,(add1 (term α)))
   (where H_1 (memcopy H α_p β z))
   (where H_2 (update H_1 α (int 1)))]
  
  [(rveval srs H V T α (None ty))
   (update H α (int 0))]
  
  [(rveval srs H V T α (vec ty))
   H]
  
  [(rveval srs H V T α (vec ty lv_e ...))
   H_1
   
   ;; find addresses α_e of the inputs lv_e
   (where [α_e ...] [(lvaddr srs H V T lv_e) ...])
   ;; determine ty of vector from type of 1st lvalue
   (where [lv_a lv_b ...] [lv_e ...])
   (where ty (lvtype srs T lv_a))
   ;; length of vector comes from number of lvalues
   (where l_v (len [lv_a lv_b ...]))
   ;; find types/sizes of the elements (always the same for each element)
   (where [ty_e ...] (vec-tys srs ty l_v))
   (where [z_e ...] [(sizeof srs ty_e) ...])
   ;; find addresses β_e of each element
   (where [z_o ...] (vec-offsets srs ty l_v))
   (where [β_e ...] ((offset α z_o) ...))
   ;; copy lvalues into their new homes
   (where H_1 (copymany H [z_e ...] [β_e ...] [α_e ...]))]
  
  ;; pack from ~ty_s to ~ty_d where ty_d is DST
  ;; (see nearly identical borrowed pointer rule below)
  [(rveval srs H V T α (pack lv_s (~ ty_d)))
   H_2
   
   ;; copy pointer value
   (where α_s (lvaddr srs H V T lv_s))
   (where H_1 (memcopy H α α_s 1))
   
   ;; reify component of type and store into heap at offset 1 of fat
   ;; pointer
   (where (~ ty_s)  (lvtype srs T lv))
   (where hv (reify-pack srs ty_s ty_d))
   (where H_2 (update H_1 (inc α) hv))]
  
  ;; pack from &ty_s to &ty_d where ty_d is DST
  ;; (see nearly identical owned pointer rule above)
  [(rveval srs H V T α (pack lv_s (& ℓ mq ty_d)))
   H_2
   
   ;; copy pointer value
   (where α_s (lvaddr srs H V T lv_s))
   (where H_1 (memcopy H α α_s 1))
   
   ;; reify component of type and store into heap at offset 1 of fat
   ;; pointer
   (where (& ℓ mq ty_s)  (lvtype srs T lv_s))
   (where hv (reify-pack srs ty_s ty_d))
   (where H_2 (update H_1 (inc α) hv))]
  
  ;; len for non-DST
  [(rveval srs H V T α (vec-len lv))
   (update H α (int l))
   (where (vec ty l) (lvtype srs T lv))]
  
  ;; len for DST
  [(rveval srs H V T α (vec-len lv))
   (update H α (reified srs H V T lv))
   (where (vec ty erased) (lvtype srs T lv))]
  
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lvselect -- helper for writing tests, selects values for a portion
;; of the heap

(define-metafunction Patina-machine
  lvselect : srs H V T lv -> (hv ...)
  
  [(lvselect srs H V T lv)
   ,(select (term H) (term α) (term z))
   
   (where ty (lvtype srs T lv))
   (where α (lvaddr srs H V T lv))
   (where z (sizeof srs ty))])

;; tests for rveval and lvselect

(module+ test
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs ,test-H ,test-V ,test-T
                                      (vaddr ,test-V c)
                                      (struct C (b1) (a b)))
                              ,test-V
                              ,test-T
                              c))
              (term ((int 23) (int 24) (ptr 98))))
  
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs ,test-H ,test-V ,test-T
                                      (vaddr ,test-V c)
                                      (struct C (b1) (a b)))
                              ,test-V
                              ,test-T
                              a))
              (term ((int 23))))
  
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs ,test-H ,test-V ,test-T
                                      (vaddr ,test-V p)
                                      (new i))
                              ,test-V
                              ,test-T
                              p))
              (term ((ptr 100))))
  
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs ,test-H ,test-V ,test-T
                                      (vaddr ,test-V p)
                                      (new i))
                              ,test-V
                              ,test-T
                              p))
              (term ((ptr 100))))
  
  (test-equal (term (deref (rveval ,test-srs ,test-H ,test-V ,test-T
                                   (vaddr ,test-V p)
                                   (new i)) 100))
              (term (int 22))) ;; *p now contains value of i
  
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs ,test-H ,test-V ,test-T
                                      (vaddr ,test-V q)
                                      (& mq imm (* ((c · 1) · 1))))
                              ,test-V
                              ,test-T
                              q))
              (term ((ptr 97))))
  
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs ,test-H ,test-V ,test-T
                                      (vaddr ,test-V i)
                                      (i + (* p)))
                              ,test-V
                              ,test-T
                              i))
              (term ((int 49))))
  
  
  ;; test that `None` writes a 0 into the discriminant, leaves rest unchanged
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs ,test-H ,test-V ,test-T
                                      (vaddr ,test-V s)
                                      (None int))
                              ,test-V
                              ,test-T
                              s))
              (term ((int 0) (ptr 95))))
  
  ;; test that `(Some p)` writes a 1 into the discriminant
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs ,test-H ,test-V ,test-T
                                      (vaddr ,test-V s)
                                      (Some p))
                              ,test-V
                              ,test-T
                              s))
              (term ((int 1) (ptr 99))))
  
  ;; test `(vec int i1 i2 i3)`
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs ,test-H ,test-V ,test-T
                                      (vaddr ,test-V ints3)
                                      (vec int i1 i2 i3))
                              ,test-V
                              ,test-T
                              ints3))
              (term ((int 1) (int 2) (int 3))))
  
  ;; test pack
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs
                                      ;; regenerate the value of intsp
                                      ,test-H
                                      ,test-V
                                      ,test-T
                                      (vaddr ,test-V intsp)
                                      (pack ints3p (& b1 imm (vec int erased))))
                              ,test-V
                              ,test-T
                              intsp))
              (term ((ptr 22) (int 3))))
  
  ;; test len for non-DST
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs
                                      ,test-H
                                      ,test-V
                                      ,test-T
                                      (vaddr ,test-V i)
                                      (vec-len ints3))
                              ,test-V
                              ,test-T
                              i))
              (term ((int 3))))
  
  ;; test len for DST
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs
                                      ,test-H
                                      ,test-V
                                      ,test-T
                                      (vaddr ,test-V i)
                                      (vec-len (* intsp)))
                              ,test-V
                              ,test-T
                              i))
              (term ((int 3))))
  
  ;; test taking address of DST
  (test-equal (term (lvselect ,test-srs
                              (rveval ,test-srs
                                      ,test-H
                                      ,test-V
                                      ,test-T
                                      (vaddr ,test-V intsp)
                                      (& b1 imm (* intsp)))
                              ,test-V
                              ,test-T
                              intsp))
              (term ((ptr 22) (int 3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; free-pointer srs H α ty -> H
;;
;; `α` should contain a pointer to memory of type `ty`. Frees the memory
;; pointed at by `α` (shallowly).

(define-metafunction Patina-machine
  free-pointer : srs H α ty -> H
  
  [(free-pointer srs H α ty)
   H_1
   (side-condition (not (term (is-DST srs ty))))
   (where (ptr β) (deref H α))
   (where z (sizeof srs ty))
   (where H_1 (shrink H β z))
   ]
  
  [(free-pointer srs H α ty)
   H_1
   (side-condition (term (is-DST srs ty)))
   (where (ptr β) (deref H α))
   (where hv (deref H (inc α)))
   (where z (sizeof-dst srs ty hv))
   (where H_1 (shrink H β z))
   ]
  
  )

(module+ test 
  ; free a ~int
  (test-equal (term (free-pointer ,test-srs
                                  [(1 (int 22))
                                   (10 (ptr 99))
                                   (99 (int 33))]
                                  10
                                  int))
              (term [(1 (int 22)) (10 (ptr 99))]))
  
  ; free a ~[int] of len 3
  (test-equal (term (free-pointer ,test-srs
                                  [(1 (int 22))
                                   (10 (ptr 95))
                                   (11 (int 3))
                                   (95 (int 33))
                                   (96 (int 34))
                                   (97 (int 35))
                                   (98 (int 36))
                                   ]
                                  10
                                  (vec int erased)))
              (term [(1 (int 22)) (10 (ptr 95)) (11 (int 3)) (98 (int 36))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; drop-contents -- drops the memory owned by `α` which has type `ty`
;;
;; Note that this does *not* free (or deinitialize) `α` itself!

(define-metafunction Patina-machine
  drop-contents-at-offsets : srs H α (ty ...) (z ...) -> H
  
  [(drop-contents-at-offsets srs H α () ())
   H]
  
  [(drop-contents-at-offsets srs H α (ty_0 ty_1 ...) (z_0 z_1 ...))
   (drop-contents-at-offsets srs H_1 α (ty_1 ...) (z_1 ...))
   (where H_1 (drop-contents srs H ty_0 (offset α z_0)))]
  
  )

(define-metafunction Patina-machine
  drop-contents-vec : srs H α ty l -> H
  
  [(drop-contents-vec srs H α ty l)
   (drop-contents-at-offsets srs H α
                             (vec-tys srs ty l)
                             (vec-offsets srs ty l))]
  
  )

(define-metafunction Patina-machine
  drop-contents-dst : srs H ty α hv -> H
  
  [(drop-contents-dst srs H (vec ty erased) α (int z))
   (drop-contents-vec srs H α ty z)]
  
  [(drop-contents-dst srs H (struct s ℓs) α)
   (drop-contents-dst srs H_1 ty_z (offset α z_z) hv)
   (where (ty_a ... ty_z) (field-tys srs s ℓs))
   (where (z_a ... z_z) (field-offsets srs s ℓs))
   (where H_1 (drop-contents-at-offsets srs H α (ty_a ...) (z_a ...)))]
  
  )

(define-metafunction Patina-machine
  drop-contents : srs H ty α -> H
  
  [(drop-contents srs H int α)
   H]
  
  [(drop-contents srs H (vec ty z) α)
   (drop-contents-vec srs H α ty z)]
  
  [(drop-contents srs H (& ℓ mq ty) α) H]
  
  [(drop-contents srs H (~ ty) α)
   H_2
   (where (ptr β) (deref H α))
   (where z (sizeof srs ty))
   (where H_1 (drop-contents srs H ty β))
   (where H_2 (shrink H_1 β z))
   (side-condition (not (term (is-DST srs ty))))]
  
  [(drop-contents srs H (~ ty) α_0)
   H_2
   (where (ptr β) (deref H α))
   (where hv (deref H (inc α)))
   (where z (sizeof-dst srs ty hv))
   (where H_1 (drop-contents-dst srs H ty β hv))
   (where H_2 (shrink H_1 β z))
   (side-condition (term (is-DST srs ty)))]
  
  [(drop-contents srs H (struct s ℓs) α)
   (drop-contents-at-offsets srs H α tys zs)
   (where tys (field-tys srs s ℓs))
   (where zs (field-offsets srs s ℓs))]
  
  [(drop-contents srs H (Option ty) α)
   H
   (where (int 0) (deref H α))]
  
  [(drop-contents srs H (Option ty) α)
   (drop-contents srs H ty ,(add1 (term α)))
   (where (int 1) (deref H α))]
  )

(define-metafunction Patina-machine
  drop-lv-contents : srs H V T lv -> H
  
  [(drop-lv-contents srs H V T lv)
   (drop-contents srs H ty α)
   (where ty (lvtype srs T lv))
   (where α (lvaddr srs H V T lv))])

(module+ test 
  (test-equal (term (drop-lv-contents ,test-srs ,test-H ,test-V ,test-T p))
              (term (shrink ,test-H 99 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; free-variables -- pop the stack frame for a block; i.e., shallowly remove the
;; memory used by its variables

(define-metafunction Patina-machine
  free-variables : srs H vmap vdecls -> H
  
  [(free-variables srs H [] []) H]
  [(free-variables srs
                   H
                   [(x_0 α_0) (x_1 α_1) ...]
                   [(x_0 ty_0) (x_1 ty_1) ...])
   (free-variables srs H_1 [(x_1 α_1) ...] [(x_1 ty_1) ...])
   (where z (sizeof srs ty_0))
   (where H_1 (shrink H α_0 z))]
  )

(module+ test 
  ;; frees the memory used b the local variables, but not what they may reference
  (test-equal (term (free-variables ,test-srs
                                    [(1 (int 22))
                                     (10 (ptr 99))
                                     (99 (int 33))]
                                    [(i 1) (p 10)]
                                    [(i int) (p (~ int))]))
              (term ((99 (int 33))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; alloc-variables -- allocate space for variables upon entry to a block,
;; filling the memory with void

(define-metafunction Patina-machine
  alloc-variables : srs H ((x ty) ...) -> (vmap vdecls H)
  
  [(alloc-variables srs H ()) (() () H)]
  [(alloc-variables srs H ((x_0 ty_0) (x_1 ty_1) ...))
   (((x_0 α_0) (x_2 α_2) ...)
    ((x_0 ty_0) (x_2 ty_2) ...)
    H_2)
   (where z (sizeof srs ty_0))
   (where (H_1 α_0) (malloc H z))
   (where (((x_2 α_2) ...)
           ((x_2 ty_2) ...)
           H_2) (alloc-variables srs H_1 ((x_1 ty_1) ...)))])

(module+ test
  
  ;; this should release all memory but that which pertains to `i` and `p`,
  ;; as well as `97` and `98` which are marked as 'static'
  (test-equal (term (alloc-variables ,test-srs
                                     ,test-H
                                     ((j int)
                                      (k (struct B (static))))))
              (term (((j 100) (k 101))
                     ((j int) (k (struct B (static))))
                     ,(append (term ((102 void) (101 void) (100 void)))
                              test-H)))))

;; unwrap

(define-metafunction Patina-machine
  unwrap : srs H ℓ mode ty α -> (H ty α)
  
  [(unwrap srs H ℓ (ref ℓ_x mq_x) ty α)
   (H_u ty_m α_m)
   ;; type of variable `x_m`
   (where ty_m (& ℓ_x mq_x ty))
   ;; generate memory for `x_m`
   (where (H_m α_m) (malloc H (sizeof srs ty_m)))
   ;; update mem location with ptr to payload
   (where H_u (update H_m α_m (ptr α)))]
  
  [(unwrap srs H ℓ by-value ty α)
   (H_u ty α_m)
   ;; generate memory for `x_m`
   (where (H_m α_m) (malloc H (sizeof srs ty)))
   ;; copy payload from α into α_m
   (where H_u (memcopy H_m α_m α (sizeof srs ty)))]
  )

(module+ test
  (test-equal (term (unwrap ,test-srs ,test-H l1 (ref l2 mut) (~ int)
                            ,(add1 (term (vaddr ,test-V s)))))
              (term (,(append (term [(100 (ptr 21))]) test-H)
                     (& l2 mut (~ int))
                     100)))
  
  (test-equal (term (unwrap ,test-srs ,test-H l1 by-value (~ int)
                            ,(add1 (term (vaddr ,test-V s)))))
              (term (,(append (term [(100 (ptr 95))]) test-H)
                     (~ int)
                     100))))

;; --> -- machine step from one configuration C to the next

(define machine-step
  (reduction-relation
   Patina-machine
   
   ;; Stack frame with no more statements. Free variables.
   [--> ((srs fns) H [vmap_0 vmap_1 ...] [vdecls_0 vdecls_1 ...]
                   [(ℓ ()) sf_1 ...])
        ((srs fns) H_1 [vmap_1 ...] [vdecls_1 ...] [sf_1 ...])
        (where H_1 (free-variables srs H vmap_0 vdecls_0))]
   
   ;; Assignments. The memory for the lvalue should always be alloc'd,
   ;; but not initialized.
   [--> ((srs fns) H V T [(ℓ ((lv = rv) st ...)) sf ...])
        ((srs fns) H_1 V T [(ℓ (st ...)) sf ...])
        (where α (lvaddr srs H V T lv))
        (where H_1 (rveval srs H V T α rv))]
   
   ;; Overwrites. The memory for the lvalue should always be fully initialized.
   ;; Previous contents will be dropped.
   [--> ((srs fns) H V T [(ℓ ((lv := rv) st ...)) sf ...])
        ((srs fns) H_2 V T [(ℓ (st ...)) sf ...])
        (where α (lvaddr srs H V T lv))
        (where H_1 (drop-lv-contents srs H V T lv))
        (where H_2 (rveval srs H_1 V T α rv))]
   
   ;; Frees. lv should be a pointer whose contents have been freed.
   [--> ((srs fns) H V T [(ℓ ((free lv) st ...)) sf ...])
        ((srs fns) H_2 V T [(ℓ (st ...)) sf ...])
        (where H_1 (free-pointer srs H V T lv))]
   
   ;; Drops. The memory for the lvalue should be fully initialized.
   [--> ((srs fns) H V T [(ℓ ((drop lv) st ...)) sf ...])
        ((srs fns) H_1 V T [(ℓ (st ...)) sf ...])
        (where H_1 (drop-lv-contents srs H V T lv))]
   
   ;; Match, None case.
   [--> ((srs fns) H V T [(ℓ [st_a st ...]) sf ...])
        ((srs fns) H [() vmap ...] [() vdecls ...] [(ℓ_m [bk_n]) (ℓ [st ...]) sf ...])
        ;; st_a is some kind of match:
        (where (match lv_d (Some mode x_d => bk_s) (None => bk_n)) st_a)
        ;; the discriminant lies at address α_d:
        (where α_d (lvaddr srs H V T lv_d))
        ;; it is a None value:
        (where (int 0) (deref H α_d))
        ;; generate a fresh lifetime: (FIXME)
        (where ℓ_m lmatch)
        ;; unpack V and T
        (where ([vmap ...] [vdecls ...]) (V T))
        ]
   
   ;; Match, some case.
   [--> ((srs fns) H V T [(ℓ [st_a st ...]) sf ...])
        C_n
        ;; st_a is a match:
        (where (match lv_d (Some mode x_m => bk_s) (None => bk_n)) st_a)
        ;; the discriminant lies at address α_d:
        (where α_d (lvaddr srs H V T lv_d))
        ;; the discriminant has Option type:
        (where (Option ty) (lvtype srs T lv_d))
        ;; it is a Some value:
        (where (int 1) (deref H α_d))
        ;; make a pointer to the payload:
        (where α_v ,(add1 (term α_d)))
        ;; generate a fresh lifetime: (FIXME)
        (where ℓ_m lmatch)
        ;; handle the ref/move into `x_m`:
        (where (H_m ty_m α_m) (unwrap srs H ℓ_m mode ty α_v))
        ;; create new entry for vmap/vdecls
        (where vmap_m [(x_m α_m)])
        (where vdecls_m [(x_m ty_m)])
        ;; unpack V and T
        (where ([vmap ...] [vdecls ...]) (V T))
        (where C_n ((srs fns) H_m [vmap_m vmap ...] [vdecls_m vdecls ...]
                              [(ℓ_m [bk_s]) (ℓ [st ...]) sf ...]))
        ]
   
   ;; Push a new block.
   [--> ((srs fns) H (vmap ...) (vdecls ...)
                   [sf_1 sf_2 ...])
        ((srs fns) H_1  [vmap_b vmap ...] [vdecls_b vdecls ...]
                   [sf_b (ℓ_1 [st_1 ...]) sf_2 ...])
        
        ;; unpack the top-most stack frame sf_1:
        (where (ℓ_1 [st_0 st_1 ...]) sf_1)
        ;; unpack the next statement st_0, which should be a block:
        (where (block ℓ_b vdecls_b [st_b ...]) st_0)
        ;; allocate space for block svariables in memory:
        (where (vmap_b vdecls_b H_1) (alloc-variables srs H vdecls_b))
        ;; create new stack frame for block
        ;; FIXME substitute a fresh lifetime for ℓ_b
        (where sf_b (ℓ_b (st_b ...)))
        ]
   
   ;; Push a call.
   [--> ((srs fns) H V T S)
        ((srs fns) H_2 [vmap_a vmap ...] [vdecls_a vdecls ...]
                   [(lX (bk_f)) (ℓ_1 [st_r ...]) sf_r ...])
        
        ;; unpack V and T for later expansion
        (where ([vmap ...] [vdecls ...]) (V T))
        ;; unpack the stack frames:
        (where [(ℓ_1 sts_1) sf_r ...] S)
        ;; unpack the statements sts_1 from top-most activation:
        (where ((call g ℓs_a lvs_a) st_r ...) sts_1)
        ;; determine the types of the actual args to be passed:
        (where tys_a ,(map (λ (lv) (term (lvtype srs T ,lv)))
                           (term lvs_a)))
        ;; determine sizes of those types
        (where zs_a ,(map (λ (ty) (term (sizeof srs ,ty)))
                          (term tys_a)))
        ;; determine where lvalues are found in memory
        (where αs_a ,(map (λ (lv) (term (lvaddr srs H V T ,lv)))
                          (term lvs_a)))
        ;; lookup the fun def'n (FIXME s/ℓs_f/ℓs_a/):
        (where (fun g ℓs_f vdecls_f bk_f) (fun-defn fns g))
        ;; allocate space for parameters in memory:
        (where (vmap_a vdecls_a H_1) (alloc-variables srs H vdecls_f))
        ;; determine addresses for each formal argument:
        (where ((x_f ty_f) ...) vdecls_f)
        (where βs_f ,(map (λ (lv) (term (lvaddr srs H_1
                                                (vmap_a) (vdecls_a)
                                                ,lv)))
                          (term (x_f ...))))
        ;; move from actual params into formal params:
        (where H_2 (copymany H_1 zs_a βs_f αs_a))
        ]
   ))

(module+ test 
  
  ;; test stepping where top-most stack frame has no remaining statements
  (test--> machine-step
           (term (,twentytwo-prog () (()) (()) ((l0 ()))))
           (term (,twentytwo-prog () () () ())))
  
  ;; test popping off a stack frame with vars and another frame beneath
  (test--> machine-step
           (term (,twentytwo-prog
                  [(0 (int 22)) (1 (int 23))]
                  [[(j 1)] [(i 0)]]
                  [[(j int)] [(i int)]]
                  [(l0 []) (l1 [])]))
           (term (,twentytwo-prog
                  [(0 (int 22))]
                  [[(i 0)]]
                  [[(i int)]]
                  [(l1 [])])))
  
  ;;;; test pushing a new block
  (test--> machine-step
           (term (,twentytwo-prog
                  [(0 (int 22))]
                  [[(a 0)]]
                  [[(a int)]]
                  [(l1 [(block l2
                               [(b int)
                                (c (~ int))]
                               [(i = 2)
                                (j = (new i))])])]))
           (term (,twentytwo-prog
                  [(2 void) (1 void) (0 (int 22))]
                  [[(b 1) (c 2)] [(a 0)]]
                  [[(b int) (c (~ int))] [(a int)]]
                  [(l2 [(i = 2) (j = (new i))])
                   (l1 [])]))))

;; test a series of state steps, starting from the initial state.
;; This tests:
;; - function calls
;; - block activation
;; - assignment (through a pointer)
;; - popping

(define state-0
  (term (,twentytwo-prog ,initial-H ,initial-V ,initial-T ,initial-S)))

(define state-1
  (term (,twentytwo-prog
         [(2 (ptr 0)) (0 (int 0)) (1 (ptr 0))]
         [[(outp 2)] [(resultp 1)]]
         [[(outp (& a mut int))] [(resultp (& l0 mut int))]]
         [(lX [(block l0 [] (((* outp) = 22)))])
          (l0 [])])))

(define state-2
  (term (,twentytwo-prog
         [(2 (ptr 0)) (0 (int 0)) (1 (ptr 0))]
         [[] [(outp 2)] [(resultp 1)]]
         [[] [(outp (& a mut int))] [(resultp (& l0 mut int))]]
         [(l0 [((* outp) = 22)])
          (lX [])
          (l0 [])])))

(define state-3
  (term (,twentytwo-prog
         [(2 (ptr 0)) (0 (int 22)) (1 (ptr 0))]
         [[] [(outp 2)] [(resultp 1)]]
         [[] [(outp (& a mut int))] [(resultp (& l0 mut int))]]
         [(l0 [])
          (lX []) 
          (l0 [])])))

(define state-N
  (term (,twentytwo-prog
         [(0 (int 22))]
         []
         []
         [])))

(module+ test
  (syntactically-correct C state-0)
  (syntactically-correct C state-1)
  (syntactically-correct C state-2)
  (syntactically-correct C state-3)
  (syntactically-correct C state-N)
  
  (test--> machine-step state-0 state-1)
  (test--> machine-step state-1 state-2)
  (test--> machine-step state-2 state-3)
  (test-->> machine-step state-0 state-N))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test summation example

(define sum-state-0
  (term (,sum-prog ,initial-H ,initial-V ,initial-T ,initial-S)))

(define sum-state-N
  (term (,sum-prog [(0 (int 66))] [] [] [])))

(module+ test 
  (syntactically-correct C sum-state-0)
  (syntactically-correct C sum-state-N)
  
  (test-->> machine-step sum-state-0 sum-state-N))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test dst example

(define dst-state-0
  (term (,dst-prog ,initial-H ,initial-V ,initial-T ,initial-S)))

(define dst-state-N
  (term (,dst-prog [(0 (int 69))] [] [] [])))

(module+ test 
  (syntactically-correct C dst-state-0)
  (syntactically-correct C dst-state-N)
  (test-->> machine-step dst-state-0 dst-state-N))

;; ---------------------------------------------------------------------------------------------------
(module+ test
  (test-results))
