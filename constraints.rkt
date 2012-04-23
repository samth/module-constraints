#lang racket
(require redex/reduction-semantics)

(caching-enabled? #f)

(define-language js
  ;; section 1 of andreas' pdf
  [e x (dot e x) n (+ e e)]
  [m x (dot m x) (module d ...)] ;; explicitly use a sequence here
  [d (let x e) (mod x m) (export x) (export *) (import m x) (import m *)]
  [n number]
  [x variable-not-otherwise-mentioned]
  [program (d ...)]
  ;; section 2
  [σ α V (module ρ)]
  [final-σ V (module ρ)]
  [α (A variable-not-otherwise-mentioned)]
  [ρ (R variable-not-otherwise-mentioned)]
  [final-γ simple-γ (simple-γ ...)]
  [γ ρ (: x σ) (γ ...) (γ *)] ;; multisequences to avoid associativity, · with ()
  [simple-γ (: x σ) ((: x σ) *)]
  [Γ (γ ...)]
  [hσ σ (Γ x) (dot σ x)]
  [hγ γ (restrict γ export-ids) (⊔ γ ...) (dot σ *)]
  [C bot (:= α hσ) (:= ρ hγ)] ;; represent concatenation with Cs, ⊤ with ()
  [Cs (C ...)]  
  [export-ids (x ...) *]
  )

;; implicit equivalences
(define-metafunction js
  norm-γ : γ -> γ
  [(norm-γ (γ_1 ... γ_2 ...)) (norm-γ (γ_1 ... γ_2 ...))]
  [(norm-γ ((γ ...) *)) (norm-γ ((γ *) ...))]
  [(norm-γ ((γ *) *)) (norm-γ (γ *))]
  [(norm-γ (γ ...)) ((norm-γ γ) ...)]
  [(norm-γ (γ *)) ((norm-γ γ) *)]
  [(norm-γ γ) γ])

(define-metafunction js
  norm-C : Cs -> Cs  
  [(norm-C (C_1 ... bot C_2 ...)) bot]
  [(norm-C Cs) Cs])

;; typing rules

(define-metafunction js
  fresh-ρ :  -> ρ
  [(fresh-ρ) (R ,(gensym 'ρ))])

(define-metafunction js
  fresh-α :  -> α
  [(fresh-α) (A ,(gensym 'α))])

(define-judgment-form js
  #:mode (typ/e I I O O)
  #:contract (typ/e Γ e σ Cs)
  
  [(where α (fresh-α))
   ---
   (typ/e Γ x α ((:= α (Γ x))))]
  
  [(typ/e Γ e σ (C ...))
   (where α (fresh-α))
   ---
   (typ/e Γ (dot e x) α (norm-C (C ... (:= α (dot σ x)))))]
  
  [(typ/e Γ n V ())]
  
  [(typ/e Γ e_1 σ_1 (C_1 ...)) 
   (typ/e Γ e_2 σ_2 (C_2 ...))
   ---
   (typ/e Γ (+ e_1 e_2) V (norm-C (C_1 ... C_2 ...)))])


(judgment-holds (typ/e () (+ 3 4) σ_1 Cs_1) (σ_1 Cs_1))

(judgment-holds (typ/e () (+ y (dot z w)) σ_1 Cs_1) (σ_1 Cs_1))


(define-judgment-form js
  #:mode (typ/m I I O O)
  #:contract (typ/m Γ m σ Cs)
  
  [(where α (fresh-α))
   ---
   (typ/m Γ x α ((:= α (Γ x))))]
  
  [(typ/m Γ m σ (C ...))
   (where α (fresh-α))
   (where ρ (fresh-ρ))
   ---
   (typ/m Γ (dot m x) α (norm-C (C ... (:= α (dot σ x)) (:= ρ (dot σ *)))))]
  
  [(where ρ   (fresh-ρ))
   (where ρ_1 (fresh-ρ))
   (where ρ_2 (fresh-ρ))
   (typ/d (γ_1 ... ρ) d γ_d (C_1 ...)) ...
   (where (C_new ...) (C_1 ... ...  (:= ρ (⊔ γ_d ...)) (:= ρ_1 (restrict ρ (exports d ...)))))
   ;(where γ )
   ---
   (typ/m (γ_1 ...) (module d ...) (module ρ_1) (C_new ...))])

(define-metafunction js
  exports : d ... -> export-ids
  [(exports d ...) (join-exports (export1 d) ...)])

(define-metafunction js
  export1 : d -> export-ids
  [(export1 (export x)) (x)]
  [(export1 (export *)) *]
  [(export1 d) ()])

(define-metafunction js
  join-exports : export-ids ... -> export-ids
  [(join-exports any_1 ... * any_2 ...) *]
  [(join-exports (x ...) ...) (x ... ...)])

(define-judgment-form js
  #:mode (typ/d I I O O)
  #:contract (typ/d Γ d γ Cs)
  
  [(typ/d Γ (export x) () ())]
  [(typ/d Γ (export *) () ())]
  
  [(typ/e Γ e σ Cs)
   ---
   (typ/d Γ (let x e) (: x V) Cs)]
  
  [(typ/m Γ m σ (C ...))
   (where α (fresh-α))
   ---
   (typ/d Γ (mod x m) (: x α) (C ... (:= α σ)))]
  
  [(typ/m Γ m σ (C ...))
   (where α (fresh-α))
   (where ρ (fresh-ρ))
   ---
   (typ/d Γ (import m x) (: x α) (C ... (:= α (dot σ x)) (:= ρ (dot σ *))))]
  
  [(typ/m Γ m σ (C ...))   
   (where ρ (fresh-ρ))
   ---
   (typ/d Γ (import m *) (ρ *) (C ... (:= ρ (dot σ *))))]
  )

(define-judgment-form js
  #:mode (typ I O O)
  #:contract (typ (module d ...) σ Cs)
  
  [(typ/m () (module d ...) σ Cs)
   ---
   (typ (module d ...) σ Cs)])

(define-syntax-rule (gen d ...)
  (judgment-holds (typ (module d ...) σ_1 Cs_1) (σ_1 Cs_1)))

(gen (let x 1))

(gen (import x *))

(gen (mod x (module (export X) (let X 1) (let Y 2)))     
     (import x *))

(define-syntax-rule (constraints-of d ...)
  (match-let ([(list (list sig con-set)) (judgment-holds (typ (module d ...) σ_1 Cs_1) (σ_1 Cs_1))])
    con-set))

;; solving constraints

(define-extended-language jsc js
  [σ .... (module γ)]
  [final-σ .... (module γ)])

;; constraints on signatures
(define-metafunction jsc
  solveA : (:= α hσ) -> (:= α hσ) or bot
  [(solveA (:= α ((γ ... (γ_1 ... (: x σ))) x)))
   (:= α σ)]
  [(solveA (:= α ((γ ... (((: x σ) *))) x)))
   (:= α σ)]
  [(solveA (:= α ((γ ... (γ_1 ... ((: x σ_1) *) ((: x σ) *))) x)))
   bot] ;; could allow this if σ = σ_1
  [(solveA (:= α ((γ ... (γ_1 ... (: x_1 σ))) x)))
   (:= α ((γ ... (γ_1 ...)) x))
   (side-condition (not (equal? (term x) (term x_1))))]
  [(solveA (:= α ((γ ... (γ_1 ... ((: x_1 σ) *))) x))) 
   (:= α ((γ ... (γ_1 ...)) x))
   (side-condition (not (equal? (term x) (term x_1))))]
  [(solveA (:= α ((γ ... ()) x))) 
   (:= α ((γ ...) x))]
  [(solveA (:= α (() x))) 
   bot]
  [(solveA (:= α (dot (module ρ) x)))
   (:= α ((ρ) x))]
  [(solveA (:= α (dot V x)))
   (:= α V)]
  [(solveA (:= α α))
   bot]
  [(solveA C) C])

(define-metafunction jsc
  names-of : (simple-γ ...) -> (x ...)
  [(names-of ((: x σ) γ ...))
   (x_1 ... x_2 ...)
   (where (x_1 ... x x_2 ...) (names-of (γ ...)))]
  [(names-of (((: x σ) *) γ ...))
   (x_1 ... x_2 ...)
   (where (x_1 ... x x_2 ...) (names-of (γ ...)))]
  [(names-of ((: x σ) γ ...))
   (x x_1 ...)
   (where (x_1 ...) (names-of (γ ...)))]
  [(names-of (((: x σ) *) γ ...))
   (x x_1 ...)
   (where (x_1 ...) (names-of (γ ...)))]
  [(names-of ()) ()])

(define-metafunction jsc
  plain-names-of : (simple-γ ...) -> (x ...)
  [(plain-names-of ((: x σ) γ ...))
   (x_1 ... x_2 ...)
   (where (x_1 ... x x_2 ...) (plain-names-of (γ ...)))]
  [(plain-names-of (((: x σ) *) γ ...))
   (x_1 ...)
   (where (x_1 ...) (plain-names-of (γ ...)))]
  [(plain-names-of ((: x σ) γ ...))
   (x x_1 ...)
   (where (x_1 ...) (plain-names-of (γ ...)))]  
  [(plain-names-of ()) ()])

(define-metafunction jsc 
  solveR : (:= ρ hγ) -> (:= ρ hγ) or bot  
  [(solveR (:= ρ (γ_1 ... ρ γ_2 ...)))
   bot]
  [(solveR (:= ρ (dot (module ρ_1) *)))
   (:= ρ ρ_1)]
  [(solveR (:= ρ (dot V *)))
   bot]
  [(solveR (:= ρ (restrict γ *)))
   (:= ρ γ)]
  [(solveR (:= ρ (restrict (simple-γ ...) (x ...))))
   (:= ρ (simple-γ ...))
   (side-condition (set=? (apply set (term (x ...)))
                          (apply set (term (names-of (simple-γ ...))))))]
  [(solveR (:= ρ (restrict (simple-γ ...) (x ...))))
   bot
   (side-condition (proper-subset? (apply set (term (names-of (simple-γ ...))))
                                   (apply set (term (x ...)))))]
  [(solveR (:= ρ (restrict (γ_1 ... (: x σ) γ ...) (x_1 ...))))
   (:= ρ (restrict (γ_1 ... γ ...) (x_1 ...)))
   (side-condition (not (set-member? (apply set (term (x_1 ...)))
                                     (term x))))]
  [(solveR (:= ρ (restrict (γ_1 ... ((: x σ) *) γ ...) (x_1 ...))))
   (:= ρ (restrict (γ_1 ... γ ...) (x_1 ...)))
   (side-condition (not (set-member? (apply set (term (x_1 ...)))
                                     (term x))))]
  [(solveR (:= ρ (⊔ γ)))
   (:= ρ γ)]
  [(solveR (:= ρ (⊔ γ_1 ... () γ_2 ...)))
   (:= ρ (⊔ γ_1 ... γ_2 ...))]
  
  [(solveR (:= ρ (⊔ simple-γ_1 ...)))
   (:= ρ (simple-γ_1 ...))]
  
  [(solveR (:= ρ (⊔ ((: x σ_1) γ_1 ...) ((: x σ_2) γ_2 ...) γ_3 ...)))
   bot]
  [(solveR (:= ρ (⊔ (((: x σ_1) *) γ_1 ...) ((: x σ_2) γ_2 ...) γ_3 ...)))
   (:= ρ (⊔ (γ_1 ...) ((: x σ_2) γ_2 ...) γ_3 ...))]
  
  [(solveR (:= ρ (⊔ ((: x σ_1) γ_1 ...) (simple-γ_2 ...) γ_3 ...)))
   (:= ρ (⊔ (γ_1 ...) ((: x σ_1) simple-γ_2 ...) γ_3 ...))
   (side-condition (not (set-member? (apply set (term (names-of (simple-γ_2 ...))))
                                     (term x))))]
  [(solveR (:= ρ (⊔ (((: x σ_1) *) γ_1 ...) (simple-γ_2 ...) γ_3 ...)))
   (:= ρ (⊔ (γ_1 ...) (((: x σ_1) *) simple-γ_2 ...) γ_3 ...))
   (side-condition (not (set-member? (apply set (term (plain-names-of (simple-γ_2 ...))))
                                     (term x))))]
  [(solveR C) C])

(define-metafunction jsc
  substA : α any any -> any
  [(substA α any_r (:= any_1 any_2))
   (:= any_1 (substA α any_r any_2))]
  [(substA α any_1 α) any_1]
  [(substA α any_1 (any_2 ...)) ((substA α any_1 any_2) ...)]
  [(substA α any_1 any_2) any_2])

(define-metafunction jsc
  substR : ρ any any -> any
  [(substR ρ any_r (:= any_1 any_2))
   (:= any_1 (substR ρ any_r any_2))]
  [(substR ρ any_1 ρ) any_1]
  [(substR ρ any_1 (any_2 ...)) ((substR ρ any_1 any_2) ...)]
  [(substR ρ any_1 any_2) any_2])

(define solver
  (reduction-relation 
   jsc
   #:domain Cs
   [--> (C_0 ... bot C_1 ....) (bot) bot]
   [--> (C_0 ... (:= α hσ) C_1 ...)
        (C_0 ... C C_1 ...)
        (where C (solveA (:= α hσ)))
        (where (A x) α)
        (side-condition (not (equal? (term (:= α hσ)) (term C))))
        (computed-name (format "solveA ~a" (term x)))]
   [--> (C_0 ... (:= ρ hγ) C_1 ...)
        (C_0 ... C C_1 ...)
        (where (R x) ρ)
        (where C (solveR (:= ρ hγ)))
        (side-condition (not (equal? (term (:= ρ hγ)) (term C))))
        (computed-name (format "solveR ~a" (term x)))]
   [--> (C_0 ... (:= ρ final-γ) C_1 ...)
        (C_2 ... (:= ρ final-γ) C_3 ...)
        (where (R x) ρ)
        (where (C_2 ...) (substR ρ final-γ (C_0 ...)))
        (where (C_3 ...) (substR ρ final-γ (C_1 ...)))
        (side-condition (not (equal? (term (C_0 ... C_1 ...)) (term (C_2 ... C_3 ...)))))
        (computed-name (format "substR ~a" (term x)))]
   [--> (C_0 ... (:= α final-σ) C_1 ...)
        (C_2 ... (:= α final-σ) C_3 ...)
        (where (A x) α)
        (where (C_2 ...) (substA α final-σ (C_0 ...)))
        (where (C_3 ...) (substA α final-σ (C_1 ...)))
        (side-condition (not (equal? (term (C_0 ... C_1 ...)) (term (C_2 ... C_3 ...)))))
        (computed-name (format "substA ~a" (term x)))]))

(require unstable/lazy-require)
(lazy-require [redex (traces)])

(define (go cs)
  (traces solver cs))

(define d 
  '((:= (R ρ1456) (⊔ () (: X V) (: Y V)))
    (:= (R ρ1457) (restrict (R ρ1456) (X)))
    (:= (A α1459) (module (R ρ1457)))
    (:= (A α1460) (((R ρ1453)) x))
    (:= (R ρ1461) (dot (A α1460) *))
    (:= (R ρ1453) (⊔ (: x (A α1459)) ((R ρ1461) *)))
    (:= (R ρ1454) (restrict (R ρ1453) ()))))


(go (constraints-of (mod x (module (export X) (let X 1) (let Y 2)))     
                    (import x *)))

(define fail '((:=
                (R ρ29966)
                ((: X V) (: Y V)))
               (:= (R ρ29967) ((: X V)))
               (:=
                (A α29969)
                (module ((: X V))))
               (:=
                (A α29970)
                (((R ρ29963)) x))
               (:=
                (R ρ29971)
                (dot (A α29970) *))
               (:=
                (R ρ29963)
                (⊔
                 (: x (module ((: X V))))
                 ((R ρ29971) *)))
               (:=
                (R ρ29964)
                (restrict (R ρ29963) ()))))
