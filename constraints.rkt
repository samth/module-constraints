#lang racket
(require redex/reduction-semantics)


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
  [α (A variable-not-otherwise-mentioned)]
  [ρ (R variable-not-otherwise-mentioned)]
  [γ ρ (: x σ) · (γ γ ...) (γ *)] ;; multisequences to avoid associativity
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
  [(norm-γ (γ_1 ... · γ_2 ...)) (norm-γ (γ_1 ... γ_2 ...))]
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
  
  [(typ/d Γ (export x) · ())]
  [(typ/d Γ (export *) · ())]
  
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

;; solving constraints

;; constraints on signatures
(define-metafunction js 
  solveA : (:= α hσ) -> (:= α hσ) or bot
  [(solveA (:= α ((γ ... (γ_1 ... (: x σ))) x)))
   (:= α σ)]
  [(solveA (:= α ((γ ... (((: x σ) *))) x)))
   (:= α σ)]
  [(solveA (:= α ((γ ... (γ_1 ... ((: x σ_1) *) ((: x σ) *))) x)))
   bot] ;; could allow this 
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
   (:= α V)])

