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
  [α variable-not-otherwise-mentioned]
  [ρ variable-not-otherwise-mentioned]
  [γ ρ (: x σ) · (γ γ ...) (γ *)] ;; multisequences to avoid associativity
  [Γ (γ ...)]
  [hσ σ (Γ x) (dot σ x)]
  [hγ γ (restrict γ export-ids) (⊔ γ ...) (dot σ *)]
  [C ⊤ bot (:= α hσ) (:= ρ hγ)] ;; represent concatenation with Cs
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
  [(norm-C (C_1 ... ⊤ C_2 ...)) (norm-C (C_1 ... C_2 ...))]
  [(norm-C (C_1 ... bot C_2 ...)) bot]
  [(norm-C Cs) Cs])

;; typing rules

(define-metafunction js
  fresh-ρ :  -> ρ
  [(fresh-ρ) ,(gensym 'ρ)])

(define-metafunction js
  fresh-var :  -> α
  [(fresh-var) ,(gensym 'α)])

(define-judgment-form js
  #:mode (typ/e I I O O)
  #:contract (typ/e Γ e σ Cs)
  
  [(where α (fresh-var))
   ---
   (typ/e Γ x α ((:= α (Γ x))))]
  
  [(typ/e Γ e σ (C ...))
   (where α (fresh-var))
   ---
   (typ/e Γ (dot e x) α (norm-C (C ... (:= α (dot σ x)))))]
  
  [(typ/e Γ n V (⊤))]
  
  [(typ/e Γ e_1 σ_1 (C_1 ...)) 
   (typ/e Γ e_2 σ_2 (C_2 ...))
   ---
   (typ/e Γ (+ e_1 e_2) V (norm-C (C_1 ... C_2 ...)))])


(judgment-holds (typ/e () (+ 3 4) σ_1 Cs_1) (σ_1 Cs_1))

(judgment-holds (typ/e () (+ y (dot z w)) σ_1 Cs_1) (σ_1 Cs_1))


(define-judgment-form js
  #:mode (typ/m I I O O)
  #:contract (typ/m Γ m σ Cs)
  
  [(where α (fresh-var))
   ---
   (typ/m Γ x α ((:= α (Γ x))))]
  
  [(typ/m Γ m σ (C ...))
   (where α (fresh-var))
   (where ρ (fresh-ρ))
   ---
   (typ/m Γ (dot m x) α (norm-C (C ... (:= α (dot σ x)) (:= ρ (dot σ *)))))]
  
  [(where (γ_1 ...) Γ)
   (where ρ_1 (fresh-var))
   (where ρ (fresh-ρ))
   (typ/d (γ_1 ... ρ) d γ_d (C ...)) ...   
   (where γ (⊔ γ_d ...))
   ---
   (typ/m Γ (module d ...) (module ρ_1) (C ... ... (:= ρ γ) (:= ρ_1 (restrict γ (exports d ...)))))])

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
  
  [(typ/d Γ (export x) · (⊤))]
  [(typ/d Γ (export *) · (⊤))]
  
  [(typ/e Γ e σ Cs)
   ---
   (typ/d Γ (let x e) (: x V) Cs)]
  
  [(typ/m Γ m σ (C ...))
   (where α (fresh-var))
   ---
   (typ/d Γ (mod x m) (: x α) (C ... (:= α σ)))]
  
  [(typ/m Γ m σ (C ...))
   (where α (fresh-var))
   (where ρ (fresh-ρ))
   ---
   (typ/d Γ (import m x) (: x α) (C ... (:= α (dot σ x)) (:= ρ (dot σ *))))]
  
  [(typ/m Γ m σ (C ...))   
   (where ρ (fresh-ρ))
   ---
   (typ/d Γ (import m x) (ρ *) (C ... (:= ρ (dot σ *))))]
  )

(define-judgment-form js
  #:mode (typ I O O)
  #:contract (typ (module d ...) γ Cs)
  
  [(typ/m () (module d ...) γ Cs)
   ---
   (typ (module d ...) γ Cs)])

(define-syntax-rule (gen d ...)
  (judgment-holds (typ (module d ...) γ_1 Cs_1) (γ_1 Cs_1)))

(gen (let x 1))


  







