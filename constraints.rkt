#lang racket
(require redex/reduction-semantics)


(define-language js
  ;; section 1 of andreas' pdf
  [e x (dot e x) n (+ e e)]
  [m x (dot m x) (b d ...)] ;; explicitly use a sequence here
  [d (let x e) (mod x m) (export x) (export *) (import m x) (import m *)]
  [n number]
  [x variable-not-otherwise-mentioned]
  [program (d ...)]
  ;; section 2
  [σ α V (ρ)]
  [α variable-not-otherwise-mentioned]
  [ρ variable-not-otherwise-mentioned]
  [γ ρ (: x σ) · (γ γ ...) (γ *)] ;; multisequences to avoid associativity
  [Γ (γ ...)]
  [hσ σ (Γ x) (dot σ x)]
  [hγ γ (restrict γ x ...) (⊔ γ ...) (dot σ *)]
  [C ⊤ bot (:= α hσ) (:= ρ hγ)] ;; represent concatenation with Cs
  [Cs (C ...)]
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
  [(norm-C (C_1 ... ⊤ C_2 ...)) bot]
  [(norm-C Cs) Cs])
