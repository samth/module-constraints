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
  [α (A variable-not-otherwise-mentioned)]
  [ρ (R variable-not-otherwise-mentioned)]
  
  [σ α V (module ρ)]
  [final-σ V (module ρ)]
  
  [pre-γ γ simple-γ (pre-γ *) (pre-γ ...)] ;; normalized to γ
  
  [γ (simple-γ ...)] ;; multisequences to avoid associativity, · with ()
  [simple-γ base-γ ρ (ρ *)]
  [base-γ (: x σ) ((: x σ) *)]  
  
  [Γ (γ ...)]
  
  [hσ σ (select Γ x) (dot σ x)]
  [hγ γ (restrict γ export-ids) (dot σ *)]
  [C ⊥ (:= α hσ) (:= ρ hγ)] ;; represent concatenation with Cs, ⊤ with ()
  [Cs (C ...)]  
  
  [export-ids (x ...) *]
  )


;; extend the language to support solving constraints

(define-extended-language jsc js
  [σ .... (module γ)]
  [hσ .... (check Γ x) (check* Γ x)]
  [final-σ .... (module γ)])

(define-metafunction jsc
  flatten : pre-γ -> γ
  [(flatten simple-γ) (simple-γ)]
  [(flatten (pre-γ ...))
   (simple-γ ... ...)
   (where ((simple-γ ...) ...) ((flatten pre-γ) ...))]
  [(flatten (pre-γ *))
   ((add-* simple-γ) ...)
   (where (simple-γ ...) (flatten pre-γ))])

(define-metafunction jsc
  add-* : simple-γ -> simple-γ
  [(add-* (simple-γ *)) (simple-γ *)]
  [(add-* simple-γ) (simple-γ *)])

;; totality checking
(module+ testX
  (redex-check js pre-γ_1 (term (flatten pre-γ_1))))

;; implicit equivalences
(define-metafunction js
  norm-γ : pre-γ -> γ
  [(norm-γ ((γ ...) *)) (norm-γ ((γ *) ...))]
  [(norm-γ ((γ *) *)) (norm-γ (γ *))]
  [(norm-γ (γ ...)) ((norm-γ γ) ...)]
  [(norm-γ (γ *)) ((norm-γ γ) *)]
  [(norm-γ γ) γ])

(define-metafunction js
  norm-C : Cs -> Cs  
  [(norm-C (C_1 ... ⊥ C_2 ...)) (⊥)]
  [(norm-C Cs) Cs])

;; typing rules

(define-metafunction js
  fresh-ρ :  -> ρ
  [(fresh-ρ) (R ,(gensym 'ρ))])

(define-metafunction js
  fresh-α :  -> α
  [(fresh-α) (A ,(gensym 'α))])

(define-judgment-form jsc
  #:mode (typ/e I I O O)
  #:contract (typ/e Γ e σ Cs)
  
  [(where α (fresh-α))
   ---
   (typ/e Γ x α ((:= α (select Γ x))))]
  
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
(judgment-holds (typ/e () (dot z w) σ_1 Cs_1) (σ_1 Cs_1))

(judgment-holds (typ/e () (+ y (dot z w)) σ_1 Cs_1) (σ_1 Cs_1))


(define-metafunction jsc
  ⊔ : γ ... -> γ
  [(⊔ γ ...) (flatten (γ ...))])

(define-judgment-form js
  #:mode (typ/m I I O O)
  #:contract (typ/m Γ m σ Cs)
  
  [(where α (fresh-α))
   ---
   (typ/m Γ x α ((:= α (select Γ x))))]
  
  [(typ/m Γ m σ (C ...))
   (where α (fresh-α))
   (where ρ (fresh-ρ))
   ---
   (typ/m Γ (dot m x) α (norm-C (C ... (:= α (dot σ x)) (:= ρ (dot σ *)))))]
  
  [(where ρ   (fresh-ρ))
   (where ρ_1 (fresh-ρ))
   (typ/d (γ_1 ... [ρ]) d γ_d (C_1 ...)) ...
   ---
   (typ/m (γ_1 ...) (module d ...) (module ρ_1) 
          (C_1 ... ...  (:= ρ (⊔ γ_d ...)) (:= ρ_1 (restrict [ρ] (exports d ...)))))])

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
   (typ/d Γ (let x e) [(: x V)] Cs)]
  
  [(typ/m Γ m σ (C ...))
   (where α (fresh-α))
   ---
   (typ/d Γ (mod x m) [(: x α)] (C ... (:= α σ)))]
  
  [(typ/m Γ m σ (C ...))
   (where α (fresh-α))
   (where ρ (fresh-ρ))
   ---
   (typ/d Γ (import m x) [(: x α)] (C ... (:= α (dot σ x)) (:= ρ (dot σ *))))]
  
  [(typ/m Γ m σ (C ...))   
   (where ρ (fresh-ρ))
   ---
   (typ/d Γ (import m *) [(ρ *)] (C ... (:= ρ (dot σ *))))]
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

;; constraints on signatures
(define-metafunction jsc
  solveA : (:= α hσ) -> (C ...)
  ;; failure -- duplicate binding for x
  ;; NOTE -- could succeed here if σ_1 = σ_2
  [(solveA (:= α (select (γ ... (simple-γ_1 ... (: x σ_1) simple-γ_2 ... (: x σ_2) simple-γ_3 ...)) x)))
   (⊥)]
  ;; succeed with no unresolved rows, don't need a check
  ;; NOTE -- this case is an optimization of the next case
  [(solveA (:= α (select (γ ... (base-γ_1 ... (: x σ) base-γ_2 ...)) x)))
   ((:= α σ))]
  ;; possibly-unresolved rows, add a check
  [(solveA (:= α (select (γ ... (simple-γ_1 ... (: x σ) simple-γ_2 ...)) x)))
   ((:= α σ)
    (:= α (check (γ ... (simple-γ_1 ... (: x σ) simple-γ_2 ...)) x)))]
  
  ;; done with this and it failed
  [(solveA (:= α (check (γ ... (simple-γ_1 ... (: x σ_1) simple-γ_2 ... (: x σ) simple-γ_3 ...)) x)))
   (⊥)]
  ;; done with this and it succeeded
  [(solveA (:= α (check (γ ... (base-γ_1 ... (: x σ) base-γ_2 ...)) x)))
   ()]
  
  ;; stars
  
  ;; failure -- duplicate binding for x
  ;; NOTE -- could succeed here if σ_1 = σ_2
  [(solveA (:= α (select (γ ... (simple-γ_1 ... ((: x σ_1) *) simple-γ_2 ... ((: x σ_2) *) simple-γ_3 ...)) x)))
   (⊥)]
  ;; succeed with no unresolved rows, don't need a check
  [(solveA (:= α (select (γ ... (base-γ_1 ... ((: x σ) *) base-γ_2 ...)) x)))
   ((:= α σ))]
  ;; possibly-unresolved rows, add a check
  [(solveA (:= α (select (γ ... (simple-γ_1 ... ((: x σ) *) simple-γ_2 ...)) x)))
   ((:= α σ)
    (:= α (check* (γ ... (simple-γ_1 ... ((: x σ) *) simple-γ_2 ...)) x)))]
  
  ;; done with this and it failed b/c of duplicate *
  [(solveA (:= α (check* (γ ... (simple-γ_1 ... ((: x σ_1) *) simple-γ_2 ... ((: x σ) *) simple-γ_3 ...)) x)))
   (⊥)]
  ;; done with this and it failed b/c of later addition of non-* binding for x
  [(solveA (:= α (check* (γ ... (simple-γ_1 ... (: x σ_1) base-γ_2 ...)) x)))
   (⊥)]
  ;; done with this and it succeeded
  [(solveA (:= α (check* (γ ... (base-γ_1 ... ((: x σ) *) base-γ_2 ...)) x)))
   ()]
  
  ;; all concrete bindings, none of them match `x', search upward
  ;; FIXME -- is this rule right?  do we need to search upwards even if we haven't fully resolved?
  ;; I don't see how it could be right to do that
  [(solveA (:= α ((γ ... (base-γ ...)) x))) 
   ((:= α ((γ ...) x)))]
  
  ;; empty env, fail
  [(solveA (:= α (() x))) 
   (⊥)]
  
  ;; selection out of a module just selects out the relevant row
  [(solveA (:= α (dot (module ρ) x)))
   ((:= α (select [ρ] x)))]
  
  ;; property access on objects is dynamic
  [(solveA (:= α (dot V x)))
   ((:= α V))]
  
  ;; trivial recursive constraints are illegal
  [(solveA (:= α α))
   (⊥)]
  
  ;; otherwise, do nothing
  [(solveA C)
   (C)])

(define-metafunction jsc
  names-of : (base-γ ...) -> (x ...)
  [(names-of ((: x σ) base-γ ...))
   (x_1 ... x_2 ...)
   (where (x_1 ... x x_2 ...) (names-of (base-γ ...)))]
  [(names-of (((: x σ) *) base-γ ...))
   (x_1 ... x_2 ...)
   (where (x_1 ... x x_2 ...) (names-of (base-γ ...)))]
  [(names-of ((: x σ) base-γ ...))
   (x x_1 ...)
   (where (x_1 ...) (names-of (base-γ ...)))]
  [(names-of (((: x σ) *) base-γ ...))
   (x x_1 ...)
   (where (x_1 ...) (names-of (base-γ ...)))]
  [(names-of ()) ()])

(define-metafunction jsc
  plain-names-of : (base-γ ...) -> (x ...)
  [(plain-names-of ((: x σ) base-γ ...))
   (x_1 ... x_2 ...)
   (where (x_1 ... x x_2 ...) (plain-names-of (base-γ ...)))]
  [(plain-names-of (((: x σ) *) base-γ ...))
   (x_1 ...)
   (where (x_1 ...) (plain-names-of (base-γ ...)))]
  [(plain-names-of ((: x σ) base-γ ...))
   (x x_1 ...)
   (where (x_1 ...) (plain-names-of (base-γ ...)))]  
  [(plain-names-of ()) ()])

(define-metafunction jsc 
  solveR : (:= ρ hγ) -> (:= ρ hγ) or ⊥ 
  
  ;; trivial recursion is an error
  ;; NOTE -- could alternatively just drop ρ on the RHS  
  [(solveR (:= ρ (simple-γ_1 ... ρ simple-γ_2 ...)))
   ⊥]
  
  ;; FIXME -- this rule isn't in Andreas' PDF
  ;; trivial recursion is an error through * as well
  [(solveR (:= ρ (simple-γ_1 ... (ρ *) simple-γ_2 ...)))
   ⊥]
  
  ;; importing everything just copies the body
  [(solveR (:= ρ (dot (module ρ_1) *)))
   (:= ρ [ρ_1])]
  
  ;; importing from a non-module name is an error
  [(solveR (:= ρ (dot V *)))
   ⊥]
  
  ;; restricting to * is not a restriction
  [(solveR (:= ρ (restrict γ *)))
   (:= ρ γ)]
  ;; we can only discharge a restriction when we have all concrete names
  [(solveR (:= ρ (restrict (base-γ ...) (x ...))))
   (:= ρ (base-γ ...))
   (side-condition (set=? (apply set (term (x ...)))
                          (apply set (term (names-of (base-γ ...))))))]
  
  ;; trying to restrict a name that isn't available is an error
  [(solveR (:= ρ (restrict (base-γ ...) (x ...))))
   ⊥
   (side-condition (proper-subset? (apply set (term (names-of (base-γ ...))))
                                   (apply set (term (x ...)))))]
  
  ;; discard constraints on names that are restricted
  ;; FIXME -- what if there's a conflict that gets discarded?  can that happen?
  [(solveR (:= ρ (restrict (simple-γ_1 ... (: x σ) simple-γ ...) (x_1 ...))))
   (:= ρ (restrict (simple-γ_1 ... simple-γ ...) (x_1 ...)))
   (side-condition (not (set-member? (apply set (term (x_1 ...)))
                                     (term x))))]
  [(solveR (:= ρ (restrict (simple-γ_1 ... ((: x σ) *) simple-γ ...) (x_1 ...))))
   (:= ρ (restrict (simple-γ_1 ... simple-γ ...) (x_1 ...)))
   (side-condition (not (set-member? (apply set (term (x_1 ...)))
                                     (term x))))]
  
  ;; duplicate constaints on x is an error
  ;; NOTE -- could allow this when σ_1 = σ_2
  [(solveR (:= ρ (simple-γ_0 ... (: x σ_1) simple-γ_1 ... (: x σ_2) simple-γ_2 ...)))
   ⊥]
  ;; drop * constraints on x when there is a non-star binding for x
  [(solveR (:= ρ (simple-γ_0 ... ((: x σ_1) *) simple-γ_1 ... (: x σ_2) simple-γ_2 ...)))
   (:= ρ (simple-γ_0 ... simple-γ_1 ... (: x σ_2) simple-γ_2 ...))]
  [(solveR (:= ρ (simple-γ_0 ... (: x σ_1) simple-γ_1 ... ((: x σ_2) *) simple-γ_2 ...)))
   (:= ρ (simple-γ_0 ... simple-γ_1 ... (: x σ_2) simple-γ_2 ...))]
  
  ;; otherwise, we're done
  [(solveR C) C])

(define-metafunction jsc
  substA : α any any -> any
  [(substA α any_r (:= any_1 any_2))
   (:= any_1 (substA α any_r any_2))]
  [(substA α any_1 α) any_1]
  [(substA α any_1 (any_2 ...)) ((substA α any_1 any_2) ...)]
  [(substA α any_1 any_2) any_2])

;; rows have to be re-normalized, so this is harder
(define-metafunction jsc
  substR : ρ any any -> any
  [(substR ρ any_r (:= any_1 any_2))
   (:= any_1 (substR ρ any_r any_2))]
  [(substR ρ any_1 ρ) any_1]
  
  ;; have to call flatten here to re-normalize
  [(substR ρ any_1 (simple-γ ...))
   (flatten ((substR ρ any_1 simple-γ) ...))]
  
  [(substR ρ any_1 (any_2 ...)) ((substR ρ any_1 any_2) ...)]
  [(substR ρ any_1 any_2) any_2])

(define solver
  (reduction-relation 
   jsc
   #:domain Cs
   ;; fail
   [--> (C_0 ... ⊥ C_1 ....) (⊥) ⊥]
   
   ;; simplify a signature constraint
   [--> (C_0 ... (:= α hσ) C_1 ...)
        (C_0 ... C ... C_1 ...)
        (where (C ...) (solveA (:= α hσ)))
        (where (A x) α)
        (side-condition (not (equal? (term ((:= α hσ))) (term (C ...)))))
        (computed-name (format "solveA ~a" (term x)))]
   
   ;; simplify a row constraint
   [--> (C_0 ... (:= ρ hγ) C_1 ...)
        (C_0 ... C C_1 ...)
        (where (R x) ρ)
        (where C (solveR (:= ρ hγ)))
        (side-condition (not (equal? (term (:= ρ hγ)) (term C))))
        (computed-name (format "solveR ~a" (term x)))]
   
   ;; substitute a row
   [--> (C_0 ... (:= ρ γ) C_1 ...)
        (C_2 ... (:= ρ γ) C_3 ...)
        (where (R x) ρ)
        (where (C_2 ...) (substR ρ γ (C_0 ...)))
        (where (C_3 ...) (substR ρ γ (C_1 ...)))
        ;; only do this if we can't simplify first
        (side-condition (equal? (term (:= ρ γ)) (term (solveR (:= ρ γ)))))
        ;; don't substitute if it doesn't make progress
        (side-condition (not (equal? (term (C_0 ... C_1 ...)) (term (C_2 ... C_3 ...)))))
        (computed-name (format "substR ~a" (term x)))]
   ;; substitute a signature
   [--> (C_0 ... (:= α final-σ) C_1 ...)
        (C_2 ... (:= α final-σ) C_3 ...)
        (where (A x) α)
        (where (C_2 ...) (substA α final-σ (C_0 ...)))
        (where (C_3 ...) (substA α final-σ (C_1 ...)))
        ;; only do this if we can't simplify first
        (side-condition (equal? (term ((:= α final-σ))) (term (solveA (:= α final-σ)))))
        ;; don't substitute if it doesn't make progress
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

#;
(go (constraints-of (mod x (module (export X) (let X 1) (let Y 2)))     
                    (import x *)))

(define fail 
  '((:= (R ρ29966) ((: X V) (: Y V)))
    (:= (R ρ29967) ((: X V)))
    (:= (A α29969) (module ((: X V))))
    (:= (A α29970) (((R ρ29963)) x))
    (:= (R ρ29971) (dot (A α29970) *))
    (:= (R ρ29963) (⊔ (: x (module ((: X V)))) ((R ρ29971) *)))
    (:= (R ρ29964) (restrict (R ρ29963) ()))))
