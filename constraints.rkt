#lang racket
(require redex/reduction-semantics)

(caching-enabled? #f)

(define-syntax-rule (module+ _ ...) (begin))

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
  
  [σ α V (module [ρ])]
  [final-σ V (module γ)]
  
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
  [simple-C (:= α final-σ) (:= ρ γ)]
  [solved-C (:= α solved-σ) (:= ρ solved-γ)]
  [solved-σ V (module solved-γ)]
  [solved-γ (solved-base-γ ...)]
  [solved-base-γ (: x solved-σ) ((: x solved-σ) *)])

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
   (typ/m (γ_1 ...) (module d ...) (module [ρ_1]) 
          (C_1 ... ...  (:= ρ (flatten (γ_d ...))) (:= ρ_1 (restrict [ρ] (exports d ...)))))])

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
    (:= α (check* (γ ... (simple-γ_1 ... ((: x σ) *) simple-γ_2 ...)) x)))
   ;; can't select an x that's starred if anything else might become an unstarred x
   (side-condition (for/and ([t (term (simple-γ_1 ... simple-γ_2 ...))])
                       (not (redex-match jsc ρ t))))]
  
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
  name-in : (simple-γ ...) x -> #t or #f
  [(name-in ((: x σ) simple-γ ...) x) #t]
  [(name-in (((: x σ) *) simple-γ ...) x) #t]
  [(name-in () x) #f]
  [(name-in (simple-γ simple-γ_1 ...) x)
   (name-in (simple-γ_1 ...) x)])

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
  [(solveR (:= ρ (dot (module γ) *)))
   (:= ρ γ)]
  
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
   (solveR (:= ρ (restrict (simple-γ_1 ... simple-γ ...) (x_1 ...))))
   (side-condition (not (term (name-in (simple-γ_1 ...) x))))
   (side-condition (not (set-member? (apply set (term (x_1 ...)))
                                     (term x))))]
  [(solveR (:= ρ (restrict (simple-γ_1 ... ((: x σ) *) simple-γ ...) (x_1 ...))))
   (:= ρ (restrict (simple-γ_1 ... simple-γ ...) (x_1 ...)))
   (side-condition (not (term (name-in (simple-γ_1 ...) x))))
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

(define-metafunction jsc
  subst : simple-C any -> any
  [(subst (:= α final-σ) any)
   (substA α final-σ any)]
  [(subst (:= ρ γ) any)
   (substR ρ γ any)])

(define-metafunction jsc
  solve : C -> (C ...)
  [(solve (:= α hσ)) (solveA (:= α hσ))]
  [(solve (:= ρ hγ)) [(solveR (:= ρ hγ))]])

(define-metafunction jsc
  cname : C -> x
  [(cname (:= (A x) hσ)) x]
  [(cname (:= (R x) hγ)) x])

(define-metafunction jsc
  solvable? : C -> #t or #f
  [(solvable? C) ,(not (equal? (term (C)) (term (solve C))))])

(define-metafunction jsc
  substable? : C (C ...) -> #t or #f
  [(substable? simple-C (C ...))
   ,(not (equal? (term (C ...))
                 (term (subst simple-C (C ...)))))]
  [(substable? C any) #f])

(define solver
  (reduction-relation 
   jsc
   #:domain (C ...)
   ;; fail
   [--> (C_0 ... ⊥ C_1 ....) (⊥) ⊥]
   
   ;; simplify a signature constraint
   [--> (C_0 ... C_s C_1 ...)
        (C_0 ... C ... C_1 ...)
        (where (C ...) (solve C_s))        
        (side-condition (not (equal? (term (C_s)) (term (C ...)))))
        (side-condition (not (ormap (λ (e) (term (solvable? ,e))) (term (C_0 ...)))))
        (computed-name (format "solve ~a" (term (cname C_s))))]   
   
   ;; substitute
   [--> (C_0 ... simple-C C_1 ...)
        (C_2 ... simple-C C_3 ...)
        ;; only do this if we can't simplify something first        
        (side-condition (for/and ([t (term (C_0 ... simple-C C_1 ...))])
                          (not (term (solvable? ,t)))))
        ;; make sure nothing else earlier is substable
        (side-condition (for/and ([t (term (C_0 ...))])
                         (not (term (substable? ,t (C_0 ... simple-C C_1 ...))))))
        (where (C_2 ...) (subst simple-C (C_0 ...)))
        (where (C_3 ...) (subst simple-C (C_1 ...)))
        ;; don't substitute if it doesn't make progress
        (side-condition (not (equal? (term (C_0 ... C_1 ...)) (term (C_2 ... C_3 ...)))))
        (computed-name (format "subst ~a" (term (cname simple-C))))]))

(require unstable/lazy-require)
(lazy-require [redex (traces)])

(define (go cs)
  (traces solver cs #:pred (λ (e) (if (term (final-state ,e))
                                      "green"
                                      #true))))

(define-metafunction jsc
  final-state : (C ...) -> #t or #f
  [(final-state (solved-C ...)) #t]
  [(final-state (C ...)) #f])

(module+ test
  (judgment-holds (typ/e () (+ 3 4) σ_1 Cs_1) (σ_1 Cs_1))
  (judgment-holds (typ/e () (dot z w) σ_1 Cs_1) (σ_1 Cs_1))
  
  (judgment-holds (typ/e () (+ y (dot z w)) σ_1 Cs_1) (σ_1 Cs_1))
  (gen (let x 1))
  
  (gen (import x *))
  
  (gen (mod x (module (export X) (let X 1) (let Y 2)))     
       (import x *)))

(define-syntax-rule (run d ...)
  (go (constraints-of d ...)))
#;#;
(run (mod x (module (export X) (let X 1) (let Y 2)))     
     (import x *))

(run 
 (mod y (module (export X) (let X 1)))
 (mod x (module (export X) (import y *) (let Y 2)))
 (import x *))

(define stuck2
  '((:= (R ρ68) ((: X V)))
    (:= (R ρ69) ((: X V)))
    (:= (A α70) (module ((: X V))))
    (:=
     (A α73)
     (select (((: y (module ((: X V)))) (: x (module ((R ρ72)))) ((R ρ72) *)) (((R ρ74) *) (: Y V))) y))
    (:= (R ρ74) (dot (A α73) *))
    (:= (R ρ71) (((R ρ74) *) (: Y V)))
    (:= (R ρ72) (restrict (((R ρ74) *)) (X)))
    (:= (A α75) (module ((R ρ72))))
    (:= (A α76) (module ((R ρ72))))
    (:= (A α76) (check (((: y (module ((: X V)))) (: x (module ((R ρ72)))) ((R ρ72) *))) x))
    (:= (R ρ77) ((R ρ72)))
    (:= (R ρ66) ((: y (module ((: X V)))) (: x (module ((R ρ72)))) ((R ρ72) *)))
    (:= (R ρ67) (restrict (((R ρ72) *)) ()))))

