module correctness.dsyn-defined where

open import Agda.Builtin.Unit using (⊤)
open import Data.Sum using ([_,_])
open import Data.Maybe using (Is-just)
open import Data.Product.Base using (_×_)
open import Function.Base using (case_of_)

open import spec 
open import correctness.dsem
open import correctness.spec

DSyn-ExistsP-Prim : {σ τ : Typ Pr} → Primop Pr σ τ → Rep σ → Set
DSyn-ExistsP-Prim {σ} {τ} op x = Is-just (DSemᵀ {σ} {τ} (evalprim op) x)

-- A predicate stating that the syntactic derivative exists for a valuation and term.
DSyn-ExistsP : {Γ : Env Pr} {τ : Typ Pr} → Val Pr Γ → Term Pr Γ τ → Set
DSyn-ExistsP val (unit) = ⊤ 
DSyn-ExistsP val (var idx) = ⊤
DSyn-ExistsP val (pair l r) = DSyn-ExistsP val l × DSyn-ExistsP val r
DSyn-ExistsP val (fst' t) = DSyn-ExistsP val t
DSyn-ExistsP val (snd' t) = DSyn-ExistsP val t
DSyn-ExistsP val (let' rhs body) = DSyn-ExistsP val rhs × DSyn-ExistsP (push (interp rhs val) val) body
DSyn-ExistsP val (prim op t) = DSyn-ExistsP-Prim op (interp t val) × DSyn-ExistsP val t
DSyn-ExistsP val (inl t) = DSyn-ExistsP val t
DSyn-ExistsP val (inr t) = DSyn-ExistsP val t
DSyn-ExistsP val (case' e l r) = DSyn-ExistsP val e × (case interp e val of
                    [ ( λ v' → DSyn-ExistsP (push v' val) l )
                    , ( λ v' → DSyn-ExistsP (push v' val) r )
                    ])

-- =======================================
-- A datatype wrapper for DSyn-ExistsP.
-- =======================================
-- MOTIVATION:
-- For chad-equiv-dsem, when the term is (case' e l r), we wish to perform a with-abstraction on 'interp e (Etup-to-val a)'.
-- If chad-equiv-dsem has DSyn-ExistsP in its goal, then this with-abstraction also impacts this.
-- This leads to an ill-typed abstraction, as 'interp e (Etup-to-val a)' is part of the definition of DSyn-ExistsP.
-- Instead, we want to only apply this with-abstraction on the term.
-- By wrapping the predicate in a constructor, this with abstraction no longer effects it.
-- Then, after having done a with-abstraction on 'interp e (Etup-to-val a)', we can with-abstract on DSyn-Exists to obtain the underlying predicate.
data DSyn-Exists : {Γ : Env Pr} {τ : Typ Pr} → Val Pr Γ → Term Pr Γ τ → Set where
    ∃dsyn :  {Γ : Env Pr} {τ : Typ Pr} → { val : Val Pr Γ } → { t : Term Pr Γ τ } → (DSyn-ExistsP val t)  → DSyn-Exists val t



-- In this module we proof that when the syntactic derivative is well-defined,
-- then the semantic derivative is also well-defined.
module DSyn-defined-implies-DSem-defined where
    open import Agda.Builtin.Equality using (_≡_; refl)
    open import Agda.Builtin.Sigma using (_,_; fst; snd)
    open import Agda.Builtin.Unit using (tt)
    open import Agda.Builtin.Float using (primFloatLess)

    open import Data.Empty using (⊥)
    open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
    open import Data.List using ([]; _∷_)
    open import Function.Base using (_∘_; _$_; case_of_; id)
    open import Function.Bundles using (Equivalence)
    open import Relation.Binary.PropositionalEquality using (sym; _≗_)
    import Data.Maybe.Relation.Unary.Any as Any

    open import spec
    open import correctness.spec
    open import correctness.dsem
    open import correctness.lemmas.dsem-lemmas
    open apply-cong[,]

    private module case-helper {Γ : Env Pr} {σ τ ρ : Typ Pr} (a : Rep (Etup Pr Γ)) (e : Term Pr Γ (σ :+ τ)) (l : Term Pr (σ ∷ Γ) ρ) (r : Term Pr (τ ∷ Γ) ρ) where
        f : (Rep $ (σ :+ τ) :* Etup Pr Γ) → Rep ρ
        f = λ (cond , a') → [ (λ v → interp l $ Etup-to-val (v , a'))
                            , (λ v → interp r $ Etup-to-val (v , a'))
                            ] cond
        g : (a' : Rep (Etup Pr Γ)) → Rep ((σ :+ τ) :* Etup Pr Γ)
        g = λ a' → interp e (Etup-to-val a') , a'

        case-simp-ext : (f ∘ g) ≗ interp (case' e l r) ∘ Etup-to-val
        case-simp-ext a' with (interp e (Etup-to-val a'))
        ... | inj₁ _ = refl
        ... | inj₂ _ = refl

    ∃DSyn→∃DSem : {Γ : Env Pr} {τ : Typ Pr}  ( a : Rep (Etup Pr Γ) ) → ( t : Term Pr Γ τ ) 
        → DSyn-ExistsP (Etup-to-val a) t → (Is-just (DSemᵀ {Etup Pr Γ} {τ} (interp t ∘ Etup-to-val) a))
    ∃DSyn→∃DSem {Γ} {τ} a ( unit ) w = DSemᵀ-exists-unit a
    ∃DSyn→∃DSem {Γ} {τ} a ( var idx ) w = DSemᵀ-var a idx (zerovDense (D2τ' τ)) .fst
    ∃DSyn→∃DSem {Γ} {τ} a ( pair l r ) w = DSemᵀ-exists-lemma-pair₂ (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) a (∃DSyn→∃DSem a l (w .fst) , ∃DSyn→∃DSem a r (w .snd))
    ∃DSyn→∃DSem {Γ} {τ} a ( fst' t ) w = DSemᵀ-exists-lemma-chain fst (interp t ∘ Etup-to-val) a (DSemᵀ-fst (interp t $ Etup-to-val a) (zerovDense (D2τ' τ))  .fst) (∃DSyn→∃DSem a t w)
    ∃DSyn→∃DSem {Γ} {τ} a ( snd' t ) w = DSemᵀ-exists-lemma-chain snd (interp t ∘ Etup-to-val) a (DSemᵀ-snd (interp t $ Etup-to-val a) (zerovDense (D2τ' τ))  .fst) (∃DSyn→∃DSem a t w)
    ∃DSyn→∃DSem {Γ} {τ} a ( let' {σ = σ} rhs body ) w =
      let ih-rhs = DSemᵀ-exists-lemma-pair₂ (interp rhs ∘ Etup-to-val) id a (∃DSyn→∃DSem a rhs (fst w) , DSemᵀ-exists-lemma-identity a) 
          ih-body = ∃DSyn→∃DSem (interp rhs (Etup-to-val a) , a) body (snd w)
      in DSemᵀ-exists-lemma-chain {Etup Pr Γ} {σ :* Etup Pr Γ} {τ} (interp body ∘ Etup-to-val) (λ z → interp rhs (Etup-to-val z) , z) a ih-body ih-rhs
    ∃DSyn→∃DSem {Γ} {τ} a ( prim {σ = σ} op t ) w = DSemᵀ-exists-lemma-chain {τ2 = σ} (evalprim op) (interp t ∘ Etup-to-val) a (w .fst) (∃DSyn→∃DSem a t (w .snd))
    ∃DSyn→∃DSem {Γ} {τ} a ( inl t ) w = DSemᵀ-exists-lemma-chain inj₁ (interp t ∘ Etup-to-val) a (DSemᵀ-inj₁ (interp t $ Etup-to-val a) (zerovDense (D2τ' _ :*! D2τ' _)) .fst) (∃DSyn→∃DSem a t w) 
    ∃DSyn→∃DSem {Γ} {τ} a ( inr t ) w = DSemᵀ-exists-lemma-chain inj₂ (interp t ∘ Etup-to-val) a (DSemᵀ-inj₂ (interp t $ Etup-to-val a) (zerovDense (D2τ' _ :*! D2τ' _)) .fst) (∃DSyn→∃DSem a t w) 
    ∃DSyn→∃DSem {Γ} {τ} a ( case' e l r ) w
      using f ← case-helper.f a e l r
      using g ← case-helper.g a e l r
      using ext ← case-helper.case-simp-ext a e l r
      using de ← ∃DSyn→∃DSem a e (fst w)
      using dg ← DSemᵀ-exists-lemma-pair₂ (interp e ∘ Etup-to-val) id a (de , DSemᵀ-exists-lemma-identity a)
      with interp e (Etup-to-val a) in eq1
    ∃DSyn→∃DSem {Γ} a (case' {σ = σ} {τ = τ} e l r) (we , wl) | inj₁ x
      = let dl = ∃DSyn→∃DSem (x , a) l wl
            df = Equivalence.from (DSemᵀ-exists-lemma-case-inj₁ (g a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) x eq1) dl
            df∘g = DSemᵀ-exists-lemma-chain {τ2 = (σ :+ τ) :* Etup Pr Γ} f g a df dg
      in DSemᵀ-exists-extensionality (f ∘ g) _ ext a df∘g
    ∃DSyn→∃DSem {Γ} a (case' {σ = σ} {τ = τ} e l r) (we , wr) | inj₂ x
      = let dr = ∃DSyn→∃DSem (x , a) r wr
            df = Equivalence.from (DSemᵀ-exists-lemma-case-inj₂ (g a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) x eq1) dr
            df∘g = DSemᵀ-exists-lemma-chain {τ2 = (σ :+ τ) :* Etup Pr Γ} f g a df dg
      in DSemᵀ-exists-extensionality (f ∘ g) _ ext a df∘g

    DSyn-Exists→DSem-Exists : {Γ : Env Pr} {τ : Typ Pr}  ( a : Rep (Etup Pr Γ) ) → ( t : Term Pr Γ τ ) 
        → DSyn-Exists (Etup-to-val a) t → (Is-just (DSemᵀ {Etup Pr Γ} {τ} (interp t ∘ Etup-to-val) a))
    DSyn-Exists→DSem-Exists a t (∃dsyn x) = ∃DSyn→∃DSem a t x

open DSyn-defined-implies-DSem-defined public