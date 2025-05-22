{-# OPTIONS --allow-unsolved-metas #-}
module correctness.lemmas.dsem-interp-lemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_×_; uncurry; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; isInj₁; isInj₂)
open import Data.Maybe using (Maybe; Is-just; to-witness; just; nothing; maybe; from-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; _+_)
import Data.Maybe.Relation.Unary.Any as Any
open import Function.Bundles using (_⇔_;  mk⇔; Equivalence)
open import Function.Base using (_$_; _∘_; id; case_of_; flip)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import correctness.lemmas.LinRepDense-is-comm-monoid
open import correctness.lemmas.dsem-lemmas
open apply-cong[,]

open import spec
open import correctness.spec
open import correctness.lemmas.value-compatibility-lemmas using (≃τ-and-≃Γ-implies-Compatible-idx-LEtup)
open import correctness.dsem
open import correctness.dsyn-defined
import spec.LACM as LACM

DSemᵀ-lemma-interp-let : {Γ : Env Pr} {σ τ : Typ Pr}
  → (a : Rep (Etup Pr Γ))
  → (ctg : LinRepDense (D2τ' τ))
  → (rhs : Term Pr Γ σ)
  → (body : Term Pr (σ ∷ Γ) τ)
  → (d-let : Is-just $ DSemᵀ {σ = Etup Pr Γ} {τ = τ} (interp (let' rhs body) ∘ Etup-to-val) a )
  → (d-rhs : Is-just $ DSemᵀ {σ = Etup Pr Γ } {τ = σ} (interp rhs ∘ Etup-to-val) a )
  → (d-body : Is-just $ DSemᵀ {σ = σ :* (Etup Pr Γ)} {τ = τ} (interp body ∘ Etup-to-val) (interp rhs (Etup-to-val a) , a) )
  → let ctg-body = to-witness d-body ctg
    in (Etup2EV (to-witness d-rhs (ctg-body .fst)) ev+ Etup2EV (ctg-body .snd))
       ≡ Etup2EV (to-witness d-let ctg)
DSemᵀ-lemma-interp-let {Γ} {σ} {τ} a ctg rhs body d-let d-rhs d-body =
  let ctg-body = to-witness d-body ctg
      g : (env : Rep (Etup Pr Γ)) → Rep σ × Rep (Etup Pr Γ) -- Note that g constructs a pair, thus we can use the pair rule on it
      g = (λ env → (interp rhs (Etup-to-val env) , env))
      dg : Is-just (DSemᵀ {Etup Pr Γ } {σ :* (Etup Pr Γ)} g a)
      dg = DSemᵀ-exists-lemma-pair₂ (interp rhs ∘ Etup-to-val) id a (d-rhs , DSemᵀ-exists-lemma-identity a)
      (d-id , eq1) = DSemᵀ-identity a (snd ctg-body)
  in begin
  Etup2EV (to-witness d-rhs (fst ctg-body)) ev+ Etup2EV (snd ctg-body)
    ≡⟨ ev+congR (cong Etup2EV (sym eq1)) ⟩
  Etup2EV (to-witness d-rhs (fst ctg-body)) ev+ Etup2EV (to-witness d-id (snd ctg-body))
    ≡⟨ DSemᵀ-ev-lemma-pair (interp rhs ∘ Etup-to-val) id a (fst ctg-body) (snd ctg-body) d-rhs d-id dg ⟩
  Etup2EV (to-witness dg ctg-body)
    ≡⟨ cong Etup2EV (sym (DSemᵀ-lemma-chain _ g a d-body dg d-let ctg)) ⟩
  Etup2EV (to-witness d-let ctg)
  ∎
  
module Interp-case {Γ : Env Pr} {σ τ ρ : Typ Pr}
  (a : Rep (Etup Pr Γ))
  (e : Term Pr Γ (σ :+ τ))
  (l : Term Pr (σ ∷ Γ) ρ)
  (r : Term Pr (τ ∷ Γ) ρ)
  (de : Is-just $ DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a)
  (dsyn : DSyn-Exists (Etup-to-val a) (case' e l r))
  (ctg : LinRepDense (D2τ' ρ))
  where
  private
    -- This lemma works by splitting up the case into 2 'nice' functions f and g using the chain rule and extensionality.
    -- f makes a choice depending on inj₁ or inj₂, g merely sets up the correct input.

    -- ===================
    -- Useful names
    -- ===================
    f : (Rep $ (σ :+ τ) :* Etup Pr Γ) → Rep ρ
    f = λ (cond , a') → [ (λ v → interp l $ Etup-to-val (v , a'))
                        , (λ v → interp r $ Etup-to-val (v , a'))
                        ] cond

    g : (a' : Rep (Etup Pr Γ)) → Σ (Rep σ ⊎ Rep τ) (λ v → Rep (Etup Pr Γ))
    g = λ a' → interp e (Etup-to-val a') , a'

    d-case : Is-just $ DSemᵀ {Etup Pr Γ} {ρ} (interp (case' e l r) ∘ Etup-to-val) a
    d-case = DSyn-Exists→DSem-Exists a (case' e l r) dsyn

    dg : Is-just (DSemᵀ {Etup Pr Γ} {(σ :+ τ) :* Etup Pr Γ} g a)
    dg = DSemᵀ-exists-lemma-pair₂ (interp e ∘ Etup-to-val) id a (de , DSemᵀ-exists-lemma-identity a)

    case-simp-ext : interp (case' e l r) ∘ Etup-to-val ≗ (f ∘ g)
    case-simp-ext a' with (interp e (Etup-to-val a'))
    ... | inj₁ _ = refl
    ... | inj₂ _ = refl

    d-case-simp : Is-just (DSemᵀ {Etup Pr Γ} {ρ} (f ∘ g) a)
    d-case-simp = DSemᵀ-exists-extensionality (interp (case' e l r) ∘ Etup-to-val) (f ∘ g) case-simp-ext a d-case 

    -- ===================
    -- Simplify (similair to a let-binding)
    -- ===================
    DSemᵀ-lemma-interp-case-simplify : (df : Is-just (DSemᵀ {(σ :+ τ) :* Etup Pr Γ} {ρ} f (g a))) →
                                        Etup2EV (to-witness d-case ctg) 
                                      ≡ (Etup2EV (to-witness de (to-witness df ctg . fst)) ev+ Etup2EV (to-witness df ctg .snd)) 
    DSemᵀ-lemma-interp-case-simplify df =
      let ctg-f = to-witness df ctg
          (d-id , eq) = DSemᵀ-identity a (to-witness df ctg .snd)
      in begin
      Etup2EV (to-witness d-case ctg)
        ≡⟨ cong Etup2EV (DSemᵀ-extensionality _ _ case-simp-ext a d-case d-case-simp ctg) ⟩
      Etup2EV (to-witness d-case-simp ctg)
        ≡⟨ cong Etup2EV (DSemᵀ-lemma-chain f g a df dg d-case-simp ctg) ⟩
      Etup2EV (to-witness dg (to-witness df ctg))
        ≡⟨ sym (DSemᵀ-ev-lemma-pair (interp e ∘ Etup-to-val) id a (ctg-f .fst) (ctg-f .snd) de d-id dg) ⟩
      Etup2EV (to-witness de (ctg-f . fst)) ev+ Etup2EV (to-witness d-id (ctg-f .snd))
        ≡⟨ ev+congR (cong Etup2EV eq) ⟩
      Etup2EV (to-witness de (to-witness df ctg .fst)) ev+ Etup2EV (to-witness df ctg .snd)
      ∎

    -- ===================
    -- Apply the inj₁ and inj₂ dsem-lemmas
    -- ===================
    DSemᵀ-lemma-interp-case-left : (df : Is-just (DSemᵀ {(σ :+ τ) :* Etup Pr Γ} {ρ} f (g a))) →
              (x : Rep σ) → (interp-e-val≡inj-x : interp e (Etup-to-val a) ≡ inj₁ x)
             → (dl : Is-just $ DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a))
             → (Etup2EV (to-witness de (to-witness df ctg . fst)) ev+ Etup2EV (to-witness df ctg .snd)) 
               ≡ (Etup2EV (to-witness de (to-witness dl ctg .fst , zerovDense (D2τ' τ))) ev+ Etup2EV (to-witness dl ctg .snd))
    DSemᵀ-lemma-interp-case-left df x interp-e-val≡inj-x dl 
      rewrite DSemᵀ-lemma-case-inj₁ (g a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) df ctg x interp-e-val≡inj-x dl 
      = refl

    DSemᵀ-lemma-interp-case-right : (df : Is-just (DSemᵀ {(σ :+ τ) :* Etup Pr Γ} {ρ} f (g a))) →
              (x : Rep τ) → (interp-e-val≡inj-x : interp e (Etup-to-val a) ≡ inj₂ x)
             → (dr : Is-just $ DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a))
             → (Etup2EV (to-witness de (to-witness df ctg . fst)) ev+ Etup2EV (to-witness df ctg .snd)) 
               ≡ (Etup2EV (to-witness de (zerovDense (D2τ' σ) , to-witness dr ctg .fst )) ev+ Etup2EV (to-witness dr ctg .snd))
    DSemᵀ-lemma-interp-case-right df x interp-e-val≡inj-x dr
      rewrite DSemᵀ-lemma-case-inj₂ (g a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) df ctg x interp-e-val≡inj-x dr
      = refl

    -- ===================
    -- A proof that f is differentiable, which depends on a
    -- ===================
    mk-df-inj₁ : (x : Rep σ) → interp e (Etup-to-val a) ≡ inj₁ x 
                → Is-just (DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a)) → Is-just (DSemᵀ {(σ :+ τ) :* Etup Pr Γ} {ρ} f (g a))
    mk-df-inj₁ x w dl
      = let rule = DSemᵀ-exists-lemma-case-inj₁ (g a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) x w
      in Equivalence.from rule dl

    mk-df-inj₂ : (x : Rep τ) → interp e (Etup-to-val a) ≡ inj₂ x 
                → Is-just (DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a)) → Is-just (DSemᵀ {(σ :+ τ) :* Etup Pr Γ} {ρ} f (g a))
    mk-df-inj₂ x w dr
      = let rule = DSemᵀ-exists-lemma-case-inj₂ (g a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) x w
      in Equivalence.from rule dr
    
  -- ===================
  -- The main lemma
  -- ===================
  DSemᵀ-lemma-interp-case : 
      [ (λ x  → (dl : Is-just $ DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a))
              → let ctg-l = to-witness dl ctg
              in Etup2EV (to-witness de ( ctg-l .fst , zerovDense (D2τ' τ))) ev+ Etup2EV (ctg-l .snd)
                ≡ Etup2EV (to-witness d-case ctg))
      , (λ x  → (dr : Is-just $ DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a))
              → let ctg-r = to-witness dr ctg
              in Etup2EV (to-witness de (zerovDense (D2τ' σ) , ctg-r .fst)) ev+ Etup2EV (ctg-r .snd)
                ≡ Etup2EV (to-witness d-case ctg))
      ] (interp e (Etup-to-val a))
  DSemᵀ-lemma-interp-case 
    with interp e (Etup-to-val a) in interp-e-val≡inj-x  
  ... | (inj₁ x) = λ dl → let df = mk-df-inj₁ x interp-e-val≡inj-x dl
                          in sym (trans (DSemᵀ-lemma-interp-case-simplify df) (DSemᵀ-lemma-interp-case-left  df x interp-e-val≡inj-x dl))
  ... | (inj₂ x) = λ dr → let df = mk-df-inj₂ x interp-e-val≡inj-x dr
                          in sym (trans (DSemᵀ-lemma-interp-case-simplify df) (DSemᵀ-lemma-interp-case-right df x interp-e-val≡inj-x dr))

  -- ===================
  -- The main lemma + applying congruence on the condition
  -- ===================
  DSemᵀ-lemma-cong-interp-case : (c : Rep (σ :+ τ)) → (w : interp e (Etup-to-val a) ≡ c) →
      [ (λ x  → (dl : Is-just $ DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a))
              → let ctg-l = to-witness dl ctg
              in Etup2EV (to-witness de ( ctg-l .fst , zerovDense (D2τ' τ))) ev+ Etup2EV (ctg-l .snd)
                ≡ Etup2EV (to-witness d-case ctg))
      , (λ x  → (dr : Is-just $ DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a))
              → let ctg-r = to-witness dr ctg
              in Etup2EV (to-witness de (zerovDense (D2τ' σ) , ctg-r .fst)) ev+ Etup2EV (ctg-r .snd)
                ≡ Etup2EV (to-witness d-case ctg))
      ] c
  DSemᵀ-lemma-cong-interp-case c refl = DSemᵀ-lemma-interp-case
open Interp-case public