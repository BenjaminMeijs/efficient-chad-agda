{-# OPTIONS --allow-unsolved-metas #-}
module correctness.lemmas.dsem-ev-lemmas where

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

open import spec
open import correctness.spec
open import correctness.lemmas.value-compatibility-lemmas using (≃τ-and-≃Γ-implies-Compatible-idx-LEtup)
open import correctness.dsem
import spec.LACM as LACM

private
    trans₂ : {A : Set} {x y a b : A} → x ≡ y → x ≡ a → y ≡ b → a ≡ b
    trans₂ refl refl refl = refl

module Onehot where
    private
        onehot-equiv-addLEτ : {Γ : Env Pr} {τ : Typ Pr}
            → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
            in (ctg : LinRep (D2τ' τ))
            → (evIn : LEtup (map D2τ' Γ) )
            → Compatible-idx-LEtup (idx , ctg) evIn
            → LEtup2EV (addLEτ idx' ctg evIn)
              ≡ (Etup2EV (onehot idx (sparse2dense ctg)) ev+ LEtup2EV evIn)
        onehot-equiv-addLEτ {τ ∷ Γ}  Z      ctg (x , xs) w = cong₂ _,_ (plusv-equiv-plusvDense ctg x w) (sym (ev+zeroL' Etup-zerovDense-equiv-zero-EV))
        onehot-equiv-addLEτ {τ ∷ Γ} (S idx) ctg (x , xs) w = cong₂ _,_ (sym plusvDense-zeroL') (onehot-equiv-addLEτ idx ctg xs w)

    onehot-equiv-addLEτ-lemma : {Γ : Env Pr} {τ : Typ Pr}
        → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
        in (ctg : LinRep (D2τ' τ))
        → (evIn : LEtup (map D2τ' Γ) )
        → (val : Val Pr Γ) → (ctg ≃τ valprj val idx) → (evIn ≃Γ val)
        → LEtup2EV (addLEτ idx' ctg evIn)
          ≡ (Etup2EV (onehot idx (sparse2dense ctg)) ev+ LEtup2EV evIn)
    onehot-equiv-addLEτ-lemma idx ctg evIn val ~τ ~Γ = onehot-equiv-addLEτ idx ctg evIn (≃τ-and-≃Γ-implies-Compatible-idx-LEtup idx ctg evIn val ~τ ~Γ)

module Ev-zero {Γ : Env Pr} {τ : Typ Pr} { f : Rep (Etup Pr Γ)  →  Rep τ } { a : Rep (Etup Pr Γ) }
    { ctg : LinRepDense (D2τ' τ) }
    {{ w : ctg ≡ zerovDense (D2τ' τ)}}
    ( df : Is-just (DSemᵀ {Etup Pr Γ} {τ} f a) )
    where

    DSemᵀ-ev-lemma-ctg-zero' : Etup2EV (to-witness df ctg) ≡ zero-EV (map D2τ' Γ)
    DSemᵀ-ev-lemma-ctg-zero'
      = trans (cong (Etup2EV ∘ to-witness df) w) 
              (trans (cong Etup2EV (Zero.DSemᵀ-lemma-ctg-zero' df)) Etup-zerovDense-equiv-zero-EV)

    DSemᵀ-ev-lemma-ctg-zero-evIn' : { evIn : LEtup (map D2τ' Γ)  }
                    → LEtup2EV {map D2τ' Γ} evIn 
                      ≡ Etup2EV (to-witness df ctg) ev+ LEtup2EV {map D2τ' Γ} evIn
    DSemᵀ-ev-lemma-ctg-zero-evIn' {evIn} = sym (ev+zeroL' DSemᵀ-ev-lemma-ctg-zero')

module Ev-pair {Γ : Env Pr} {τ1 τ2 : Typ Pr } (f : Rep (Etup Pr Γ) →  Rep τ1) (g : Rep (Etup Pr Γ) →  Rep τ2) (a : Rep (Etup Pr Γ))
            (ctg-f : LinRepDense (D2τ' τ1)) (ctg-g : LinRepDense (D2τ' τ2))
            (df : Is-just (DSemᵀ {Etup Pr Γ} {τ1} f a))
            (dg : Is-just (DSemᵀ {Etup Pr Γ} {τ2} g a))
            (dh : Is-just (DSemᵀ {Etup Pr Γ} {τ1 :* τ2} (λ e → (f e , g e) ) a))
    where
    private
      h : Rep (Etup Pr Γ) → Rep (τ1 :* τ2)
      h e = (f e , g e)

    DSemᵀ-ev-lemma-pair : (Etup2EV (to-witness df ctg-f) ev+ Etup2EV (to-witness dg ctg-g)) 
                           ≡ Etup2EV (to-witness dh (ctg-f , ctg-g))
    DSemᵀ-ev-lemma-pair 
      = let rule = Pair.DSemᵀ-lemma-pair f g a dh df dg ctg-f ctg-g
        in sym (trans₂ (cong Etup2EV rule) refl (plusvDense-equiv-ev+ (to-witness df ctg-f) (to-witness dg ctg-g)))

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
      dg = Pair.DSemᵀ-exists-lemma-pair₂ (interp rhs ∘ Etup-to-val) id a (d-rhs , DSemᵀ-identity a (zerovDense (D2τ' (Etup Pr Γ))) .fst)
      (d-id , eq1) = DSemᵀ-identity a (snd ctg-body)
  in begin
  Etup2EV (to-witness d-rhs (fst ctg-body)) ev+ Etup2EV (snd ctg-body)
    ≡⟨ ev+congR (cong Etup2EV (sym eq1)) ⟩
  Etup2EV (to-witness d-rhs (fst ctg-body)) ev+ Etup2EV (to-witness d-id (snd ctg-body))
    ≡⟨ Ev-pair.DSemᵀ-ev-lemma-pair (interp rhs ∘ Etup-to-val) id a (fst ctg-body) (snd ctg-body) d-rhs d-id dg ⟩
  Etup2EV (to-witness dg ctg-body)
    ≡⟨ cong Etup2EV (sym (DSemᵀ-lemma-chain _ g a d-let d-body dg ctg)) ⟩
  Etup2EV (to-witness d-let ctg)
  ∎
  
module Ev-case {Γ : Env Pr} {σ τ ρ : Typ Pr}
  (a : Rep (Etup Pr Γ))
  (e : Term Pr Γ (σ :+ τ))
  (l : Term Pr (σ ∷ Γ) ρ)
  (r : Term Pr (τ ∷ Γ) ρ)
  (de : Is-just $ DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a)
  (d-case : Is-just $ DSemᵀ {Etup Pr Γ} {ρ} (interp (case' e l r) ∘ Etup-to-val) a)
  (ctg : LinRepDense (D2τ' ρ))
  where

  private
    -- TODO: add overview comment explaining how this proof works

    f : (Rep $ (σ :+ τ) :* Etup Pr Γ) → Rep ρ
    f = λ (cond , a') → [ (λ v → interp l $ Etup-to-val (v , a'))
                        , (λ v → interp r $ Etup-to-val (v , a'))
                        ] cond
    g : (a' : Rep (Etup Pr Γ)) → Σ (Rep σ ⊎ Rep τ) (λ v → Rep (Etup Pr Γ))
    g = λ a' → interp e (Etup-to-val a') , a'

    df : Is-just (DSemᵀ {(σ :+ τ) :* Etup Pr Γ} {ρ} f (g a))
    df = {!   !}

    dg : Is-just (DSemᵀ {Etup Pr Γ} {(σ :+ τ) :* Etup Pr Γ} g a)
    dg = {!   !}

    case-simp-ext : interp (case' e l r) ∘ Etup-to-val ≗ (f ∘ g)
    case-simp-ext a' with (interp e (Etup-to-val a'))
    ... | inj₁ _ = refl
    ... | inj₂ _ = refl

    d-case-simp : Is-just (DSemᵀ {Etup Pr Γ} {ρ} (f ∘ g) a)
    d-case-simp = DSemᵀ-exists-extensionality (interp (case' e l r) ∘ Etup-to-val) (f ∘ g) case-simp-ext a d-case 

    DSemᵀ-lemma-interp-case-simplify : Etup2EV (to-witness d-case ctg) 
                                      ≡ (Etup2EV (to-witness de (to-witness df ctg . fst)) ev+ Etup2EV (to-witness df ctg .snd)) 
    DSemᵀ-lemma-interp-case-simplify =
      let ctg-f = to-witness df ctg
          (d-id , eq) = DSemᵀ-identity a (to-witness df ctg .snd)
      in begin
      Etup2EV (to-witness d-case ctg)
        ≡⟨ cong Etup2EV (DSemᵀ-extensionality _ _ case-simp-ext a d-case d-case-simp ctg) ⟩
      Etup2EV (to-witness d-case-simp ctg)
        ≡⟨ cong Etup2EV (DSemᵀ-lemma-chain f g a d-case-simp df dg ctg) ⟩
      Etup2EV (to-witness dg (to-witness df ctg))
        ≡⟨ sym (Ev-pair.DSemᵀ-ev-lemma-pair (interp e ∘ Etup-to-val) id a (ctg-f .fst) (ctg-f .snd) de d-id dg) ⟩
      Etup2EV (to-witness de (ctg-f . fst)) ev+ Etup2EV (to-witness d-id (ctg-f .snd))
        ≡⟨ ev+congR (cong Etup2EV eq) ⟩
      Etup2EV (to-witness de (to-witness df ctg .fst)) ev+ Etup2EV (to-witness df ctg .snd)
      ∎

    DSemᵀ-lemma-interp-case-left : (x : Rep σ) → (interp-e-val≡inj-x : interp e (Etup-to-val a) ≡ inj₁ x)
             → (dl : Is-just $ DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a))
             → (Etup2EV (to-witness de (to-witness df ctg . fst)) ev+ Etup2EV (to-witness df ctg .snd)) 
               ≡ (Etup2EV (to-witness de (to-witness dl ctg .fst , zerovDense (D2τ' τ))) ev+ Etup2EV (to-witness dl ctg .snd))
    DSemᵀ-lemma-interp-case-left x interp-e-val≡inj-x dl 
      rewrite DSemᵀ-lemma-case-inj₁ (g a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) x interp-e-val≡inj-x df dl ctg
      = refl

    DSemᵀ-lemma-interp-case-right : (x : Rep τ) → (interp-e-val≡inj-x : interp e (Etup-to-val a) ≡ inj₂ x)
             → (dr : Is-just $ DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a))
             → (Etup2EV (to-witness de (to-witness df ctg . fst)) ev+ Etup2EV (to-witness df ctg .snd)) 
               ≡ (Etup2EV (to-witness de (zerovDense (D2τ' σ) , to-witness dr ctg .fst )) ev+ Etup2EV (to-witness dr ctg .snd))
    DSemᵀ-lemma-interp-case-right x interp-e-val≡inj-x dr
      rewrite DSemᵀ-lemma-case-inj₂ (g a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) x interp-e-val≡inj-x df dr ctg
      = refl

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
  ... | (inj₁ x) = λ dl → sym (trans DSemᵀ-lemma-interp-case-simplify $ DSemᵀ-lemma-interp-case-left  x interp-e-val≡inj-x dl)
  ... | (inj₂ x) = λ dr → sym (trans DSemᵀ-lemma-interp-case-simplify $ DSemᵀ-lemma-interp-case-right x interp-e-val≡inj-x dr)

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