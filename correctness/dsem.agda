module correctness.dsem where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (_∷_)
open import Function.Base using (id; _∘_; flip)
open import Data.Product.Base using (uncurry)
open import Agda.Builtin.Float using (primFloatPlus; primFloatTimes; primFloatNegate)

open import spec using (Typ; Pr; Env; Rep; D2τ' ; _:*_; _:+_; R; valprj)
open import spec.linear-types using (Idx; S; Z)

open import correctness.spec using (LinRepDense; zerovDense; plusvDense; Etup; Etup-to-val)

onehot : {Γ : Env Pr} {τ : Typ Pr}
        → (idx : Idx Γ τ)
        → (x : LinRepDense (D2τ' τ))
        → LinRepDense (D2τ' (Etup Pr Γ))
onehot {ρ ∷ Γ} {τ} Z       x = x , zerovDense _
onehot {ρ ∷ Γ} {τ} (S idx) x = zerovDense _ , onehot idx x

postulate
    -- ======================
    -- Definition
    -- ======================
    DSemᵀ :  {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep σ) 
            → (ctg : LinRepDense (D2τ' τ))
            → LinRepDense (D2τ' σ)

    -- ======================
    -- Misc. rules
    -- ======================
    DSemᵀ-ctg-zero : {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep σ)
            → DSemᵀ {σ} {τ} f a (zerovDense (D2τ' τ)) ≡ zerovDense (D2τ' σ)

    DSemᵀ-chain : {τ1 τ2 τ3 : Typ Pr}
                → (f : Rep τ2 → Rep τ3)
                → (g : Rep τ1 → Rep τ2)
                → (a : Rep τ1)
                → DSemᵀ {τ1} {τ3} (f ∘ g) a
                  ≡ DSemᵀ {τ1} {τ2} g a ∘ DSemᵀ {τ2} {τ3} f (g a)

    DSemᵀ-pair : {σ τ1 τ2 : Typ Pr}
            → (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → (a : Rep σ)
            → (ctg-f : LinRepDense (D2τ' τ1))
            → (ctg-g : LinRepDense (D2τ' τ2))
            → let dsem-f = DSemᵀ {σ} {τ1} f a ctg-f
                  dsem-g = DSemᵀ {σ} {τ2} g a ctg-g
                  h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
                  ctg : LinRepDense (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
              in DSemᵀ {σ} {τ1 :* τ2} h a ctg
                 ≡ plusvDense (D2τ' σ) dsem-f dsem-g

    DSemᵀ-var : {Γ : Env Pr} {τ : Typ Pr}
              → let σ = Etup Pr Γ
              in (a : Rep σ)
              → (idx : Idx Γ τ)
              → (ctg : LinRepDense (D2τ' τ))
              → DSemᵀ {σ} {τ} (flip valprj idx ∘ Etup-to-val) a ctg
                ≡ onehot idx ctg

    -- ======================
    -- DSem on linear functions (Derivative of a linear function f is f)
    -- ======================
    DSemᵀ-identity : {τ : Typ Pr} 
            → (a : Rep τ)
            → DSemᵀ {τ} {τ} id a
              ≡ id

    DSemᵀ-inj₁ : {σ τ : Typ Pr}
            → (a : Rep σ)
            → DSemᵀ {σ} {σ :+ τ} inj₁ a
              ≡ fst

    DSemᵀ-inj₂ : {σ τ : Typ Pr}
            → (a : Rep σ)
            → DSemᵀ {σ} {τ :+ σ} inj₂ a
              ≡ snd

    -- ======================
    -- (primitive) Operations on Floats
    -- ======================
    DSemᵀ-prim-floatPlus : let  σ : Typ Pr ; σ = (R :* R) ; τ : Typ Pr ; τ = R 
            in (a : Rep σ)
            → (ctg : LinRepDense (D2τ' τ))
            → let (x , y) = a
              in DSemᵀ {σ} {τ} (uncurry primFloatPlus) (x , y) ctg
              ≡ (ctg , ctg)

    DSemᵀ-prim-floatTimes : let  σ : Typ Pr ; σ = (R :* R) ; τ : Typ Pr ; τ = R 
            in (a : Rep σ)
            → (ctg : LinRepDense (D2τ' τ))
            → let (x , y) = a
              in DSemᵀ {σ} {τ} (uncurry primFloatTimes) (x , y) ctg
              ≡ (primFloatTimes ctg y , primFloatTimes ctg x)

    DSemᵀ-prim-floatNegate : let  σ : Typ Pr ; σ = R ; τ : Typ Pr ; τ = R 
            in (a : Rep σ) 
            → (ctg : LinRepDense (D2τ' τ))
            → DSemᵀ {σ} {τ} primFloatNegate a ctg
              ≡ primFloatNegate ctg