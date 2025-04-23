module HO-correctness.fundamental-lemma where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)

open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Data.List using (map; _∷_; [])
open import Function.Base using (id; _$_; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)

open import spec
open import correctness.spec
open import correctness.dsem
open import correctness.lemmas
open import HO-correctness.logical-relation
open import HO-correctness.lemmas
open import HO-correctness.projection
open import HO-correctness.basics-in-relation


zero-LEtup : ( Γ : Env Pr ) → LEtup (map D2τ' Γ)
zero-LEtup [] = tt
zero-LEtup (τ ∷ Γ) = (zerov (D2τ' τ) .fst) , (zero-LEtup Γ)

FL-In : { Γ : Env Pr } → 
    let σ = Etup Pr Γ
    in (isRd : Is-ℝᵈ σ)
    → Set
FL-In {[]} isRd = ⊤
FL-In {τ ∷ Γ} isRd = 
    (Σ ((Rep (Etup Pr Γ) → Rep τ) × 
        (Rep (D1τ (Etup Pr Γ)) → Rep (D1τ τ) 
                                × (LinRep (D2τ' τ) → LinRepDense (D2τ' (Etup Pr Γ))))) 
    (λ (f , f') → P7 (Etup Pr Γ) (snd isRd) τ f f'))
    × FL-In (snd isRd)

FL-In-to-Val : ( Γ : Env Pr ) → (isRd : Is-ℝᵈ (Etup Pr Γ))
    → FL-In isRd
    → Rep (Etup Pr Γ)
    → Val Pr Γ
-- FL-In-to-Val = {!   !}
FL-In-to-Val [] isRd w x = empty
FL-In-to-Val (τ ∷ Γ) (isRdτ , isRdΓ) (((f , f') , p) , w) (x , xs) = 
    push (f xs) (FL-In-to-Val Γ isRdΓ w xs)

FL-Out : {!   !}
FL-Out = {!   !}

FL-f : {Γ : Env Pr}
    { τ : Typ Pr } ( isRd : Is-ℝᵈ (Etup Pr Γ) )
    → FL-In isRd
    → Term Pr Γ τ
    → Rep (Etup Pr Γ) → Rep τ
FL-f {Γ} {τ} isRd w t x = interp t (FL-In-to-Val Γ isRd w x)

FL-f' : {!   !}
FL-f' = {!   !}

fundamental-lemma : {Γ : Env Pr} {τ : Typ Pr}
    → let σ = Etup Pr Γ
          LΓ = map D2τ' Γ
      in (isRd : Is-ℝᵈ σ)
    → (a : FL-In isRd)
    → (t : Term Pr Γ τ)
    → P7 σ isRd τ (FL-f isRd a t) {!   !}
    -- → P7 σ isRd τ (interp t ∘ Etup-to-val) (P7-chad isRd t (zero-LEtup Γ))
fundamental-lemma isRd a t = {!   !}

P7-chad : {Γ : Env Pr} {τ : Typ Pr}
    → let σ = Etup Pr Γ 
          LΓ = map D2τ' Γ
    in (isRd : Is-ℝᵈ σ)
    → (f : Term Pr Γ τ)
    → (evIn : LEtup LΓ)
    → Rep (D1τ σ) → Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))
P7-chad {Γ = Γ} isRd f evIn x = 
    let val = Etup-to-val-primal (un-primal isRd x) 
        (a , b) = interp (chad f) val
    in a , (λ ctg → EV-to-Etup (LEtup2EV {map D2τ' Γ} (LACMexec (b ctg .fst) evIn)))

chad-in-P7 : {Γ : Env Pr} {τ : Typ Pr}
    → let σ = Etup Pr Γ
          LΓ = map D2τ' Γ
      in (isRd : Is-ℝᵈ σ)
    → (t : Term Pr Γ τ)
    → P7 σ isRd τ (interp t ∘ Etup-to-val) (P7-chad isRd t (zero-LEtup Γ))
chad-in-P7 isRd t = {!   !}
