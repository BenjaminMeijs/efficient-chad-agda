module correctness.HO-chad-correct where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)

open import Data.Empty using (⊥)
open import Data.List using (_∷_; map; [])
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_]; isInj₁; isInj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Function.Base using (id; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)

open import spec
open import correctness.spec
open import correctness.dsyn-defined
open import correctness.chad-ctg-zero
open import correctness.lemmas
open import correctness.dsem


-- Nested composition
P7∘ : { τ1 τ2 τ3 : Typ Pr } → { isRd : Is-ℝᵈ (τ1 :* τ2)  }
    → (f' : Rep τ2 → ( Rep (D1τ τ3) × (LinRep (D2τ' τ3) → LinRepDense (D2τ' τ2))))
    → (g' : Rep τ1 → ( Rep (D1τ τ2) × (LinRep (D2τ' τ2) → LinRepDense (D2τ' τ1))))
    → (Rep τ1 → ( Rep (D1τ τ3) × (LinRep (D2τ' τ3) → LinRepDense (D2τ' τ1))))
P7∘ {τ1} {τ2} {τ3} {isRd} f' g' 
  = λ x → let a = f' (unprimal (snd isRd) (g' x .fst))
          in (fst a) , (λ ctg → let b = (undense (snd isRd) (snd a ctg)) 
                                in g' x .snd b)

P7-chain-rule : { τ1 τ2 τ3 : Typ Pr } → { isRd : Is-ℝᵈ (τ1 :* τ2) }
    → (f : Rep τ2 → Rep τ3)
    → (g : Rep τ1 → Rep τ2)
    → (f' : Rep τ2 → ( Rep (D1τ τ3) × (LinRep (D2τ' τ3) → LinRepDense (D2τ' τ2))))
    → (g' : Rep τ1 → ( Rep (D1τ τ2) × (LinRep (D2τ' τ2) → LinRepDense (D2τ' τ1))))
    → P7 τ2 (snd isRd) τ3 f f'
    → P7 τ1 (fst isRd) τ2 g g'
    → P7 τ1 (fst isRd) τ3 (f ∘ g) (P7∘ {isRd = isRd} f' g')
P7-chain-rule {τ1} {τ2} {Un} {isRd} f g f' g' pf pg
  = (λ _ → refl) , (λ x → refl , λ ctg → {!   !})
P7-chain-rule {τ1} {τ2} {Inte} {isRd} f g f' g' pf pg
  = (λ x → pf .fst (g x)) , (λ x → {!   !} , (λ ctg → {!   !}))
P7-chain-rule {τ1} {τ2} {R} {isRd} f g f' g' pf pg
  = {!   !}
P7-chain-rule {τ1} {τ2} {τ3 :* τ4} {isRd} f g f' g' pf pg
  = {!   !}
P7-chain-rule {τ1} {τ2} {τ3 :+ τ4} {isRd} f g f' g' pf pg = {!   !}
P7-chain-rule {τ1} {τ2} {τ3 :-> τ4} {isRd} f g f' g' pf pg
  = {!   !}

P7equivImpliesInP7 : ( σ τ : Typ Pr ) ( isRd : Is-ℝᵈ (σ :* τ) )
    → (f : Rep σ → Rep τ)
    → (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (g : Rep σ → Rep τ)
    → (g' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (P7≡ σ (fst isRd) τ f f' g g')
    → P7 σ (fst isRd) τ f f'
    → P7 σ (fst isRd) τ g g'
P7equivImpliesInP7 = ?

interp-chad : {Γ : Env Pr} {τ : Typ Pr} 
                  (t : Term Pr Γ τ)
                  (a : Val Pr Γ)
                  (evIn : LEtup (map D2τ' Γ) ) -- incoming LEtup
                → (ctg : LinRep (D2τ' τ))
                → (Rep (D1τ τ) × LEtup (map D2τ' Γ) )
interp-chad t a evIn ctg = let (x , y) = interp (chad t) (primalVal a)
                        in x , LACMexec (y ctg .fst) evIn 