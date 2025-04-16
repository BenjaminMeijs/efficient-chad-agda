module HO-correctness.lemmas where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)

-- open import Data.Empty using (⊥)
-- open import Data.List using (_∷_; map; [])
-- open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_]; isInj₁; isInj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Function.Base using (id; _$_; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)

open import spec
open import correctness.spec
open import HO-correctness.logical-relation


lemma-primal₁ : { τ : Typ Pr } → ( isRd : Is-ℝᵈ τ ) 
  → (x : Rep τ)
  → un-primal isRd (to-primal isRd x) ≡ x
lemma-primal₁ {Un} isRd x = refl
lemma-primal₁ {R} isRd x = refl
lemma-primal₁ {τ1 :* τ2} isRd x = cong₂ _,_ (lemma-primal₁ (isRd .fst) (x .fst))
                                            (lemma-primal₁ (isRd .snd) (x .snd))

lemma-primal₂ : { τ : Typ Pr } → ( isRd : Is-ℝᵈ τ ) 
  → (x : Rep (D1τ τ))
  → to-primal isRd (un-primal isRd x) ≡ x
lemma-primal₂ {Un} isRd x = refl
lemma-primal₂ {R} isRd x = refl
lemma-primal₂ {τ :* τ₁} isRd x = cong₂ _,_ (lemma-primal₂ (isRd .fst) (x .fst))
                                           (lemma-primal₂ (isRd .snd) (x .snd))


dense2sparse : {τ : Typ Pr} → (Is-ℝᵈ τ) → LinRepDense (D2τ' τ) → LinRep (D2τ' τ)
dense2sparse {Un} isRd x = tt
dense2sparse {R} isRd x = x
dense2sparse {τ1 :* τ2} isRd x = just (dense2sparse (isRd .fst) (x .fst) 
                                     , dense2sparse (isRd .snd) (x .snd))

lemma-dense : {τ : Typ Pr} → (isRd : Is-ℝᵈ τ) 
    → (x : LinRepDense (D2τ' τ))
    → sparse2dense (dense2sparse isRd x) ≡ x
lemma-dense {Un} isRd x = refl
lemma-dense {R} isRd x = refl
lemma-dense {τ1 :* τ2} isRd x = cong₂ _,_ (lemma-dense (isRd .fst) (x .fst))
                                          (lemma-dense (isRd .snd) (x .snd))


