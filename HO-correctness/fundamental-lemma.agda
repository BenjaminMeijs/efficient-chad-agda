{-# OPTIONS --allow-unsolved-metas #-}
module HO-correctness.fundamental-lemma where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)

open import Data.List using (List; map; _∷_; [])
open import Function.Base using (_$_; const; _∘_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)

open import spec hiding (LR)
open import spec.LACM as LACM
open import spec.HL
open import HO-correctness.dense-rep
open import HO-correctness.dsem
open import HO-correctness.logical-relation
open import HO-correctness.lemmas.trivial-equivalences


private
    trans₂ : {A : Set} {x y a b : A} → x ≡ y → x ≡ a → y ≡ b → a ≡ b
    trans₂ refl refl refl = refl


Etup-≡-HL : ∀ {tag} → (Γ : Env tag) → Rep (Etup tag Γ) ≡ HL Γ Rep
Etup-≡-HL [] = refl
Etup-≡-HL (x ∷ Γ) = cong₂ _×_ refl (Etup-≡-HL Γ)
Etup-to-HL : ∀ {tag} → { Γ : Env tag } → Rep (Etup tag Γ) → HL Γ Rep
Etup-to-HL {_} {Γ} = sub (Etup-≡-HL Γ)
HL-to-Etup : ∀ {tag} → { Γ : Env tag } → HL Γ Rep → Rep (Etup tag Γ)
HL-to-Etup {_} {Γ} = sub (sym $ Etup-≡-HL Γ)

LETs-≡-HL : ( Γ : Env Pr ) → LETs (map D2τ' Γ) ≡ HL (map D2τ' Γ) LinRep
LETs-≡-HL [] = refl
LETs-≡-HL (x ∷ Γ) = cong₂ _×_ refl (LETs-≡-HL Γ)
LETs-to-HL : { Γ : Env Pr } → LETs (map D2τ' Γ) → HL (map D2τ' Γ) LinRep
LETs-to-HL {Γ} x = sub (LETs-≡-HL Γ) x
HL-to-LETs : { Γ : Env Pr } → HL (map D2τ' Γ) LinRep → LETs (map D2τ' Γ) 
HL-to-LETs {Γ} x = sub (sym $ LETs-≡-HL Γ) x


precond : {σ : Typ Pr}
    → (q : Is-ℝᵈ σ)
    → Typ Pr → Set
precond {σ} q τ =
    (Σ ((Rep σ → Rep τ) × 
        (Rep (D1τ σ) → Rep (D1τ τ) 
                                × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ)))) 
        (λ (f , f') → LR σ q τ f f'))

zero-LETs : (Γ : Env Pr) → LETs (map D2τ' Γ)
zero-LETs [] = tt
zero-LETs (τ ∷ Γ) = (zerov (D2τ' τ) .fst) , (zero-LETs Γ)

FL-f-val : {Γ : Env Pr}
    → (q : Is-ℝᵈ (Etup Pr Γ))
    → HL Γ (precond q) → Rep (Etup Pr Γ)
    → Val Pr Γ
FL-f-val {Γ} q l x = 
    let f _ y = y .fst .fst x
    in Etup-to-val (HL-to-Etup (HL-map f l))

FL-f : {Γ : Env Pr}
    { τ : Typ Pr } ( isRd : Is-ℝᵈ (Etup Pr Γ) )
    → HL Γ (precond isRd)
    → Term Pr Γ τ
    → Rep (Etup Pr Γ) → Rep τ
FL-f isRd w t x = interp t (FL-f-val isRd w x)

propagator : ( σ τ : Typ Pr ) → Set 
propagator σ τ = LinRep (D2τ' τ) → LinRepDense (D2τ' σ)

getCtgPropagators : {Γ : Env Pr}
    → (q : Is-ℝᵈ (Etup Pr Γ))
    → HL Γ (precond q) → Rep (D1τ (Etup Pr Γ))
    → HL Γ (propagator (Etup Pr Γ))
getCtgPropagators {Γ} q p x = 
    let f τ y = y .fst .snd x .snd
    in HL-map f p

sumCtgPropagators : {Γ : Env Pr}
    → (q : Is-ℝᵈ (Etup Pr Γ))
    → HL Γ (propagator (Etup Pr Γ)) → LETs (map D2τ' Γ)
    → LinRepDense (D2τ' (Etup Pr Γ))
sumCtgPropagators {Γ} q l1 w = 
    let l2 = sub (sym HL-chain) (LETs-to-HL w)
        applied = HL-zipWith (λ _ x y → x y) l1 l2
        plus _ x y = plusvDense (D2τ' (Etup Pr Γ)) x y 
        zero = zerovDense (D2τ' (Etup Pr Γ)) 
        sum = HL-foldr plus zero applied
    in sum

lemma-D1Γ≡ : {Γ : Env Pr} → (q : Is-ℝᵈ (Etup Pr Γ)) 
    → HL Γ (Rep ∘ D1τ) ≡ HL (D1Γ Γ) Rep
lemma-D1Γ≡ {[]} q = refl
lemma-D1Γ≡ {x ∷ Γ} q = cong₂ _×_ refl (lemma-D1Γ≡ (q .snd))

lemma-D1Γ₁ : {Γ : Env Pr} → (q : Is-ℝᵈ (Etup Pr Γ)) 
    → HL Γ (Rep ∘ D1τ) → HL (D1Γ Γ) Rep
lemma-D1Γ₁ q x = sub (lemma-D1Γ≡ q) x

lemma-D1Γ₂ : {Γ : Env Pr} → (q : Is-ℝᵈ (Etup Pr Γ)) 
    → HL (D1Γ Γ) Rep → HL Γ (Rep ∘ D1τ) 
lemma-D1Γ₂ q x = sub (sym $ lemma-D1Γ≡ q) x

FL-f'-val : {Γ : Env Pr}
    → (q : Is-ℝᵈ (Etup Pr Γ))
    → HL Γ (precond q) → Rep (D1τ (Etup Pr Γ))
    → Val Du (D1Γ Γ)
FL-f'-val {Γ} q p x = 
    let f a y = (y .fst .snd x .fst)
        env = HL-map f p
    -- Note that this is just a bijeciton between two equivalent sets
    -- TODO use HL-chain
    in Etup-to-val (HL-to-Etup (lemma-D1Γ₁ q env))


FL-f' : {Γ : Env Pr} {τ : Typ Pr}
    → (isRd : Is-ℝᵈ (Etup Pr Γ))
    → (HL Γ (precond isRd))
    → (Term Pr Γ τ)
    → (Rep (D1τ (Etup Pr Γ))
    → Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' (Etup Pr Γ))))
FL-f' {Γ} {τ} isRd w t x =
    let propagators = getCtgPropagators {Γ} isRd w x
        (g , g') = interp (chad t) (FL-f'-val isRd w x)
    in g , λ ctg → let w = (LACM.exec (g' ctg .fst) (zero-LETs Γ))
                   in sumCtgPropagators isRd propagators w

fundamental-lemma : ( Γ : Env Pr ) ( τ : Typ Pr )
    → let σ = Etup Pr Γ
          LΓ = map D2τ' Γ
      in (isRd : Is-ℝᵈ σ)
    → (p : HL Γ (precond isRd)) 
    → (t : Term Pr Γ τ)
    → LR σ isRd τ (FL-f isRd p t) (FL-f' isRd p t)
fundamental-lemma Γ τ isRd a t = {!   !}
 