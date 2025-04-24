module HO-correctness.fundamental-lemma where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)

open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Data.List using (List; map; _∷_; []; foldr; foldl; zipWith)
open import Function.Base using (id; _$_; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; subst; trans; cong; cong₂; _≗_)

open import spec
open import correctness.spec
open import correctness.dsem
open import correctness.lemmas
open import HO-correctness.logical-relation
open import HO-correctness.lemmas
open import HO-correctness.projection
open import HO-correctness.basics-in-relation


HL : {A : Set} → (L : List A) → (A → Set) → Set
HL [] f = ⊤
HL (x ∷ Γ) f = f x × HL Γ f

HL-zipWith : {A : Set} → {α β ɣ : A → Set }
    → { L : List A }
    → (f : ( a : A ) → (α a) → (β a) → (ɣ a))
    → HL L α → HL L β → HL L ɣ
HL-zipWith {L = []} f x y = tt
HL-zipWith {L = a ∷ L} f (x , xs) (y , ys) 
    = f a x y , HL-zipWith f xs ys

HL-map : {A : Set} → { α β : A → Set } → {L : List A}
    → (f : (a : A) → (α a) → (β a)) → HL L α → HL L β
HL-map {A} {α} {β} {[]} f x = tt
HL-map {A} {α} {β} {a ∷ L} f (x , xs) = f a x , HL-map f xs

lemma-zipWith-snd-[] : {A B C : Set}
    → ( f : A → B → C ) 
    → ( L : List A )
    → (zipWith f L []) ≡ []
lemma-zipWith-snd-[] f [] = refl
lemma-zipWith-snd-[] f (x ∷ L) = refl

HL-zipWithG : {A B C : Set} → {α : A → Set } 
    {β : B → Set}
    → { L1 : List A } {L2 : List B}
    → (f : A → B → C)
    → (g : C → Set)
    → (h : ( a : A ) → (b : B) → (α a) → (β b) → (g (f a b)))
    → HL L1 α → HL L2 β → HL (zipWith f L1 L2) g
HL-zipWithG {L1 = []} f g h x y = tt
HL-zipWithG {L1 = L1} {L2 = []} f g h x y
    rewrite lemma-zipWith-snd-[] f L1
    = tt
HL-zipWithG {L1 = a ∷ L1} {L2 = b ∷ L2} f g h (x , xs) (y , ys) = 
    h a b x y , (HL-zipWithG f g h xs ys)

Etup-≡-HL : ∀ {tag} → (Γ : Env tag) → Rep (Etup tag Γ) ≡ HL Γ Rep
Etup-≡-HL [] = refl
Etup-≡-HL (x ∷ Γ) = cong₂ _×_ refl (Etup-≡-HL Γ)
Etup-to-HL : ∀ {tag} → (Γ : Env tag) → Rep (Etup tag Γ) → HL Γ Rep
Etup-to-HL Γ x rewrite Etup-≡-HL Γ = x
HL-to-Etup : ∀ {tag} → (Γ : Env tag) → HL Γ Rep → Rep (Etup tag Γ)
HL-to-Etup Γ x rewrite sym (Etup-≡-HL Γ) = x

LEtup-≡-HL : ( Γ : Env Pr ) → LEtup (map D2τ' Γ) ≡ HL (map D2τ' Γ) LinRep
LEtup-≡-HL [] = refl
LEtup-≡-HL (x ∷ Γ) = cong₂ _×_ refl (LEtup-≡-HL Γ)
LEtup-to-HL : { Γ : Env Pr } → LEtup (map D2τ' Γ) → HL (map D2τ' Γ) LinRep
LEtup-to-HL {Γ} x rewrite (LEtup-≡-HL Γ) = x
HL-to-LEtup : { Γ : Env Pr } → HL (map D2τ' Γ) LinRep → LEtup (map D2τ' Γ) 
HL-to-LEtup {Γ} x rewrite sym (LEtup-≡-HL Γ) = x


precond : {σ : Typ Pr}
    → (q : Is-ℝᵈ σ)
    → Typ Pr → Set
precond {σ} q τ =
    (Σ ((Rep σ → Rep τ) × 
        (Rep (D1τ σ) → Rep (D1τ τ) 
                                × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ)))) 
        (λ (f , f') → P7 σ q τ f f'))



zero-LEtup : ( Γ : Env Pr ) → LEtup (map D2τ' Γ)
zero-LEtup [] = tt
zero-LEtup (τ ∷ Γ) = (zerov (D2τ' τ) .fst) , (zero-LEtup Γ)

FL-f-val : {Γ : Env Pr}
    → (q : Is-ℝᵈ (Etup Pr Γ))
    → HL Γ (precond q) → Rep (Etup Pr Γ)
    → Val Pr Γ
FL-f-val {Γ} q l x = 
    let f _ y = y .fst .fst x
    in Etup-to-val (HL-to-Etup Γ (HL-map f l))

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
    → HL Γ (propagator (Etup Pr Γ)) → HL Γ (LinRep ∘ D2τ')
    → HL Γ (LinRepDense ∘ D2τ')
sumCtgPropagators {Γ} q l1 l2 = 
    let applied = HL-zipWith (λ _ x y → x y) l1 l2
        sum = {!   !}
    in {!   !}

lemma-D1Γ≡ : {Γ : Env Pr} → (q : Is-ℝᵈ (Etup Pr Γ)) 
    → HL Γ (Rep ∘ D1τ) ≡ HL (D1Γ Γ) Rep
lemma-D1Γ≡ {[]} q = refl
lemma-D1Γ≡ {x ∷ Γ} q = cong₂ _×_ refl (lemma-D1Γ≡ (q .snd))

lemma-D1Γ₁ : {Γ : Env Pr} → (q : Is-ℝᵈ (Etup Pr Γ)) 
    → HL Γ (Rep ∘ D1τ) → HL (D1Γ Γ) Rep
lemma-D1Γ₁ q x rewrite lemma-D1Γ≡ q = x

lemma-D1Γ₂ : {Γ : Env Pr} → (q : Is-ℝᵈ (Etup Pr Γ)) 
    → HL (D1Γ Γ) Rep → HL Γ (Rep ∘ D1τ) 
lemma-D1Γ₂ q x rewrite sym (lemma-D1Γ≡ q) = x

FL-f'-val : {Γ : Env Pr}
    → (q : Is-ℝᵈ (Etup Pr Γ))
    → HL Γ (precond q) → Rep (D1τ (Etup Pr Γ))
    → Val Du (D1Γ Γ)
FL-f'-val {Γ} q p x = 
    let f a y = (y .fst .snd x .fst)
        env = HL-map f p
    -- Note that this is just a bijeciton between two equivalent sets
    in Etup-to-val (HL-to-Etup (D1Γ Γ) (lemma-D1Γ₁ q env))


FL-f' : {Γ : Env Pr} {τ : Typ Pr}
    → (isRd : Is-ℝᵈ (Etup Pr Γ))
    → (HL Γ (precond isRd))
    → (Term Pr Γ τ)
    → (Rep (D1τ (Etup Pr Γ))
    → Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' (Etup Pr Γ))))
FL-f' {Γ} {τ} isRd w t x =
    let -- env = Fundament-apply-f' {Γ} {Γ} isRd w x
        -- propagators = getCtgPropagators {Γ} {Γ} isRd w x
        propagators = getCtgPropagators {Γ} isRd w x
        (g , g') = interp (chad t) (FL-f'-val isRd w x)
    in g , λ ctg → let w = (LACMexec (g' ctg .fst) (zero-LEtup Γ))
                   in {!  LEtup-to-HL w  !}
        -- (g , g') = interp (chad t) (Etup-to-val (Etup-D1τ-distr₁ Γ env))
    -- in g , λ ctg → let w = LEtup2EV {map D2τ' Γ} (LACMexec (g' ctg .fst) (zero-LEtup Γ))
                --    in EV-to-Etup (sumCtgPropagators isRd isRd propagators w)

fundamental-lemma : {Γ : Env Pr} {τ : Typ Pr}
    → let σ = Etup Pr Γ
          LΓ = map D2τ' Γ
      in (isRd : Is-ℝᵈ σ)
    → (p : HL Γ (precond isRd)) 
    → (t : Term Pr Γ τ)
    → P7 σ isRd τ (FL-f isRd p t) {!   !}
    -- → P7 σ isRd τ (FL-f isRd fun t) (FL-f' isRd fun t)
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
chad-in-P7 isRd t =
    let fun = {!   !}
        lemma = fundamental-lemma isRd fun t
        a = {!   !}
        b = {!   !}
    in {!   !}
