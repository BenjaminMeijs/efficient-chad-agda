module correctness.lemmas.value-compatibility-lemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Agda.Builtin.Maybe using (just; nothing)

open import Data.List using ([]; _∷_; map)
open import Data.Product using (_×_)
open import Data.Sum using (inj₁; inj₂)

open import spec
open import correctness.spec

≃τ-zerov : ( τ : Typ Pr ) →  ( x : Rep τ )  → zerov (D2τ' τ) .fst ≃τ x
≃τ-zerov Un _ = tt
≃τ-zerov Inte _ = tt
≃τ-zerov R _ = tt
≃τ-zerov ( σ :* τ ) _ = tt
≃τ-zerov ( σ :+ τ ) _ = tt

≃τ-inj₁ : ( σ τ : Typ Pr ) 
    → ( x : LinRep (D2τ' σ)) (y : Rep σ)
    → (x ≃τ y) → _≃τ_ {σ :+ τ} (just (inj₁ x)) (inj₁ y)
≃τ-inj₁ Un _ _ _ _ = tt
≃τ-inj₁ Inte _ _ _ _ = tt
≃τ-inj₁ R _ _ _ _ = tt
≃τ-inj₁ ( _ :* _ ) _ _ _ w = w
≃τ-inj₁ ( _ :+ _ ) _ _ _ w = w

≃τ-transL : ( τ : Typ Pr ) → ( x : LinRep (D2τ' τ) ) → ( y : LinRep (D2τ' τ) ) → ( z : Rep τ )
        → x ≡ y → x ≃τ z → y ≃τ z
≃τ-transL τ x y z refl w2 = w2

≃τ-transR : ( τ : Typ Pr ) → ( x : LinRep (D2τ' τ) ) → ( y : Rep τ ) → ( z : Rep τ )
        → y ≡ z → x ≃τ y → x ≃τ z
≃τ-transR τ x y z refl w = w

≃Γ-transL : {Γ : Env Pr} {τ : Typ Pr} 
        → ( x : LEtup (map D2τ' Γ) ) → ( y : LEtup (map D2τ' Γ) ) → ( z : Val Pr Γ )
        → x ≡ y → x ≃Γ z → y ≃Γ z
≃Γ-transL {[]}    {τ} _ _ _ _    _ = tt
≃Γ-transL {σ ∷ Γ} {τ} _ _ _ refl w = w

≃Γ-fst : {Γ' : Env Pr} {τ : Typ Pr} 
    → let Γ = τ ∷ Γ' in ( x : LEtup (map D2τ' Γ) )
    → (y : Rep τ ) ( ys : Val Pr Γ' )
    → (x ≃Γ push y ys) → fst x ≃τ y
≃Γ-fst {Γ} {Un} (x , xs) y ys w = tt
≃Γ-fst {Γ} {Inte} (x , xs) y ys w = tt
≃Γ-fst {Γ} {R} (x , xs) y ys w = tt
≃Γ-fst {Γ} {σ :* τ} (x , xs) y ys w = w .fst
≃Γ-fst {Γ} {σ :+ τ} (x , xs) y ys w = w .fst

≃Γ-snd : {Γ' : Env Pr} {τ : Typ Pr} 
    → let Γ = τ ∷ Γ' in ( x : LEtup (map D2τ' Γ) )
    → (y : Rep τ ) ( ys : Val Pr Γ' )
    → (x ≃Γ push y ys) → snd x ≃Γ ys
≃Γ-snd {Γ} {Un} (x , xs) y ys w = w
≃Γ-snd {Γ} {Inte} (x , xs) y ys w = w
≃Γ-snd {Γ} {R} (x , xs) y ys w = w
≃Γ-snd {Γ} {σ :* τ} (x , xs) y ys w = w .snd
≃Γ-snd {Γ} {σ :+ τ} (x , xs) y ys w = w .snd

≃Γ-intro-zero : {Γ : Env Pr} {τ : Typ Pr}
            → (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ) (x : Rep τ)
            → evIn ≃Γ val
            → (zerov (D2τ' τ) .fst , evIn) ≃Γ push x val
≃Γ-intro-zero {Γ} {Un}     _ _ _ w = w
≃Γ-intro-zero {Γ} {Inte}   _ _ _ w = w
≃Γ-intro-zero {Γ} {R}      _ _ _ w = w
≃Γ-intro-zero {Γ} {σ :* τ} _ _ _ w = tt , w
≃Γ-intro-zero {Γ} {σ :+ τ} _ _ _ w = tt , w


x≃τz-and-y≃τz-implies-x≃₃y : {τ : Typ Pr}
    → (x : LinRep (D2τ' τ)) (y : LinRep (D2τ' τ)) (z : Rep τ)
    → (x ≃τ z) → (y ≃τ z) → (x ≃₃ y)
x≃τz-and-y≃τz-implies-x≃₃y {Un} x y z w1 w2 = tt
x≃τz-and-y≃τz-implies-x≃₃y {Inte} x y z w1 w2 = tt
x≃τz-and-y≃τz-implies-x≃₃y {R} x y z w1 w2 = tt
x≃τz-and-y≃τz-implies-x≃₃y {σ :* τ} (just (x , xs)) (just (y , ys)) (z , zs) w1 w2
    = x≃τz-and-y≃τz-implies-x≃₃y x y z (w1 .fst) (w2 .fst) , x≃τz-and-y≃τz-implies-x≃₃y xs ys zs (w1 .snd) (w2 .snd)
x≃τz-and-y≃τz-implies-x≃₃y {σ :* τ} (just _) nothing (_ , _) _ _ = tt
x≃τz-and-y≃τz-implies-x≃₃y {σ :* τ} nothing (just _) (_ , _) _ _ = tt
x≃τz-and-y≃τz-implies-x≃₃y {σ :* τ} nothing nothing (_ , _) _ _ = tt
x≃τz-and-y≃τz-implies-x≃₃y {σ :+ τ} (just (inj₁ x)) (just (inj₁ y)) (inj₁ z) w1 w2
    = x≃τz-and-y≃τz-implies-x≃₃y x y z w1 w2
x≃τz-and-y≃τz-implies-x≃₃y {σ :+ τ} (just (inj₂ x)) (just (inj₂ y)) (inj₂ z) w1 w2
    = x≃τz-and-y≃τz-implies-x≃₃y x y z w1 w2
x≃τz-and-y≃τz-implies-x≃₃y {σ :+ τ} (just (inj₁ _)) nothing (inj₁ z) _ _ = tt
x≃τz-and-y≃τz-implies-x≃₃y {σ :+ τ} (just (inj₂ _)) nothing (inj₂ _) _ _ = tt
x≃τz-and-y≃τz-implies-x≃₃y {σ :+ τ} nothing (just _) (inj₁ _) _ _ = tt
x≃τz-and-y≃τz-implies-x≃₃y {σ :+ τ} nothing (just _) (inj₂ _) _ _ = tt
x≃τz-and-y≃τz-implies-x≃₃y {σ :+ τ} nothing nothing (inj₁ _) _ _ = tt
x≃τz-and-y≃τz-implies-x≃₃y {σ :+ τ} nothing nothing (inj₂ _) _ _ = tt

≃τ-and-≃Γ-implies-≃₄ : {Γ : Env Pr} {τ : Typ Pr}
    → (idx : Idx Γ τ) (ctg : LinRep (D2τ' τ)) (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ)
    → (ctg ≃τ valprj val idx) → (evIn ≃Γ val)
    → (idx , ctg) ≃₄ evIn
≃τ-and-≃Γ-implies-≃₄ Z ctg (x , xs) (push y ys) w1 w2
    = x≃τz-and-y≃τz-implies-x≃₃y ctg x y w1 (≃Γ-fst (x , xs) y ys w2)
≃τ-and-≃Γ-implies-≃₄ (S idx) ctg (x , xs) (push y ys) w1 w2
    = ≃τ-and-≃Γ-implies-≃₄ idx ctg xs ys w1 (≃Γ-snd (x , xs) y ys w2)

≃τ-and-≃Γ-implies-≃₅ : {Γ : Env Pr} {τ : Typ Pr}
    → (idx : Idx Γ τ) (ctg : LinRep (D2τ' τ)) (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ)
    → (ctg ≃τ valprj val idx) → (evIn ≃Γ val)
    → (idx , ctg) ≃₅ val
≃τ-and-≃Γ-implies-≃₅ Z ctg (x , xs) (push y ys) w1 w2
    = w1
≃τ-and-≃Γ-implies-≃₅ (S idx) ctg (x , xs) (push y ys) w1 w2
    = ≃τ-and-≃Γ-implies-≃₅ idx ctg xs ys w1 (≃Γ-snd (x , xs) y ys w2)


plusv-preserves-≃τ : {τ : Typ Pr}
    → (x : LinRep (D2τ' τ)) (y : LinRep (D2τ' τ)) (z : Rep τ)
    → (x ≃₃ y) → (x ≃τ z) → (y ≃τ z)
    → fst (plusv (D2τ' τ) x y) ≃τ z
plusv-preserves-≃τ {Un} _ _ _ _ _ _ = tt
plusv-preserves-≃τ {Inte} _ _ _ _ _ _ = tt
plusv-preserves-≃τ {R} _ _ _ _ _ _ = tt
plusv-preserves-≃τ {σ :* τ} (just x) (just x₁) z w1 w2 w3
    = plusv-preserves-≃τ (x .fst) (x₁ .fst) (z .fst) (w1 .fst) (w2 .fst) (w3 .fst) , plusv-preserves-≃τ (x .snd) (x₁ .snd) (z .snd) (w1 .snd) (w2 .snd) (w3 .snd)
plusv-preserves-≃τ {σ :* τ} (just (x , xs)) nothing (z , zs) tt w2 w3 = w2 .fst , w2 .snd
plusv-preserves-≃τ {σ :* τ} nothing (just (y , ys)) (z , zs) w1 w2 w3 = w3 .fst , w3 .snd
plusv-preserves-≃τ {σ :* τ} nothing nothing _ _ _ _ = tt
plusv-preserves-≃τ {σ :+ τ} (just (inj₁ x)) (just (inj₁ x₁)) (inj₁ x₂) w1 w2 w3 = plusv-preserves-≃τ x x₁ x₂ w1 w2 w3
plusv-preserves-≃τ {σ :+ τ} (just (inj₂ y₁)) (just (inj₂ y₂)) (inj₂ y) w1 w2 w3 = plusv-preserves-≃τ y₁ y₂ y w1 w2 w3
plusv-preserves-≃τ {σ :+ τ} (just _) nothing (inj₁ x₁) w1 w2 w3 = w2
plusv-preserves-≃τ {σ :+ τ} (just _) nothing (inj₂ y) w1 w2 w3 = w2
plusv-preserves-≃τ {σ :+ τ} nothing (just _) (inj₁ _) w1 w2 w3 = w3
plusv-preserves-≃τ {σ :+ τ} nothing (just _) (inj₂ _) w1 w2 w3 = w3
plusv-preserves-≃τ {σ :+ τ} nothing nothing (inj₁ _) w1 w2 w3 = tt
plusv-preserves-≃τ {σ :+ τ} nothing nothing (inj₂ _) w1 w2 w3 = tt

addLEτ-preserves-≃Γ : {Γ : Env Pr} {τ : Typ Pr}
            → (idx : Idx Γ τ) (ctg : LinRep (D2τ' τ)) (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ)
            → (evIn ≃Γ val) → ((idx , ctg) ≃₄ evIn) → ((idx , ctg) ≃₅ val)
            → addLEτ (convIdx D2τ' idx) ctg evIn ≃Γ val
addLEτ-preserves-≃Γ {Un ∷ Γ} Z ctg (x , xs) (push y val) w _ _ = w
addLEτ-preserves-≃Γ {Inte ∷ Γ} Z ctg (x , xs) (push y val) w _ _ = w
addLEτ-preserves-≃Γ {R ∷ Γ} Z ctg (x , xs) (push y val) w _ _ = w
addLEτ-preserves-≃Γ {(σ :* τ) ∷ Γ} Z ctg (x , xs) (push y val) w1 w2 w3 = plusv-preserves-≃τ {σ :* τ} ctg x y w2 w3 (w1 .fst) , (w1 .snd)
addLEτ-preserves-≃Γ {(σ :+ τ) ∷ Γ} Z ctg (x , xs) (push y val) w1 w2 w3 = plusv-preserves-≃τ {σ :+ τ} ctg x y w2 w3 (w1 .fst) , (w1 .snd)
addLEτ-preserves-≃Γ {Un ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = addLEτ-preserves-≃Γ idx ctg xs val w1 w2 w3 
addLEτ-preserves-≃Γ {Inte ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = addLEτ-preserves-≃Γ idx ctg xs val w1 w2 w3 
addLEτ-preserves-≃Γ {R ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = addLEτ-preserves-≃Γ idx ctg xs val w1 w2 w3 
addLEτ-preserves-≃Γ {(σ :* τ) ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = w1 .fst , addLEτ-preserves-≃Γ idx ctg xs val (w1 .snd) w2 w3 
addLEτ-preserves-≃Γ {(σ :+ τ) ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = w1 .fst , addLEτ-preserves-≃Γ idx ctg xs val (w1 .snd) w2 w3
