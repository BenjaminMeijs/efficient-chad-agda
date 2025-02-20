module correctness.lemmas.value-compatibility-lemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Agda.Builtin.Maybe using (just; nothing)

open import Data.List using ([]; _∷_; map)
open import Data.Product using (_×_)
open import Data.Sum using (inj₁; inj₂)

open import spec
open import correctness.spec

-- ===============================
-- Basic lemmas about ≃τ and ≃Γ
-- ===============================

≃τ-zerov : ( τ : Typ Pr ) →  ( x : Rep τ )  → zerov (D2τ' τ) .fst ≃τ x
≃τ-zerov Un _ = tt
≃τ-zerov Inte _ = tt
≃τ-zerov R _ = tt
≃τ-zerov ( σ :* τ ) _ = tt
≃τ-zerov ( σ :+ τ ) _ = tt

≃τ-congL : ( τ : Typ Pr ) → ( x : LinRep (D2τ' τ) ) → ( y : LinRep (D2τ' τ) ) → ( z : Rep τ )
        → x ≡ y → x ≃τ z → y ≃τ z
≃τ-congL τ x y z refl w2 = w2

≃τ-congR : ( τ : Typ Pr ) → ( x : LinRep (D2τ' τ) ) → ( y : Rep τ ) → ( z : Rep τ )
        → y ≡ z → x ≃τ y → x ≃τ z
≃τ-congR τ x y z refl w = w

≃Γ-congL : {Γ : Env Pr} {τ : Typ Pr} 
        → ( x : LEtup (map D2τ' Γ) ) → ( y : LEtup (map D2τ' Γ) ) → ( z : Val Pr Γ )
        → x ≡ y → x ≃Γ z → y ≃Γ z
≃Γ-congL {[]}    {τ} _ _ _ _    _ = tt
≃Γ-congL {σ ∷ Γ} {τ} _ _ _ refl w = w

≃Γ-congR : {Γ : Env Pr} {τ : Typ Pr} 
        → ( x : LEtup (map D2τ' Γ) ) → ( y : Val Pr Γ ) → ( z : Val Pr Γ )
        → y ≡ z → x ≃Γ y → x ≃Γ z
≃Γ-congR {[]}    {τ} _ _ _ _    _ = tt
≃Γ-congR {σ ∷ Γ} {τ} _ _ _ refl w = w

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

≃Γ-split : {Γ' : Env Pr} {τ : Typ Pr} 
    → let Γ = τ ∷ Γ' in ( x : LEtup (map D2τ' Γ) )
    → { y : Rep τ  } ( ys : Val Pr Γ' )
    → (x ≃Γ push y ys) → (fst x ≃τ y × snd x ≃Γ ys)
≃Γ-split {Γ} {Un} (x , xs) {y} ys w = tt , w
≃Γ-split {Γ} {Inte} (x , xs) {y} ys w = tt , w
≃Γ-split {Γ} {R} (x , xs) {y} ys w = tt , w
≃Γ-split {Γ} {τ :* τ₁} (x , xs) {y} ys w = w
≃Γ-split {Γ} {τ :+ τ₁} (x , xs) {y} ys w = w


≃Γ-intro-zero : {Γ : Env Pr} {τ : Typ Pr}
            → (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ) (x : Rep τ)
            → evIn ≃Γ val
            → (zerov (D2τ' τ) .fst , evIn) ≃Γ push x val
≃Γ-intro-zero {Γ} {Un}     _ _ _ w = w
≃Γ-intro-zero {Γ} {Inte}   _ _ _ w = w
≃Γ-intro-zero {Γ} {R}      _ _ _ w = w
≃Γ-intro-zero {Γ} {σ :* τ} _ _ _ w = tt , w
≃Γ-intro-zero {Γ} {σ :+ τ} _ _ _ w = tt , w

-- ===============================
-- Combining ≃τ's and ≃Γ's to create other kinds of compatibility
-- ===============================
≃τ's-implies-Compatible-LinReps : {τ : Typ Pr}
    → (x : LinRep (D2τ' τ)) (y : LinRep (D2τ' τ)) (z : Rep τ)
    → (x ≃τ z) → (y ≃τ z) → (Compatible-LinReps x y)
≃τ's-implies-Compatible-LinReps {Un} x y z w1 w2 = tt
≃τ's-implies-Compatible-LinReps {Inte} x y z w1 w2 = tt
≃τ's-implies-Compatible-LinReps {R} x y z w1 w2 = tt
≃τ's-implies-Compatible-LinReps {σ :* τ} (just (x , xs)) (just (y , ys)) (z , zs) w1 w2
    = ≃τ's-implies-Compatible-LinReps x y z (w1 .fst) (w2 .fst) , ≃τ's-implies-Compatible-LinReps xs ys zs (w1 .snd) (w2 .snd)
≃τ's-implies-Compatible-LinReps {σ :* τ} (just _) nothing (_ , _) _ _ = tt
≃τ's-implies-Compatible-LinReps {σ :* τ} nothing (just _) (_ , _) _ _ = tt
≃τ's-implies-Compatible-LinReps {σ :* τ} nothing nothing (_ , _) _ _ = tt
≃τ's-implies-Compatible-LinReps {σ :+ τ} (just (inj₁ x)) (just (inj₁ y)) (inj₁ z) w1 w2
    = ≃τ's-implies-Compatible-LinReps x y z w1 w2
≃τ's-implies-Compatible-LinReps {σ :+ τ} (just (inj₂ x)) (just (inj₂ y)) (inj₂ z) w1 w2
    = ≃τ's-implies-Compatible-LinReps x y z w1 w2
≃τ's-implies-Compatible-LinReps {σ :+ τ} (just (inj₁ _)) nothing (inj₁ z) _ _ = tt
≃τ's-implies-Compatible-LinReps {σ :+ τ} (just (inj₂ _)) nothing (inj₂ _) _ _ = tt
≃τ's-implies-Compatible-LinReps {σ :+ τ} nothing (just _) (inj₁ _) _ _ = tt
≃τ's-implies-Compatible-LinReps {σ :+ τ} nothing (just _) (inj₂ _) _ _ = tt
≃τ's-implies-Compatible-LinReps {σ :+ τ} nothing nothing (inj₁ _) _ _ = tt
≃τ's-implies-Compatible-LinReps {σ :+ τ} nothing nothing (inj₂ _) _ _ = tt

≃τ-and-≃Γ-implies-Compatible-idx-LEtup : {Γ : Env Pr} {τ : Typ Pr}
    → (idx : Idx Γ τ) (ctg : LinRep (D2τ' τ)) (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ)
    → (ctg ≃τ valprj val idx) → (evIn ≃Γ val)
    → Compatible-idx-LEtup (idx , ctg) evIn
≃τ-and-≃Γ-implies-Compatible-idx-LEtup Z ctg (x , xs) (push y ys) w1 w2
    = ≃τ's-implies-Compatible-LinReps ctg x y w1 (≃Γ-fst (x , xs) y ys w2)
≃τ-and-≃Γ-implies-Compatible-idx-LEtup (S idx) ctg (x , xs) (push y ys) w1 w2
    = ≃τ-and-≃Γ-implies-Compatible-idx-LEtup idx ctg xs ys w1 (≃Γ-snd (x , xs) y ys w2)

≃τ-and-≃Γ-implies-Compatible-idx-val : {Γ : Env Pr} {τ : Typ Pr}
    → (idx : Idx Γ τ) (ctg : LinRep (D2τ' τ)) (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ)
    → (ctg ≃τ valprj val idx) → (evIn ≃Γ val)
    → Compatible-idx-val (idx , ctg) val
≃τ-and-≃Γ-implies-Compatible-idx-val Z ctg (x , xs) (push y ys) w1 w2
    = w1
≃τ-and-≃Γ-implies-Compatible-idx-val (S idx) ctg (x , xs) (push y ys) w1 w2
    = ≃τ-and-≃Γ-implies-Compatible-idx-val idx ctg xs ys w1 (≃Γ-snd (x , xs) y ys w2)

-- ===============================
-- Versions of previous lemmas with (more) implicit arguments
-- ===============================

≃τ-zerov' : ( τ : Typ Pr ) → { x : Rep τ }  → zerov (D2τ' τ) .fst ≃τ x
≃τ-zerov' τ {x} = ≃τ-zerov τ x

≃Γ-intro-zero' : {Γ : Env Pr} ( τ : Typ Pr )
            → { val : Val Pr Γ } { x : Rep τ } 
            → (evIn : LEtup (map D2τ' Γ))
            → evIn ≃Γ val
            → (zerov (D2τ' τ) .fst , evIn) ≃Γ push x val
≃Γ-intro-zero' {Γ} τ {val} {x} evIn w = ≃Γ-intro-zero {Γ} {τ} evIn val x w