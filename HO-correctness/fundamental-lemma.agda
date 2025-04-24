module HO-correctness.fundamental-lemma where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)

open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Data.List using (List; map; _∷_; []; foldr; foldl)
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


HL : {A : Set} → (L : List A) → (A → Set) → Set
HL [] f = ⊤
HL (x ∷ Γ) f = f x × HL Γ f

zero-LEtup : ( Γ : Env Pr ) → LEtup (map D2τ' Γ)
zero-LEtup [] = tt
zero-LEtup (τ ∷ Γ) = (zerov (D2τ' τ) .fst) , (zero-LEtup Γ)

precond : {σ : Typ Pr}
    → (q : Is-ℝᵈ σ)
    → Typ Pr → Set
precond {σ} q τ =
    (Σ ((Rep σ → Rep τ) × 
        (Rep (D1τ σ) → Rep (D1τ τ) 
                                × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ)))) 
        (λ (f , f') → P7 σ q τ f f'))


Fundament : { σ : Typ Pr }
    → ( Γ : Env Pr )
    → (q : Is-ℝᵈ σ)
    → Set
Fundament {σ} [] q = ⊤
Fundament {σ} (τ ∷ Γ) q = 
            (Σ ((Rep σ → Rep τ) × 
                (Rep (D1τ σ) → Rep (D1τ τ) 
                                        × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ)))) 
                (λ (f , f') → P7 σ q τ f f'))
    × Fundament Γ q

Fundament-apply-f : {G Γ : Env Pr}
    → let σ = Etup Pr G
    in (q : Is-ℝᵈ σ)
    → Fundament Γ q → Rep σ 
    → Rep (Etup Pr Γ)
Fundament-apply-f {_} {[]} _ _ _ = tt
Fundament-apply-f {G} {τ ∷ Γ} q (((f , _) , _), w) x = 
    f x , Fundament-apply-f {G} {Γ} q w x

FL-f : {Γ : Env Pr}
    { τ : Typ Pr } ( isRd : Is-ℝᵈ (Etup Pr Γ) )
    → Fundament Γ isRd
    → Term Pr Γ τ
    → Rep (Etup Pr Γ) → Rep τ
FL-f isRd w t x = interp t (Etup-to-val (Fundament-apply-f isRd w x))

ctgPropagators :
    ( Γ : Env Pr )
    → ( σ : Typ Pr)
    → Set
ctgPropagators [] σ = ⊤
ctgPropagators (τ ∷ Γ) σ = 
    (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))
    × ctgPropagators Γ σ

getCtgPropagators : {G Γ : Env Pr}
    → (q : Is-ℝᵈ (Etup Pr G))
    → Fundament Γ q → Rep (D1τ (Etup Pr G))
    → ctgPropagators Γ (Etup Pr G)
getCtgPropagators {G} {[]} _ _ _ = tt
getCtgPropagators {G} {τ ∷ Γ} q (((_ , f') , _), w) x
    = (f' x .snd) , (getCtgPropagators {G} {Γ} q w x)


sumCtgPropagators : {G Γ : Env Pr}
    → (q1 : Is-ℝᵈ (Etup Pr G))
    → (q2 : Is-ℝᵈ (Etup Pr Γ))
    → ctgPropagators Γ (Etup Pr G) → EV (map D2τ' Γ)
    → EV (map D2τ' G)
sumCtgPropagators {G} {[]} q1 q2 w x = zero-EV (map D2τ' G)
sumCtgPropagators {G} {τ ∷ Γ} q1 q2 (h' , w) (x , xs) = 
    Etup-to-EV (h' (dense2sparse (fst q2) x)) 
    ev+ sumCtgPropagators {G} {Γ} q1 (snd q2) w xs

Fundament-apply-f' : {G Γ : Env Pr}
    → (q : Is-ℝᵈ (Etup Pr G))
    → Fundament Γ q → Rep (D1τ (Etup Pr G))
    → Rep (D1τ (Etup Pr Γ))
Fundament-apply-f' {_} {[]} _ _ _ = tt
Fundament-apply-f' {G} {τ ∷ Γ} q (((_ , f') , _), w) x = 
    (f' x .fst , Fundament-apply-f' {G} {Γ} q w x)

FL-f' : {Γ : Env Pr} {τ : Typ Pr}
    → (isRd : Is-ℝᵈ (Etup Pr Γ))
    → (Fundament Γ isRd)
    → (Term Pr Γ τ)
    → (Rep (D1τ (Etup Pr Γ))
    → Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' (Etup Pr Γ))))
FL-f' {Γ} {τ} isRd w t x =
    let env = Fundament-apply-f' {Γ} {Γ} isRd w x
        propagators = getCtgPropagators {Γ} {Γ} isRd w x
        (g , g') = interp (chad t) (Etup-to-val (Etup-D1τ-distr₁ Γ env))
    in g , λ ctg → let w = LEtup2EV {map D2τ' Γ} (LACMexec (g' ctg .fst) (zero-LEtup Γ))
                   in EV-to-Etup (sumCtgPropagators isRd isRd propagators w)

fundamental-lemma : {Γ : Env Pr} {τ : Typ Pr}
    → let σ = Etup Pr Γ
          LΓ = map D2τ' Γ
      in (isRd : Is-ℝᵈ σ)
    → (fun : Fundament Γ isRd)
    → (t : Term Pr Γ τ)
    → P7 σ isRd τ (FL-f isRd fun t) (FL-f' isRd fun t)
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
