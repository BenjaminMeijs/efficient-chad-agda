{-# OPTIONS --allow-unsolved-metas #-}
module HO-correctness.fundamental-lemma where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)
open import Level using (Level)

open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; map; _∷_; []; foldr; foldl; zipWith)
open import Function.Base using (id; _$_; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; dcong₂; subst; trans; cong; cong₂; _≗_)

open import spec hiding (LR)
open import correctness.spec
open import correctness.dsem
open import correctness.lemmas
open import HO-correctness.logical-relation
open import HO-correctness.lemmas
open import HO-correctness.projection
open import HO-correctness.basics-about-relation

-- ==============================
-- Heterogeneous lists
-- ==============================

HL : {l : Level} → {A : Set l} 
    → (L : List A) → (A → Set) → Set
HL [] f = ⊤
HL (x ∷ Γ) f = f x × HL Γ f

HL-fromList : {A : Set} → ( L : List A ) → HL L (const A)
HL-fromList [] = tt
HL-fromList (x ∷ L) = x , HL-fromList L

HL-chain : {A B : Set} → { L : List A } → { f : B → Set }
    → { g : A → B }
    → HL L (f ∘ g) ≡ HL (map g L) f
HL-chain {L = []} = refl
HL-chain {L = (x ∷ L)} = cong₂ _×_ refl HL-chain

HL-map : {A : Set} → { α β : A → Set } → {L : List A}
    → (f : (a : A) → (α a) → (β a)) → ( xs : HL L α) → HL L β
HL-map {A} {α} {β} {[]} f x = tt
HL-map {A} {α} {β} {a ∷ L} f (x , xs) = f a x , HL-map f xs

HL-foldr : {A B : Set} → { α : A → Set} → {L : List A}
    → (f : (a : A) → (α a) → B → B) → B → HL L α → B
HL-foldr {L = []} c n xs = n
HL-foldr {L = a ∷ L} c n (x , xs) = c a x (HL-foldr c n xs)

HL-foldl : {A B : Set} → { α : A → Set} → {L : List A}
    → (f : (a : A) → (α a) → B → B) → B → HL L α → B
HL-foldl {L = []} c n xs = n
HL-foldl {L = a ∷ L} c n (x , xs) = HL-foldl c (c a x n) xs

HL-index : {A : Set}
    → ( L : List A )
    → HL L (const ℕ)
HL-index [] = tt
HL-index (x ∷ xs) = zero , HL-map (λ _ n → suc n) (HL-index xs)

HL-zipWith : {A : Set} → {α β ɣ : A → Set }
    → { L : List A }
    → (f : ( a : A ) → (α a) → (β a) → (ɣ a))
    → HL L α → HL L β → HL L ɣ
HL-zipWith {L = []} f x y = tt
HL-zipWith {L = a ∷ L} f (x , xs) (y , ys) 
    = f a x y , HL-zipWith f xs ys

HL-map-equiv : {A : Set} {L : List A}
    → {α β : A → Set}
    → { f1 : (a : A) → (α a) → (β a) }
    → { f2 : (a : A) → (α a) → (β a) }
    → { xs : HL L α }
    → ( (a : A) → (v : α a) → f1 a v ≡ f2 a v )
    → HL-map f1 xs ≡ HL-map f2 xs
HL-map-equiv {A} {[]} p = refl
HL-map-equiv {A} {τ ∷ L} {α} {β} {f1} {f2} {xs} p = cong₂ _,_ (p τ (xs .fst)) (HL-map-equiv {A} {L} {α} {β} {f1} {f2} { xs .snd } p)

HL-map-chain : {A : Set} {L : List A}
    → {α β ɣ : A → Set}
    → ( f : (a : A) → (α a) → (β a) )
    → ( g : (a : A) → (β a) → (ɣ a) )
    → ( xs : HL L α )
    → HL-map g (HL-map f xs) 
      ≡ HL-map (λ a v → g a (f a v)) xs
HL-map-chain {A} {[]} f g xs = refl
HL-map-chain {A} {τ ∷ L} f g xs = cong₂ _,_ refl (HL-map-chain f g (xs .snd))

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

LEtup-≡-HL : ( Γ : Env Pr ) → LEtup (map D2τ' Γ) ≡ HL (map D2τ' Γ) LinRep
LEtup-≡-HL [] = refl
LEtup-≡-HL (x ∷ Γ) = cong₂ _×_ refl (LEtup-≡-HL Γ)
LEtup-to-HL : { Γ : Env Pr } → LEtup (map D2τ' Γ) → HL (map D2τ' Γ) LinRep
LEtup-to-HL {Γ} x = sub (LEtup-≡-HL Γ) x
HL-to-LEtup : { Γ : Env Pr } → HL (map D2τ' Γ) LinRep → LEtup (map D2τ' Γ) 
HL-to-LEtup {Γ} x = sub (sym $ LEtup-≡-HL Γ) x


precond : {σ : Typ Pr}
    → (q : Is-ℝᵈ σ)
    → Typ Pr → Set
precond {σ} q τ =
    (Σ ((Rep σ → Rep τ) × 
        (Rep (D1τ σ) → Rep (D1τ τ) 
                                × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ)))) 
        (λ (f , f') → LR σ q τ f f'))

zero-LEtup : ( Γ : Env Pr ) → LEtup (map D2τ' Γ)
zero-LEtup [] = tt
zero-LEtup (τ ∷ Γ) = (zerov (D2τ' τ) .fst) , (zero-LEtup Γ)

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
    → HL Γ (propagator (Etup Pr Γ)) → LEtup (map D2τ' Γ)
    → LinRepDense (D2τ' (Etup Pr Γ))
sumCtgPropagators {Γ} q l1 w = 
    let l2 = sub (sym HL-chain) (LEtup-to-HL w)
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
    in g , λ ctg → let w = (LACMexec (g' ctg .fst) (zero-LEtup Γ))
                   in sumCtgPropagators isRd propagators w

fundamental-lemma : ( Γ : Env Pr ) ( τ : Typ Pr )
    → let σ = Etup Pr Γ
          LΓ = map D2τ' Γ
      in (isRd : Is-ℝᵈ σ)
    → (p : HL Γ (precond isRd)) 
    → (t : Term Pr Γ τ)
    → LR σ isRd τ (FL-f isRd p t) (FL-f' isRd p t)
fundamental-lemma Γ τ isRd a t = {!   !}
 