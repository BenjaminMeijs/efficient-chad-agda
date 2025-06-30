module spec.HL where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Level using (Level)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; map; _∷_; [])
open import Function.Base using (const; _∘_)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

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