{-# OPTIONS --allow-unsolved-metas #-}
module HO-correctness.logical-relation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)

open import Data.Empty using (⊥)
open import Data.List using (_∷_; map; [])
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_]; isInj₁; isInj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Function.Base using (id; _$_; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)

open import spec
open import correctness.spec
open import correctness.dsyn-defined
open import correctness.chad-ctg-zero
open import correctness.lemmas
open import correctness.dsem

-- τ is a nested tuple of Rs
Is-ℝᵈ : ( τ : Typ Pr ) → Set
Is-ℝᵈ Un = ⊤
Is-ℝᵈ Inte = ⊥
Is-ℝᵈ R = ⊤
Is-ℝᵈ (σ :* τ) = Is-ℝᵈ σ × Is-ℝᵈ τ
Is-ℝᵈ (σ :+ τ) = ⊥
Is-ℝᵈ (σ :-> τ) = ⊥

to-primal : { τ : Typ Pr } → Is-ℝᵈ τ → Rep τ → Rep (D1τ τ)
to-primal {Un} isRd x = tt
to-primal {R} isRd x = x
to-primal {τ1 :* τ2} isRd x = to-primal (isRd .fst) (x .fst) , to-primal (isRd .snd) (x .snd) 

un-primal : { τ : Typ Pr } → (Is-ℝᵈ τ) → Rep (D1τ τ) → Rep τ
un-primal {Un} isRd x = tt
un-primal {R} isRd x = x
un-primal {τ1 :* τ2} isRd x = un-primal (isRd .fst) (x .fst) , un-primal (isRd .snd) (x .snd)

-- Nested and combined extensional equality
-- f is equivalent to g and f' is equivalent to g'
P7≡ : ( σ : Typ Pr ) → ( isRd : Is-ℝᵈ σ  ) → ( τ : Typ Pr )
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (g : Rep σ → Rep τ)
    → (g' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
P7≡ σ _ _ f f' g g' = f ≗ g 
  × ((x : Rep (D1τ σ)) → 
        let (f1 , f2) = f' x
            (g1 , g2) = g' x
        in f1 ≡ g1 × f2 ≗ g2)

P7 : ( σ : Typ Pr ) → ( Is-ℝᵈ σ )
    → (τ : Typ Pr)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
P7 ρ isRd Un f f' = 
  -- f f' is equivalent to the corresponding (zero) functions
  P7≡ ρ isRd Un f f' (const tt) (const (tt , const (zerovDense (D2τ' ρ))))
-- P7 ρ isRd Inte f f' = P7≡ ρ isRd Inte f f' f (λ x → (f x , const (zerovDense (D2τ' ρ))))
P7 ρ isRd Inte f f' = P7≡ ρ isRd Inte f f' f (λ x → (f (un-primal isRd x) , const (zerovDense (D2τ' ρ))))
P7 ρ isRd R f f' =
  -- Forall possible inputs of f' ...
  ( x : Rep ρ ) → 
  -- ... the first element of the tuple produced by f'
  -- is equivalent to f ...
  -- (f x ≡ f' x .fst) 
  (f x ≡ f' (to-primal isRd x) .fst) 
--   -- ... and the second element of the tuple produced by f'
--   -- is equivalent to the transposed derivative of f.
  × ((dsem : Is-just (DSemᵀ {ρ} {R} f x))
    --  → f' x .snd ≗ (to-witness dsem))
     → f' (to-primal isRd x) .snd ≗ (to-witness dsem))
P7 ρ isRd (σ :* τ) f f' =
  -- There exists some l l' and r r' ...
  Σ ((Rep ρ → Rep σ) × (Rep ρ → Rep τ)
      × (Rep (D1τ ρ) → ( Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
      × (Rep (D1τ ρ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' ρ)))))
  λ (l , r , l' , r' )
  -- ... that are in P7 ...
  → Σ (P7 ρ isRd σ l l' 
     × P7 ρ isRd τ r r')
  (λ _ → 
  -- ... and combined show that f f' is in P6.
    let h  = λ x → (l x , r x )
        h' = λ x → (l' x .fst , r' x .fst) 
                , (λ ctg → case ctg of
                   maybe′ (λ (ctgL , ctgR) → plusvDense _ (l' x .snd ctgL) (r' x .snd ctgR)) 
                          (zerovDense (D2τ' ρ)))
    in P7≡ ρ isRd (σ :* τ) f f' h h'
  )
P7 ρ isRd (σ :+ τ) f f' = {!   !}
P7 ρ isRd (σ :-> τ) F F' =
-- There exists some f f' ...  (Without EVM types)
  Σ ((Rep ρ → Rep σ → Rep τ)
    × (Rep (D1τ ρ) → (Rep (D1τ σ) → Rep (D1τ τ) × (Rep (D2τ τ) → Rep (Lin Dyn) × Rep (D2τ σ))) × (LinRep Dyn → LinRepDense (D2τ' ρ))))
  λ (f , f')
-- ... such that for all g g' ...
  → (g : Rep ρ → Rep σ) 
  → (g' : Rep (D1τ ρ) → (Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
-- ... where g g' is in P7 ...
  → P7 ρ isRd σ g g'
-- ... g g' applied to f f' is shown to be in P7 ... 
  → (let h  = λ x → f x (g x) 
         h' = λ x → let (f1 , f2) = f' x
                        (g1 , g2) = g' x
                        (h1 , h2) = f1 g1
                     in h1 , (λ y → let (d , z) = h2 y in plusvDense (D2τ' ρ) (f2 d) (g2 z))
     in P7 ρ isRd τ h h')
-- ... and f f' is equivalent to F F' .
-- [Note, this is not just extentional equality, but semantic equality of executing an EVM]
  × ((x : Rep ρ) (y : Rep σ) → f x y ≡ F x y .fst) 
  × ((x : Rep (D1τ ρ)) (y : Rep (D1τ σ)) → 
        let (f1 , f2) = f' x 
            (f3 , f4) = f1 y
            (F1 , F2) = F' x
            ((F3 , F4) , _) = F1 y
            F4' = λ ctg → let (a , b , _) = LACMexec (F4 ctg .fst) (nothing , ((zerov (D2τ' σ) .fst) , tt))
                          in a , b
        in f2 ≗ F2 × f3 ≡ F3 × f4 ≗ F4')