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
open import Data.Product using (_×_; Σ; swap)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import spec hiding (LR)
open import correctness.spec
open import correctness.dsyn-defined
open import correctness.chad-ctg-zero
open import correctness.lemmas
open import correctness.dsem

-- τ is a nested tuple of Rs
Is-ℝᵈ : ∀ {tag} ( τ : Typ tag ) → Set
Is-ℝᵈ Un = ⊤
Is-ℝᵈ Inte = ⊥
Is-ℝᵈ R = ⊤
Is-ℝᵈ (σ :* τ) = Is-ℝᵈ σ × Is-ℝᵈ τ
Is-ℝᵈ (σ :+ τ) = ⊥
Is-ℝᵈ (σ :-> τ) = ⊥
Is-ℝᵈ _ = ⊥

Is-ℝᵈ? : ∀ {tag} ( τ : Typ tag ) → Dec (Is-ℝᵈ τ)
Is-ℝᵈ? Un = yes tt
Is-ℝᵈ? Inte = no λ ()
Is-ℝᵈ? R = yes tt
Is-ℝᵈ? (τ1 :* τ2) 
  with Is-ℝᵈ? τ1 | Is-ℝᵈ? τ2
... | yes a | yes b = yes (a , b)
... | a | no b = no λ z → b (z .snd)
... | no a | b = no λ z → a (z .fst)
Is-ℝᵈ? (τ1 :+ τ2) = no λ ()
Is-ℝᵈ? (τ1 :-> τ2) = no λ ()
Is-ℝᵈ? (EVM x τ) = no λ ()
Is-ℝᵈ? (Lin x) = no λ ()

primal-Is-ℝᵈ : {τ : Typ Pr} → Is-ℝᵈ τ → Is-ℝᵈ (D1τ τ)
primal-Is-ℝᵈ {Un} x = tt
primal-Is-ℝᵈ {R} x = tt
primal-Is-ℝᵈ {τ :* τ₁} x = primal-Is-ℝᵈ (x .fst) , primal-Is-ℝᵈ (x .snd)

Is-Linear : {τ σ : LTyp} → (LinRep τ → Maybe (Σ LTyp LinRep) × LinRep σ) → Set
Is-Linear {τ} {σ} f =
  -- f 0 is zero
  ((ctg0 : LinRep τ) → (w : sparse2dense ctg0 ≡ zerovDense τ) 
    → let (a , b) = f ctg0
      in ((τ2 : LTyp) → sparse2dense {Dyn} a τ2 ≡ zerovDense τ2) 
          × sparse2dense b ≡ zerovDense σ)
  -- f (x + y) is f x + f y
  × ((ctg1 ctg2 : LinRep τ) → Compatible-LinReps ctg1 ctg2
      → let (a0 , b0) = f (plusv _ ctg1 ctg2 .fst)
            (a1 , b1) = f ctg1
            (a2 , b2) = f ctg2
        in a0 ≡ plusv Dyn a1 a2 .fst × b0 ≡ plusv _ b1 b2 .fst)


to-primal : { τ : Typ Pr } → Is-ℝᵈ τ → Rep τ → Rep (D1τ τ)
to-primal {Un} isRd x = tt
to-primal {R} isRd x = x
to-primal {τ1 :* τ2} isRd x = to-primal (isRd .fst) (x .fst) , to-primal (isRd .snd) (x .snd) 

un-primal : { τ : Typ Pr } → Is-ℝᵈ τ → Rep (D1τ τ) → Rep τ
un-primal {Un} isRd x = tt
un-primal {R} isRd x = x
un-primal {τ1 :* τ2} isRd x = un-primal (isRd .fst) (x .fst) , un-primal (isRd .snd) (x .snd)

-- Nested and combined extensional equality
-- f is equivalent to g and f' is equivalent to g'
LR≡ : ( σ : Typ Pr ) → ( isRd : Is-ℝᵈ σ  ) → ( τ : Typ Pr )
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (g : Rep σ → Rep τ)
    → (g' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
LR≡ σ _ _ f f' g g' = f ≗ g 
  × ((x : Rep (D1τ σ)) → 
        let (f1 , f2) = f' x
            (g1 , g2) = g' x
        in f1 ≡ g1 × f2 ≗ g2)

LR : ( σ : Typ Pr ) → ( Is-ℝᵈ σ )
    → (τ : Typ Pr)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
LR ρ isRd Un f f' = 
  -- f f' is equivalent to the corresponding (zero) functions
  LR≡ ρ isRd Un f f' (const tt) (const (tt , const (zerovDense (D2τ' ρ))))
-- LR ρ isRd Inte f f' = LR≡ ρ isRd Inte f f' f (λ x → (f x , const (zerovDense (D2τ' ρ))))
LR ρ isRd Inte f f' = LR≡ ρ isRd Inte f f' f (λ x → (f (un-primal isRd x) , const (zerovDense (D2τ' ρ))))
LR ρ isRd R f f' =
  -- f f' is in the logical relation if:
  -- For all possible inputs of f' ...
  ( x : Rep ρ ) → 
  -- ... the first element of the tuple produced by f'
  -- is equivalent to f ...
  -- (f x ≡ f' x .fst) 
  (f x ≡ f' (to-primal isRd x) .fst) 
  -- ... and the function is differentiable at x ...
  × (Σ  (Is-just (DSemᵀ {ρ} {R} f x))
  -- ... and the second element of the tuple produced by f'
  -- is equivalent to the transposed derivative of f.
        (λ dsem → f' (to-primal isRd x) .snd ≗ (to-witness dsem)))
LR ρ isRd (σ :* τ) f f' =
  -- f f' is in the logical relation if:
  -- There exists some l l' and r r' ...
  Σ ((Rep ρ → Rep σ) × (Rep ρ → Rep τ)
      × (Rep (D1τ ρ) → ( Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
      × (Rep (D1τ ρ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' ρ)))))
  λ (l , r , l' , r' )
  -- ... that are in the logical relation ...
  → Σ (LR ρ isRd σ l l' 
     × LR ρ isRd τ r r')
  (λ _ → 
  -- ... and can be combined using pair to get h and h' ...
    let h  = λ x → (l x , r x )
        h' = λ x → (l' x .fst , r' x .fst) 
                , (λ ctg → case ctg of
                   maybe′ (λ (ctgL , ctgR) → plusvDense _ (l' x .snd ctgL) (r' x .snd ctgR)) 
                          (zerovDense (D2τ' ρ)))
  -- ... such that h h' is equivalent to f f'
    in LR≡ ρ isRd (σ :* τ) f f' h h'
  )
LR ρ isRd (σ :+ τ) f f' = {!   !}
LR ρ isRd (σ :-> τ) F F' =
-- F F' is in the relation if:
-- There exists some f f' ...  (Essentially F F' without EVM types)
  Σ ((Rep ρ → Rep σ → Rep τ)
    × (Rep (D1τ ρ) → (Rep (D1τ σ) → Rep (D1τ τ) × (Rep (D2τ τ) → Rep (Lin Dyn) × Rep (D2τ σ))) × (LinRep Dyn → LinRepDense (D2τ' ρ))))
  λ (f , f')
-- ... such that for all g g' ...
  → (g : Rep ρ → Rep σ) 
  → (g' : Rep (D1τ ρ) → (Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
-- ... where g g' is in LR ...
  → LR ρ isRd σ g g'
-- ... g g' applied to f f' is in the relation ... 
  → (let h  = λ x → f x (g x) 
         h' = λ x → let (f1 , f2) = f' x
                        (g1 , g2) = g' x
                        (h1 , h2) = f1 g1
                     in h1 , (λ y → let (d , z) = h2 y in plusvDense (D2τ' ρ) (f' x .snd d) (g2 z))
     in LR ρ isRd τ h h')
-- ... and f f' is equivalent to F F' ...
-- [Note, this is not just extensional equality, but semantic equality of executing an EVM]
  × ((x : Rep ρ) (y : Rep σ) → f x y ≡ F x y .fst) 
  × ((x : Rep (D1τ ρ)) (y : Rep (D1τ σ)) → 
        let (f1 , f2) = f' x 
            (f3 , f4) = f1 y
            (F1 , F2) = F' x
            ((F3 , F4) , _) = F1 y
            F4' = λ ctg → case F4 ctg .fst of 
                            maybe′ swap
                                   (nothing , zerov (D2τ' σ) .fst)
        in f2 ≗ F2 × f3 ≡ F3 × f4 ≗ F4'
  -- and f' is linear.
      × Is-Linear (f' x .fst y .snd))