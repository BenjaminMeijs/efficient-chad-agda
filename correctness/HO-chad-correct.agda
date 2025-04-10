module correctness.HO-chad-correct where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)

open import Data.Empty using (⊥)
open import Data.List using (_∷_; map; [])
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_]; isInj₁; isInj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Function.Base using (id; const; _∘_; case_of_)
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

-- Nested and combined extensional equality
-- f is equivalent to g and f' is equivalent to g'
P6≡ : ( σ : Typ Pr ) → ( isRd : Is-ℝᵈ σ  ) → ( τ : Typ Pr )
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (g : Rep σ → Rep τ)
    → (g' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
P6≡ _ _ _ f f' g g' = f ≗ g 
  × (∀ {x} → let (f1 , f2) = f' x
                 (g1 , g2) = g' x
             in f1 ≡ g1 × f2 ≗ g2)

P6 : ( σ : Typ Pr ) → ( Is-ℝᵈ σ )
    → (τ : Typ Pr)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
P6 ρ isRd Un f f' = 
  -- f f' is equivalent to the corresponding (zero) functions
  P6≡ ρ isRd Un f f' (const tt) (const (tt , const (zerovDense (D2τ' ρ))))
P6 ρ isRd Inte f f' = {!   !}
P6 ρ isRd R f f' = 
  -- The first element of the tuple produced by f'
  -- is equivalent to f ...
  (∀ {x} → f x ≡ f' (primal ρ x) .fst) 
  -- ... and the second element of the tuple produced by f'
  -- is equivalent to the transposed derivative of f.
  × (∀ {x} → case DSemᵀ {ρ} {R} f x of
             maybe′ (λ dsem → f' (primal ρ x) .snd ≗ dsem) ⊤
    )
P6 ρ isRd (σ :* τ) f f' = 
  -- There eixsits some l l' and r r' ...
  Σ ((Rep ρ → Rep σ) × (Rep ρ → Rep τ)
      × (Rep (D1τ ρ) → ( Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
      × (Rep (D1τ ρ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' ρ)))))
  λ (l , r , l' , r' )
  -- ... that are in P6 ...
  → Σ (P6 ρ isRd σ l l' 
     × P6 ρ isRd τ r r')
  (λ _ → 
  -- ... and combined show that f f' is in P6.
    let h  = λ x → (l x , r x )
        h' = λ x → (l' x .fst , r' x .fst)
              , (λ where (just (ctgL , ctgR)) → plusvDense _ (l' x .snd ctgL) (r' x .snd ctgR)
                         nothing → zerovDense (D2τ' ρ))
    in P6≡ ρ isRd (σ :* τ) f f' h h'
  )
P6 ρ isRd (σ :+ τ) f f' = 
  -- There eixsits some l l' and r r' ...
  Σ ((Rep ρ → Rep σ) × (Rep ρ → Rep τ)
      × (Rep (D1τ ρ) → ( Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
      × (Rep (D1τ ρ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' ρ)))))
  λ (l , r , l' , r' )
  -- ... that are in P6 ...
  → Σ (P6 ρ isRd σ l l' × P6 ρ isRd τ r r')
  (λ _ → 
  -- and combined show that f f' is in P6.
    ∀ {x} → case (f x , f' (primal ρ x) ) of
        λ where (inj₁ a , inj₁ b , c) → 
                    a ≡ l x 
                  × b ≡ l' (primal ρ x) .fst 
                  × c ≗ λ where (just (inj₁ ctg)) → l' (primal ρ x) .snd ctg
                                _ → zerovDense (D2τ' ρ)
                (inj₂ a , inj₂ b , c) → {!   !}
                (inj₁ _ , inj₂ _ , _) → ⊥
                (inj₂ _ , inj₁ _ , _) → ⊥
  )
P6 ρ isRd (σ :-> τ) F F' = 
-- There exists some f f' ...  (Without EVM types)
  Σ ((Rep ρ → Rep σ → Rep τ)
    × (Rep (D1τ ρ) → (Rep (D1τ σ) → Rep (D1τ τ) × (Rep (D2τ τ) → Rep (Lin Dyn) × Rep (D2τ σ))) × (LinRep Dyn → LinRepDense (D2τ' ρ))))
  λ (f , f')
-- ... such that for all g g' ...
  → (g : Rep ρ → Rep σ) 
  → (g' : Rep (D1τ ρ) → (Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
-- ... where g g' is in P6 ...
  → P6 ρ isRd σ g g'
-- ... g g' applied to f f' is shown to be in P6 ... 
  → (let h  = λ x → f x (g x) 
         h' = λ x → let (f1 , f2) = f' x
                        (g1 , g2) = g' x
                        (h1 , h2) = f1 g1
                     in h1 , (λ y → let (d , z) = h2 y in plusvDense (D2τ' ρ) (f2 d) (g2 z))
     in P6 ρ isRd τ h h')
-- ... and f f' is equivalent to F F' .
-- [Note, this is not just extentional equality, but semantic equality of executing an EVM]
  × (∀ {x y} → f x y ≡ F x y .fst) 
  × (∀ {x y} → 
        let (f1 , f2) = f' x 
            (f3 , f4) = f1 y
            (F1 , F2) = F' x
            ((F3 , F4) , _) = F1 y
            F4' = λ ctg → let (a , b , _) = LACMexec (F4 ctg .fst) (nothing , ((zerov (D2τ' σ) .fst) , tt))
                          in a , b
        in f2 ≗ F2 × f3 ≡ F3 × f4 ≗ F4')

-- Nested and combined extensional equality
-- f is equivalent to g and f' is equivalent to g'
P7≡ : ( σ : Typ Pr ) → ( isRd : Is-ℝᵈ σ  ) → ( τ : Typ Pr )
    → (f : Rep σ → Rep τ)
    → (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (g : Rep σ → Rep τ)
    → (g' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
P7≡ _ _ _ f f' g g' = f ≗ g 
  × (∀ {x} → let (f1 , f2) = f' x
                 (g1 , g2) = g' x
             in f1 ≡ g1 × f2 ≗ g2)

P7 : ( σ : Typ Pr ) → ( Is-ℝᵈ σ )
    → (τ : Typ Pr)
    → (f : Rep σ → Rep τ)
    → (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
P7 ρ isRd Un f f' = 
  -- f f' is equivalent to the corresponding (zero) functions
  P7≡ ρ isRd Un f f' (const tt) (const (tt , const (zerovDense (D2τ' ρ))))
P7 ρ isRd Inte f f' = {!   !}
P7 ρ isRd R f f' =
  -- Forall possible inputs of f' ...
  ( x : Rep ρ ) → 
  -- ... the first element of the tuple produced by f'
  -- is equivalent to f ...
  (f x ≡ f' x .fst) 
--   -- ... and the second element of the tuple produced by f'
--   -- is equivalent to the transposed derivative of f.
  × ( case DSemᵀ {ρ} {R} f x of 
        maybe′ (λ dsem → f' x .snd ≗ dsem) 
               ⊤)
P7 ρ isRd (σ :* τ) f f' =
  -- There eixsits some l l' and r r' ...
  Σ ((Rep ρ → Rep σ) × (Rep ρ → Rep τ)
      × (Rep ρ → ( Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
      × (Rep ρ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' ρ)))))
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
P7 ρ isRd (σ :+ τ) f f' = 
  -- Depending on the branch taken by f, which much match that taken by the first element produced by f':
  (x : Rep ρ)
  → case f x , f' x of
     λ where
        (inj₁ a , inj₁ b , c) →
        -- BRANCH inj₁
        -- There exists some l l' ...
            Σ ((Rep ρ → Rep σ) 
            × (Rep ρ → ( Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))) 
            λ (l , l') → 
        -- ... that is in P7 ...
            Σ (P7 ρ isRd σ l l') 
            λ _ → 
        -- ... such that f f' is equivalent to l l' for this particular branch.
            a ≡ l x 
            × b ≡ l' x .fst 
            × ((ctg : Maybe (LinRep (D2τ' σ) ⊎ LinRep (D2τ' τ)))
                → case ctg of 
                  λ where (just (inj₁ ctg)) → c (just (inj₁ ctg)) ≡ l' x .snd ctg
                          (just (inj₂ ctg)) → ⊤ -- invalid input ctg, nothing to prove
                          nothing → c nothing ≡ l' x .snd (zerov (D2τ' σ) .fst))
        -- BRANCH INJ₂
        (inj₂ a , inj₂ b , c) →
          {!   !}
        -- UNMATCHED BRANCHES
        (inj₁ _ , inj₂ _ , _) → ⊥
        (inj₂ _ , inj₁ _ , _) → ⊥
P7 ρ isRd (σ :-> τ) F F' =
-- There exists some f f' ...  (Without EVM types)
  Σ ((Rep ρ → Rep σ → Rep τ)
    × (Rep ρ → (Rep (D1τ σ) → Rep (D1τ τ) × (Rep (D2τ τ) → Rep (Lin Dyn) × Rep (D2τ σ))) × (LinRep Dyn → LinRepDense (D2τ' ρ))))
  λ (f , f')
-- ... such that for all g g' ...
  → (g : Rep ρ → Rep σ) 
  → (g' : Rep ρ → (Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
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
  × ((x : Rep ρ) (y : Rep (D1τ σ)) → 
        let (f1 , f2) = f' x 
            (f3 , f4) = f1 y
            (F1 , F2) = F' x
            ((F3 , F4) , _) = F1 y
            F4' = λ ctg → let (a , b , _) = LACMexec (F4 ctg .fst) (nothing , ((zerov (D2τ' σ) .fst) , tt))
                          in a , b
        in f2 ≗ F2 × f3 ≡ F3 × f4 ≗ F4')


Fdsem : {σ τ : Typ Pr}
      → (f : Rep σ → Rep τ ) 
      → (Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
Fdsem {σ} {τ} f = λ x → primal τ (f x) , λ ctg → maybe′ (λ dsem → dsem (sparse2dense ctg)) (zerovDense (D2τ' σ)) (DSemᵀ {σ} {τ} f x)

dsemInP7 : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ)
            → (f : Rep σ → Rep τ ) 
            → P7 σ isRd τ f (Fdsem f)
dsemInP7 ρ Un isRd f = (λ x → refl) , refl , (λ y → ans)
  where ans : { x : Rep ρ } → { y : ⊤ } → Fdsem {ρ} {Un} f x .snd y ≡ const (tt , const (zerovDense (D2τ' ρ))) x .snd y
        ans {x} {tt} with DSemᵀ {ρ} {Un} f x
        ... | just d = {!   !} -- HOLDS (dsem-ctg-zero)
        ... | nothing = refl
dsemInP7 ρ Inte isRd f = {!   !}
dsemInP7 ρ R isRd f = λ x → refl , ans
  where ans : ∀ {x} → maybe′ (_≗_ (Fdsem {ρ} {R} f x .snd)) ⊤ (DSemᵀ {ρ} {R} f x)
        ans {x} with DSemᵀ {ρ} {R} f x
        ... | just d = λ _ → refl
        ... | nothing = tt
dsemInP7 ρ (σ :* τ) isRd f = 
  ( l , ( r , (l' , r'))) , ((pσ , pτ) , (λ x → refl) , (refl , (λ ctg → {!   !})))
  where l  = λ x → f x .fst
        r  = λ x → f x .snd
        l' = Fdsem l
        r' = Fdsem r
        pσ = dsemInP7 ρ σ isRd l
        pτ = dsemInP7 ρ τ isRd r
        h' = λ x → λ ctg → maybe′ (λ (ctgL , ctgR) → plusvDense _ (l' x .snd ctgL) (r' x .snd ctgR)) (zerovDense (D2τ' ρ)) ctg
        ans : {x : Rep ρ} → {ctg : Maybe (LinRep (D2τ' σ) × LinRep (D2τ' τ))} 
              → Fdsem {ρ} {σ :* τ} f x .snd ctg ≡ h' x ctg
        ans {x} {just ctg} 
          with DSemᵀ {ρ} {σ :* τ} f x
          with DSemᵀ {ρ} {σ} l x
          with DSemᵀ {ρ} {τ} r x
        ... | just d1 | just d2 | just d3 = {!   !} -- HOLDS (dsem-pair)
        ... | _ | _ | _ = {!   !} -- Outside of domain of definition
        ans {x} {nothing} = {!   !} -- HOLDS (dsem-ctg-zero)
dsemInP7 ρ (σ :+ τ) isRd f x 
  with f x | Fdsem {ρ} {σ :+ τ} f x | DSemᵀ {ρ} {σ :+ τ} f x
... | _ | _ | nothing = {!   !} -- Outside of domain of definition
... | inj₁ a | inj₁ b , c | just d = 
  (l , l') , pσ , (refl , (refl , ans))
  where l  = const a
        l' = Fdsem l
        pσ = dsemInP7 ρ σ isRd l
        ans : (ctg : Maybe (LinRep (D2τ' σ) ⊎ LinRep (D2τ' τ))) → _ 
        ans (just (inj₁ ctg))
          with (DSemᵀ {ρ} {σ} (λ _ → a) x)
        ... | just d2 = {!   !}
        ... | nothing  = {!  !}
        ans (just (inj₂ _)) = tt
        ans nothing = {!   !}
... | inj₂ a | inj₂ b , c | just d = {!   !}
... | inj₁ a | inj₂ b , c | just d = {!   !}
... | inj₂ a | inj₁ b , c | just d = {!   !}
dsemInP7 ρ (σ :-> τ) isRd F = 
  -- (f , f') , (λ g g' Pg → Pf g g' Pg , ( {! f∼F !} , f'∼F'))
  (f , f') , q1
  where f  = {!   !}
        f' = {!   !}
        q1 : (g : _) (g' : _) (Pg : _) → _
        q1 g g' Pg = {! dsemInP7 ρ τ isRd ?   !} , {!   !}

        -- Pf : (g : _) → (g' : _) → (Pg : _) →  P7 ρ isRd τ (λ x → f x (g x)) _
        -- Pf = {! (g : _) → (g' : _) → (Pg : _) →  P7 ρ isRd τ (λ x → f x (g x)) _ !}
        -- f∼F = {!   !}
        -- f'∼F' = {!  !}



interp-chad : {Γ : Env Pr} {τ : Typ Pr} 
                  (t : Term Pr Γ τ)
                  (a : Val Pr Γ)
                  (evIn : LEtup (map D2τ' Γ) ) -- incoming LEtup
                → (ctg : LinRep (D2τ' τ))
                → (Rep (D1τ τ) × LEtup (map D2τ' Γ) )
interp-chad t a evIn ctg = let (x , y) = interp (chad t) (primalVal a)
                        in x , LACMexec (y ctg .fst) evIn