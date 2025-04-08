module correctness.HO-chad-correct where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)

open import Data.Empty using (⊥)
open import Data.List using (_∷_; map; [])
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_]; isInj₁; isInj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; _>>=_)
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
        λ where nothing     → ⊤
                (just dsem) → f' (primal ρ x) .snd ≗ dsem
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

-- P6 ρ isRd R f f' = 
  -- -- The first element of the tuple produced by f'
  -- -- is equivalent to f ...
  -- (∀ {x} → f x ≡ f' (primal ρ x) .fst) 
  -- -- ... and for all inputs within the domain of definition ...
  -- × (∀ {x} 
  --      → let dod = {!   !} in dod x 
  -- -- (... whereby the domain of definition implies that dsem is defined ...)
  --      → let dsem = {!   !}
  -- -- ... the second element of the tuple produced by f'
  -- -- is equivalent to the transposed derivative of f.
  --      in f' x .snd ≗ (to-witness dsem) x)

P5-dual≡ : ( σ : Typ Pr ) → ( isRd : Is-ℝᵈ σ  ) → ( τ : Typ Pr )
    → (f : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (g : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
P5-dual≡ _ _ _ f g = 
  ∀ {x} → let (f1 , f2) = f x
              (g1 , g2) = g x
          in f1 ≡ g1 × f2 ≗ g2

P5-fst : {ρ σ τ : Typ Pr}
        → (Rep (D1τ ρ) →
            (Rep (D1τ σ) × Rep (D1τ τ)) ×
            (Maybe (LinRep (D2τ' σ) × LinRep (D2τ' τ)) → LinRepDense (D2τ' ρ)))
        → (Rep (D1τ ρ) → Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ)))
P5-fst f = {!   !}
  -- λ x → let ((a , _) , g) = f x
                --  in a , λ y → g (just (y , (zerov _ .fst)))

P5-snd : {ρ σ τ : Typ Pr}
        → (Rep (D1τ ρ) →
            (Rep (D1τ σ) × Rep (D1τ τ)) ×
            (Maybe (LinRep (D2τ' σ) × LinRep (D2τ' τ)) → LinRepDense (D2τ' ρ)))
        → (Rep (D1τ ρ) → Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' ρ)))
P5-snd f = {!   !}

P5-inj₁ : {ρ σ τ : Typ Pr}
    → Rep (D1τ ρ) →
          (Rep (D1τ σ) ⊎ Rep (D1τ τ)) ×
          (Maybe (LinRep (D2τ' σ) ⊎ LinRep (D2τ' τ)) → LinRepDense (D2τ' ρ))
    → Rep (D1τ ρ) →
          Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))
P5-inj₁ f = {!   !}
  -- λ x → let ((_ , b) , g) = f x
                --  in b , λ y → g (just ((zerov _ .fst) , y))


P5 : ( σ : Typ Pr ) → ( Is-ℝᵈ σ )
    → (τ : Typ Pr)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
P5 ρ isRd Un f f' =
    f ≗ const tt 
  × P5-dual≡ ρ isRd Un f' (const (tt , const (zerovDense (D2τ' ρ))))
P5 ρ isRd Inte f f' = {!   !}
P5 ρ isRd R f f' = {!    !}
P5 ρ isRd (σ :* τ) f f' =
  let l  = fst ∘ f
      l' = P5-fst f'
      r  = snd ∘ f
      r' = P5-snd f'
  in Σ (P5 ρ isRd σ l l' × P5 ρ isRd τ r r') 
    (λ (Pσ , Pτ) 
    → f ≗ (λ x → l x , r x) 
    × (∀ {x} → let g  = (l' x .fst , r' x .fst)
                   g' = λ where (just (ctgL , ctgR)) → plusvDense _ (l' x .snd ctgL) (r' x .snd ctgR)
                                nothing → zerovDense _
       in (f' x .fst ≡ g) × (f' x .snd ≗ g')))
P5 ρ isRd (σ :+ τ) f f' = 
  ∀ {a} → case f a , f' (primal ρ a) 
  of λ where 
    (inj₁ a' , inj₁ b₁ , b₂) →
      let l  = const a'
          l' = const (b₁ , λ ctg → b₂ (just (inj₁ ctg)))
      in (P5 ρ isRd σ l l')
    (inj₂ a' , inj₂ x , g) → {!   !}
      -- let r  = const a'
          -- r' = {! con  !}
      -- in (P5 ρ isRd τ r r')
    (inj₁ _  , inj₂ _ , _) → ⊥
    (inj₂ _  , inj₁ _ , _) → ⊥
P5 ρ isRd (σ :-> τ) f f' = {!   !}


interp-chad : {Γ : Env Pr} {τ : Typ Pr} 
                  (t : Term Pr Γ τ)
                  (a : Val Pr Γ)
                  (evIn : LEtup (map D2τ' Γ) ) -- incoming LEtup
                → (ctg : LinRep (D2τ' τ))
                → (Rep (D1τ τ) × LEtup (map D2τ' Γ) )
interp-chad t a evIn ctg = let (x , y) = interp (chad t) (primalVal a)
                        in x , LACMexec (y ctg .fst) evIn

-- chad∈P : {Γ : Env Pr} {τ : Typ Pr} 
--                   → let σ  = Etup Pr Γ 
--                         LΓ = map D2τ' Γ in
--                   (a : Rep σ) -- input of function
--                   (evIn : LEtup LΓ ) -- incoming LEtup
--                   (ctg : LinRep (D2τ' τ)) -- incoming cotangent
--                   (t : Term Pr Γ τ) -- primal function
--                 → ctg  ≃τ (interp t (Etup-to-val a)) -- compatible incoming cotangent
--                 → evIn ≃Γ Etup-to-val a -- compatible incoming LEtup
--                 → (∃-dsyn : DSyn-Exists (Etup-to-val a) t) -- function is differentiable at input
--                 → let dsem = DSyn-Exists→DSem-Exists a t ∃-dsyn 
--                 in P τ (interp t) (interp-chad t) (Etup-to-val  a) evIn ctg 
-- chad∈P {Γ} {τ} a evIn ctg t ~τ ~Γ dsyn = {! interp (chad t) (Etup-to-val-primal a)  !}

-- P→Dsem : {Γ : Env Pr} ( τ : Typ Pr ) 
--                   → let σ  = Etup Pr Γ 
--                         LΓ = map D2τ' Γ in
--                   (a : Rep σ) -- input of function
--                   (evIn : LEtup LΓ ) -- incoming LEtup
--                   (ctg : LinRep (D2τ' τ)) -- incoming cotangent
--                   (t : Term Pr Γ τ) -- primal function
--                 → (∃-dsyn : DSyn-Exists (Etup-to-val a) t) 
--                 → let f = interp t
--                       f' = interp-chad t
--                       dsem = DSyn-Exists→DSem-Exists a t ∃-dsyn
--                 in P {Γ} τ f f' (Etup-to-val a) evIn ctg
--                   → LEtup2EV {LΓ} (f' (Etup-to-val a) evIn ctg .snd) 
--                     ≡ (Etup2EV {Γ} (to-witness dsem (sparse2dense ctg))) ev+ LEtup2EV {LΓ} evIn  
-- P→Dsem Un a evIn ctg t (∃dsyn dsyn) (_ , p)
--   rewrite cong snd p
--   = DSemᵀ-ev-lemma-ctg-zero-evIn' (∃DSyn→∃DSem a t dsyn)
-- P→Dsem Inte a evIn ctg t (∃dsyn dsyn) q = {!   !}
-- P→Dsem R a evIn ctg t (∃dsyn dsyn) q = {!   !}
-- P→Dsem (σ :* τ) a evIn nothing t (∃dsyn dsyn) q = {!   !}
-- P→Dsem (σ :* τ) a evIn (just (ctgL , ctgR)) t (∃dsyn dsyn) (((g₁ , g'₁) , g₂ , g'₂) , (Pσ , Pτ) , pg , p1 , p2)
--   rewrite p2
--   = let foo = {! P→Dsem σ a evIn ctgL g'₁   !}
--         in {!   !}
-- P→Dsem (σ :+ τ) a evIn ctg t (∃dsyn dsyn) q = {!   !}
-- P→Dsem (σ :-> τ) a evIn ctg t (∃dsyn dsyn) q = {!   !}

-- HO-chad-equiv-DSemᵀ : {Γ : Env Pr} {τ : Typ Pr} 
--                   → let σ  = Etup Pr Γ 
--                         LΓ = map D2τ' Γ in
--                   (a : Rep σ) -- input of function
--                   (evIn : LEtup LΓ ) -- incoming LEtup
--                   (ctg : LinRep (D2τ' τ)) -- incoming cotangent
--                   (t : Term Pr Γ τ) -- primal function
--                 → ctg  ≃τ (interp t (Etup-to-val a)) -- compatible incoming cotangent
--                 → evIn ≃Γ Etup-to-val a -- compatible incoming LEtup
--                 → (∃-dsyn : DSyn-Exists (Etup-to-val a) t) -- function is differentiable at input
--                 → let dsem = DSyn-Exists→DSem-Exists a t ∃-dsyn
--                 in LEtup2EV {LΓ} (interp-chad t (Etup-to-val a) evIn ctg .snd)
--                   ≡ Etup2EV {Γ} ( to-witness dsem (sparse2dense ctg)) ev+ LEtup2EV {LΓ} evIn
-- HO-chad-equiv-DSemᵀ {Γ} {τ} a evIn ctg t ~τ ~Γ dsyn
--   with chad∈P a evIn ctg t ~τ ~Γ dsyn       
-- ... | q = {!   !} -- P→Dsem τ a evIn ctg t dsyn q