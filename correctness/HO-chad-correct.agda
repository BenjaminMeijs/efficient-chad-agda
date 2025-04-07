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

Is-ℝᵈ : ( τ : Typ Pr ) → Set
Is-ℝᵈ Un = ⊤
Is-ℝᵈ Inte = ⊥
Is-ℝᵈ R = ⊤
Is-ℝᵈ (σ :* τ) = Is-ℝᵈ σ × Is-ℝᵈ τ
Is-ℝᵈ (σ :+ τ) = ⊥
Is-ℝᵈ (σ :-> τ) = ⊥

Is-ℝᵈΓ : (Γ : Env Pr) → Set
Is-ℝᵈΓ [] = ⊤  
Is-ℝᵈΓ (τ ∷ Γ) = Is-ℝᵈ τ

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
    × P5-dual≡ ρ isRd (σ :* τ) f' 
        (λ x → (l' x .fst , r' x .fst) 
        , (λ where (just (ctgL , ctgR)) → plusvDense _ (l' x .snd ctgL) (r' x .snd ctgR)
                   nothing → plusvDense _ (l' x .snd (zerov _ .fst)) (r' x . snd (zerov _ .fst)))))
P5 ρ isRd (σ :+ τ) f f' = 
  ∀ {a} → case f a of 
    [ (λ a' → let l  = {! f !}
                  l' = {! f'  !}
        in Σ (P5 ρ isRd σ l l') 
          (λ _ → (a' ≡ l a) × {! l    !}))
    , (λ a' → {! Sigma  !}) ]
P5 ρ isRd (σ :-> τ) f f' = {!   !}

-- P5' ρ isRd Un f f' (a , b) = {!   !}
-- P5' ρ isRd Inte f f' p = {!   !}
-- P5' ρ isRd R f f' p = {!   !}
-- P5' ρ isRd (σ :* τ) f f' p = {!   !}
-- P5' ρ isRd (σ :+ τ) f f' p = {!   !}
-- P5' ρ isRd (σ :-> τ) f f' p = {!   !}

P4-Primal : {σ : Typ Pr} → {σ-is-Rd : Is-ℝᵈ σ}
    → (τ : Typ Pr)
    → (f : Rep σ → Rep τ)
    → (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (a : Rep σ)
    → Rep τ
P4-Primal Un f f' a = tt
P4-Primal Inte f f' a = {!   !}
P4-Primal R f f' a = {!   !}
P4-Primal (σ :* τ) f f' a = (fst (f a)) , (snd (f a))
P4-Primal (σ :+ τ) f f' a = {!   !}
P4-Primal (σ :-> τ) f f' a = {!   !}

P4-Dual : {σ : Typ Pr} → {σ-is-Rd : Is-ℝᵈ σ}
    → (τ : Typ Pr)
    → (f : Rep σ → Rep τ)
    → (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (a : Rep σ)
    → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ)))
P4-Dual Un f f' a = tt , (const (zerovDense _))
P4-Dual Inte f f' a = {!   !}
P4-Dual R f f' a = {!   !}
P4-Dual {ρ} {q} (σ :* τ) f f' a = {!   !}
P4-Dual (σ :+ τ) f f' a = {!   !}
P4-Dual (σ :-> τ) f f' a = {!   !}

-- P4Primal≡ : {σ τ : Typ Pr} → {σ-is-Rd : Is-ℝᵈ σ}
--           → (f : Rep σ → Rep τ)
--             (g : Rep σ → Rep τ)
--           → Set
-- P4Primal≡ f g = ?


P4dual≡ : {σ τ : Typ Pr} → {σ-is-Rd : Is-ℝᵈ σ}
          → (f : Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ)))
            (g : Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ)))
          → Set
P4dual≡ (f₁ , f₂) (g₁ , g₂) = f₁ ≡ g₁ × f₂ ≗ g₂

P4 : {σ : Typ Pr} → {σ-is-Rd : Is-ℝᵈ σ}
    → (τ : Typ Pr)
    → (f : Rep σ → Rep τ)
    → (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (a : Rep σ)
    →  Σ {! P4Cond  !} {!   !}
    -- (  (f ≗ (P4-Primal {σ} {σ-is-Rd} τ f f' a)) 
    -- × (P4dual≡ {σ} {τ} {σ-is-Rd} (f' a) (P4-Dual {σ} {σ-is-Rd} τ f f' a)))
    → Set
P4  τ f f' a w = ⊤

P3-fst : {ρ σ τ : Typ Pr}
        → (Rep ρ →
            (Rep (D1τ σ) × Rep (D1τ τ)) ×
            (Maybe (LinRep (D2τ' σ) × LinRep (D2τ' τ)) → LinRepDense (D2τ' ρ)))
        → (Rep ρ → Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ)))
P3-fst f = λ x → let ((a , _) , g) = f x
                 in a , λ y → g (just (y , (zerov _ .fst)))

P3-snd : {ρ σ τ : Typ Pr}
        → (Rep ρ →
            (Rep (D1τ σ) × Rep (D1τ τ)) ×
            (Maybe (LinRep (D2τ' σ) × LinRep (D2τ' τ)) → LinRepDense (D2τ' ρ)))
        → (Rep ρ → Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' ρ)))
P3-snd f = λ x → let ((_ , b) , g) = f x
                 in b , λ y → g (just ((zerov _ .fst) , y))


P3 : {σ : Typ Pr} → {Is-ℝᵈ σ}
    → (τ : Typ Pr)
    → (f : Rep σ → Rep τ)
    → (a : Rep σ)
    → (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set

P3-extract : { σ : Typ Pr } → { isR : Is-ℝᵈ σ  } → { τ : Typ Pr } → { f : Rep σ → Rep τ } → { a : Rep σ } → { f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))) }
            → P3 {σ} {isR} τ f a f'
            → (Rep τ) × (Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ)))

P3 Un f a f' = f a ≡ tt × f' a ≡ (tt , (const (zerovDense _)))
P3 Inte f a f' = {!   !}
P3 R f a f' = {!   !}
P3 {ρ} {ρR} (σ :* τ) f a f' =
    Σ (P3 {ρ} {ρR} σ (fst ∘ f) a (P3-fst f') × P3 {ρ} {ρR} τ (snd ∘ f) a (P3-snd f'))
    λ (pL , pR) → let (l , (l1' , l2')) = P3-extract {ρ} {ρR} {σ} {fst ∘ f} {a} {P3-fst f'} pL 
                      (r , (r1' , r2')) = P3-extract {ρ} {ρR} {τ} {snd ∘ f} {a} {P3-snd f'} pR
                  in (f a ≡ (l , r  )) 
                    × P4dual≡ {ρ} {σ :* τ} {ρR} (f' a) 
                        ((l1' , r1') ,
                         λ v → l2' {! v   !})
P3 (σ :+ τ) f a f' = {!   !}
P3 (σ :-> τ) f a f' = {!   !}

P3-extract {ρ} {isR} {Un} {f} {a} {f'} (fst₁ , snd₁) = {!   !}
P3-extract {ρ} {isR} {Inte} {f} {a} {f'} p = {!   !}
P3-extract {ρ} {isR} {R} {f} {a} {f'} p = {!   !}
P3-extract {ρ} {isR} {τ :* τ₁} {f} {a} {f'} p = {!   !}
P3-extract {ρ} {isR} {τ :+ τ₁} {f} {a} {f'} p = {!   !}
P3-extract {ρ} {isR} {τ :-> τ₁} {f} {a} {f'} p = {!   !}

-- P2 : {σ : Typ Pr} → {Is-ℝᵈ σ}
--     → (τ : Typ Pr)
--     → (f : Rep σ → Rep τ)
--       (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
--     → Set
-- P2 Un f f' = f ≗ const tt 
--           × f' ≗ const (tt , (const (zerovDense _)))
-- P2 Inte f f' = {! ⊤  !}
-- P2 R f f' = {!   !}
-- P2 (σ :* τ) f f' = Σ (P2 σ (fst ∘ f) (λ x → {! f' x   !}) × {!   !}) 
--               {!   !}

--             --  f ≗ (λ x → (fst (f x)) , (snd (f x)))
--                 --  × f' ≗ (λ x → ({!   !} , {!   !}) , λ x → {!   !})
-- P2 (σ :+ τ) f f' = {!   !}
-- P2 (σ :-> τ) f f' = {!   !}

P : {Γ : Env Pr} → ( τ : Typ Pr )
    → (f : Val Pr Γ → Rep τ)
    → (f' : Val Pr Γ → LEtup (map D2τ' Γ) → LinRep (D2τ' τ) → (Rep (D1τ τ) × (LEtup (map D2τ' Γ))))
    → (a : Val Pr Γ)
    → (evIn : LEtup (map D2τ' Γ))
    → (ctg : LinRep (D2τ' τ))
    → Set
P Un f f' a evIn ctg   = f a ≡ tt × f' a evIn ctg ≡ (tt , evIn)
-- Question: Wat zouden deze twee moeten zijn?
P Inte f f' a evIn ctg = ⊤
P R f f' a evIn ctg    = ⊤
P {Γ} (σ :* τ) f f' a evIn nothing  = {!   !}
P {Γ} (σ :* τ) f f' a evIn (just (ctgL , ctgR))  = 
  -- Preconditions / assumptions
  Σ (((Val Pr Γ → Rep σ) × (Val Pr Γ → LEtup (map D2τ' Γ) → LinRep (D2τ' σ) → (Rep (D1τ σ) × (LEtup (map D2τ' Γ)))))
   × ((Val Pr Γ → Rep τ) × (Val Pr Γ → LEtup (map D2τ' Γ) → LinRep (D2τ' τ) → Rep (D1τ τ) × LEtup (map D2τ' Γ))))
  λ ((g₁ , g'₁) , (g₂ , g'₂)) → Σ (P σ g₁ g'₁ a evIn ctgL × P τ g₂ g'₂ a evIn ctgR)
  λ (Pσ , Pτ) → 
  -- Postconditions / proof goal
      f a ≡ ((g₁ a) , (g₂ a))
      × (let res = (f' a evIn (just (ctgL , ctgR)))
         in (fst res ≡ (g'₁ a evIn ctgL .fst ,  g'₂ a evIn ctgR .fst))
           × LEtup2EV (snd res) ≡ ((LEtup2EV (g'₁ a evIn ctgL .snd) ev+ LEtup2EV (g'₂ a evIn ctgR .snd)) ev+ LEtup2EV evIn))
P (σ :+ τ) f f' a evIn ctg  = {!   !}
P (σ :-> τ) f f' a evIn ctg = {!   !}

interp-chad : {Γ : Env Pr} {τ : Typ Pr} 
                  (t : Term Pr Γ τ)
                  (a : Val Pr Γ)
                  (evIn : LEtup (map D2τ' Γ) ) -- incoming LEtup
                → (ctg : LinRep (D2τ' τ))
                → (Rep (D1τ τ) × LEtup (map D2τ' Γ) )
interp-chad t a evIn ctg = let (x , y) = interp (chad t) (primalVal a)
                        in x , LACMexec (y ctg .fst) evIn
  -- let (x , y) = interp (chad t) (primalVal a)
                    -- in x , λ ctg → LACMexec (fst (y ctg)) evIn

chad∈P : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep σ) -- input of function
                  (evIn : LEtup LΓ ) -- incoming LEtup
                  (ctg : LinRep (D2τ' τ)) -- incoming cotangent
                  (t : Term Pr Γ τ) -- primal function
                → ctg  ≃τ (interp t (Etup-to-val a)) -- compatible incoming cotangent
                → evIn ≃Γ Etup-to-val a -- compatible incoming LEtup
                → (∃-dsyn : DSyn-Exists (Etup-to-val a) t) -- function is differentiable at input
                → let dsem = DSyn-Exists→DSem-Exists a t ∃-dsyn 
                in P τ (interp t) (interp-chad t) (Etup-to-val  a) evIn ctg 
chad∈P {Γ} {τ} a evIn ctg t ~τ ~Γ dsyn = {! interp (chad t) (Etup-to-val-primal a)  !}

P→Dsem : {Γ : Env Pr} ( τ : Typ Pr ) 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep σ) -- input of function
                  (evIn : LEtup LΓ ) -- incoming LEtup
                  (ctg : LinRep (D2τ' τ)) -- incoming cotangent
                  (t : Term Pr Γ τ) -- primal function
                → (∃-dsyn : DSyn-Exists (Etup-to-val a) t) 
                → let f = interp t
                      f' = interp-chad t
                      dsem = DSyn-Exists→DSem-Exists a t ∃-dsyn
                in P {Γ} τ f f' (Etup-to-val a) evIn ctg
                  → LEtup2EV {LΓ} (f' (Etup-to-val a) evIn ctg .snd) 
                    ≡ (Etup2EV {Γ} (to-witness dsem (sparse2dense ctg))) ev+ LEtup2EV {LΓ} evIn  
P→Dsem Un a evIn ctg t (∃dsyn dsyn) (_ , p)
  rewrite cong snd p
  = DSemᵀ-ev-lemma-ctg-zero-evIn' (∃DSyn→∃DSem a t dsyn)
P→Dsem Inte a evIn ctg t (∃dsyn dsyn) q = {!   !}
P→Dsem R a evIn ctg t (∃dsyn dsyn) q = {!   !}
P→Dsem (σ :* τ) a evIn nothing t (∃dsyn dsyn) q = {!   !}
P→Dsem (σ :* τ) a evIn (just (ctgL , ctgR)) t (∃dsyn dsyn) (((g₁ , g'₁) , g₂ , g'₂) , (Pσ , Pτ) , pg , p1 , p2)
  rewrite p2
  = let foo = {! P→Dsem σ a evIn ctgL g'₁   !}
        in {!   !}
P→Dsem (σ :+ τ) a evIn ctg t (∃dsyn dsyn) q = {!   !}
P→Dsem (σ :-> τ) a evIn ctg t (∃dsyn dsyn) q = {!   !}

HO-chad-equiv-DSemᵀ : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep σ) -- input of function
                  (evIn : LEtup LΓ ) -- incoming LEtup
                  (ctg : LinRep (D2τ' τ)) -- incoming cotangent
                  (t : Term Pr Γ τ) -- primal function
                → ctg  ≃τ (interp t (Etup-to-val a)) -- compatible incoming cotangent
                → evIn ≃Γ Etup-to-val a -- compatible incoming LEtup
                → (∃-dsyn : DSyn-Exists (Etup-to-val a) t) -- function is differentiable at input
                → let dsem = DSyn-Exists→DSem-Exists a t ∃-dsyn
                in LEtup2EV {LΓ} (interp-chad t (Etup-to-val a) evIn ctg .snd)
                  ≡ Etup2EV {Γ} ( to-witness dsem (sparse2dense ctg)) ev+ LEtup2EV {LΓ} evIn
HO-chad-equiv-DSemᵀ {Γ} {τ} a evIn ctg t ~τ ~Γ dsyn
  with chad∈P a evIn ctg t ~τ ~Γ dsyn   
... | q = {!   !} -- P→Dsem τ a evIn ctg t dsyn q