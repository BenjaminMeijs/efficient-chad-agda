module correctness.dsem where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)
open import Function.Base using (id; _∘_; _$_; flip; case_of_)
open import Data.Product.Base using (uncurry; _×_)
open import Agda.Builtin.Float using (primFloatPlus; primFloatTimes; primFloatNegate)

open import spec using (Typ; Pr; Env; Rep; D2τ' ; _:*_; _:+_; R; valprj)
open import spec.linear-types using (Idx; S; Z)

open import correctness.spec using (LinRepDense; zerovDense; plusvDense; Etup; Etup-to-val)

onehot : {Γ : Env Pr} {τ : Typ Pr}
        → (idx : Idx Γ τ)
        → (x : LinRepDense (D2τ' τ))
        → LinRepDense (D2τ' (Etup Pr Γ))
onehot {ρ ∷ Γ} {τ} Z       x = x , zerovDense _
onehot {ρ ∷ Γ} {τ} (S idx) x = zerovDense _ , onehot idx x

WitnessInj₁ : {A : Set} {B : Set} → A ⊎ B → Set
WitnessInj₁ (inj₁ _) = ⊤
WitnessInj₁ (inj₂ _) = ⊥

WitnessInj₂ : {A : Set} {B : Set} → A ⊎ B → Set
WitnessInj₂ (inj₁ _) = ⊥
WitnessInj₂ (inj₂ _) = ⊤

postulate
    -- ======================
    -- Definition
    -- ======================
    DSemᵀ :  {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep σ) 
            → (ctg : LinRepDense (D2τ' τ))
            → LinRepDense (D2τ' σ)

    -- ======================
    -- Misc. rules
    -- ======================
    DSemᵀ-ctg-zero : {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep σ)
            → DSemᵀ {σ} {τ} f a (zerovDense (D2τ' τ)) ≡ zerovDense (D2τ' σ)

    DSemᵀ-chain : {τ1 τ2 τ3 : Typ Pr}
                → (f : Rep τ2 → Rep τ3)
                → (g : Rep τ1 → Rep τ2)
                → (a : Rep τ1)
                → (ctg : LinRepDense (D2τ' τ3))
                → DSemᵀ {τ1} {τ3} (f ∘ g) a ctg
                  ≡ DSemᵀ {τ1} {τ2} g a (DSemᵀ {τ2} {τ3} f (g a) ctg)

    DSemᵀ-pair : {σ τ1 τ2 : Typ Pr}
            → (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → (a : Rep σ)
            → (ctg-f : LinRepDense (D2τ' τ1))
            → (ctg-g : LinRepDense (D2τ' τ2))
            → let dsem-f = DSemᵀ {σ} {τ1} f a ctg-f
                  dsem-g = DSemᵀ {σ} {τ2} g a ctg-g
                  h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
                  ctg : LinRepDense (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
              in DSemᵀ {σ} {τ1 :* τ2} h a ctg
                 ≡ plusvDense (D2τ' σ) dsem-f dsem-g

    DSemᵀ-var : {Γ : Env Pr} {τ : Typ Pr}
              → let σ = Etup Pr Γ
              in (a : Rep σ)
              → (idx : Idx Γ τ)
              → (ctg : LinRepDense (D2τ' τ))
              → DSemᵀ {σ} {τ} (flip valprj idx ∘ Etup-to-val) a ctg
                ≡ onehot idx ctg

--     DSemᵀ-case : {σ1 σ2 τ : Typ Pr}
--               → (a : Rep (σ1 :+ σ2))
--               → (f : Rep σ1 →  Rep τ) 
--               → (g : Rep σ2 →  Rep τ) 
--               → (ctg : LinRepDense (D2τ' τ))
--               → let h : Rep (σ1 :+ σ2) → Rep τ
--                     h = match-inj σ1 σ2 
--                             (λ x → f x)
--                             (λ y → g y)
--                     k : Rep (σ1 :+ σ2) → LinRepDense (D2τ' σ1) × LinRepDense (D2τ' σ2)
--                     k = match-inj σ1 σ2
--                             (λ x → (DSemᵀ {σ1} {τ} f x ctg) , (zerovDense (D2τ' σ2)))
--                             (λ y → (zerovDense (D2τ' σ1)) , (DSemᵀ {σ2} {τ} g y ctg))
--                 in DSemᵀ {σ1 :+ σ2} {τ} h a ctg
--                    ≡ k a

--     DSemᵀ-case2 : {σ ρ1 ρ2 τ : Typ Pr}
--               → (a : Rep σ)
--               → (cond : Rep σ → Rep (ρ1 :+ ρ2)) 
--               → (l : Rep σ → Rep ρ1 →  Rep τ) 
--               → (r : Rep σ → Rep ρ2 →  Rep τ) 
--               → (ctg : LinRepDense (D2τ' τ))
--               → let h : Rep σ → Rep τ
--                     h = λ a' → [ (l a') , (r a') ] (cond a')
--                     k : Rep (ρ1 :+ ρ2) → LinRepDense (D2τ' σ)
--                     k = λ a' → {!   !}
--                 in DSemᵀ {σ} {τ} h a ctg
--                    ≡ k (cond a)
--     DSemᵀ-case3 : {σ ρ1 ρ2 τ : Typ Pr}
--               → (a : Rep σ)
--               → (cond : Rep σ → Rep (ρ1 :+ ρ2)) 
--               → (l : Rep σ → Rep ρ1 →  Rep τ) 
--               → (r : Rep σ → Rep ρ2 →  Rep τ) 
--               → (ctg : LinRepDense (D2τ' τ))
--               → let h : Rep σ → Rep τ
--                     h = λ b → [ (l b) , (r b) ] (cond b)
--                     k : {!   !} -- Rep (ρ1 :+ ρ2) → LinRepDense (D2τ' σ)
--                     k = {!   !}  -- [ (λ v → DSemᵀ {σ} {τ} (flip l $ v) a ctg) 
--                           -- , {! λ v → DSemᵀ {σ} {?} ? a  !} ]
--                     foo : LinRepDense (D2τ' σ)
--                     foo = [ (λ v → DSemᵀ {σ} {τ} (λ b → l b v) a ctg) 
--                           , {!   !} ] (cond a)
--                 in DSemᵀ {σ} {τ} h a ctg
--                    ≡ [ {! DSemᵀ {σ} {τ} ? a ctg  !} 
--                      , {!   !} 
--                      ] (cond a)

    -- DSemᵀ-case4 : {ρ1 ρ2 π τ : Typ Pr} →
    --           let σ = (ρ1 :+ ρ2) :* π
    --           in (a : Rep σ)
    --           → (l : Rep (ρ1 :* π) → Rep τ) 
    --           → (r : Rep (ρ2 :* π) → Rep τ) 
    --           → (ctg : LinRepDense (D2τ' τ))
    --           → let h : Rep σ → Rep τ
    --                 h = λ where (inj₁ x , y) → l (x , y)
    --                             (inj₂ x , y) → r (x , y)
    --             in
    --             [ {!   !} 
    --             , (λ v → DSemᵀ {σ} {τ} h a ctg ≡ ?
    --             ] (a .fst)
              
              -- let h : Rep σ → Rep τ
              --       h = λ where (inj₁ x , y) → l (x , y)
              --                   (inj₂ x , y) → r (x , y)
              --   in DSemᵀ {σ} {τ} h a ctg
              --     ≡ [ (λ v → {! DSemᵀ {ρ1 :* π} {?} l    !}) -- (λ v → ({! DSemᵀ {ρ1} {?}   !} , (zerovDense (D2τ' ρ2))) , {!   !}) 
              --       , {!   !} 
              --       ] (a .fst)
        -- DSemᵀ {σ} {τ} h a ctg
          --         ≡ DSemᵀ {σ} {{!   !}} cond a foo 

--     DSemᵀ-case6 : {σ ρ1 ρ2 τ : Typ Pr}
--               → (a : Rep σ)
--               → (cond : Rep σ → Rep (ρ1 :+ ρ2)) 
--               → (l : Rep ρ1 → Rep σ →  Rep τ) 
--               → (r : Rep ρ2 → Rep σ →  Rep τ) 
--               → (ctg : LinRepDense (D2τ' τ))
--               → let h : Rep σ → Rep τ
--                     h = λ b → [ (flip l $ b) , (flip r $ b) ] (cond b)
--                 in [ (λ v → DSemᵀ {σ} {τ} h a ctg ≡ DSemᵀ {σ} {τ} (l v) a ctg)
--                    , (λ v → DSemᵀ {σ} {τ} h a ctg ≡ DSemᵀ {σ} {τ} (r v) a ctg)
--                    ] (cond a)

--     DSemᵀ-case7 : {σ ρ1 ρ2 τ : Typ Pr}
--               → (a : Rep σ)
--               → (cond : Rep σ → Rep (ρ1 :+ ρ2)) 
--               → (f : Rep σ →  Rep τ) 
--               → (g : Rep σ →  Rep τ) 
--               → (ctg : LinRepDense (D2τ' τ))
--               →   [ (λ _ → ( (x : Rep σ) → (WitnessInj₁ $ cond x) → f x ≡ g x )
--                              → (DSemᵀ {σ} {τ} f a ctg ≡ DSemᵀ {σ} {τ} g a ctg))
--                   , (λ _ → ((x : Rep σ) → (WitnessInj₂ $ cond x) → f x ≡ g x)
--                              → (DSemᵀ {σ} {τ} f a ctg ≡ DSemᵀ {σ} {τ} g a ctg))
--                   ] (cond a)

    DSemᵀ-case8 : {σ1 σ2 ρ τ : Typ Pr}
              → (a : Rep ((σ1 :+ σ2) :* ρ))
              → (l : Rep (σ1 :* ρ) → Rep τ) 
              → (r : Rep (σ2 :* ρ) → Rep τ) 
              → (ctg : LinRepDense (D2τ' τ))
              → let f : (Rep ((σ1 :+ σ2) :* ρ) ) → Rep τ
                    f = λ (xs , a') → [ (λ x → l (x , a'))
                                      , (λ x → r (x , a'))
                                     ] xs
              in  [ (λ v → let dsem-l = DSemᵀ {σ1 :* ρ} {τ} l (v , snd a) ctg
                             in DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a ctg 
                                ≡  ( (dsem-l .fst , zerovDense (D2τ' σ2)) , dsem-l .snd)  )
                  , (λ v → let dsem-r = DSemᵀ {σ2 :* ρ} {τ} r (v , snd a) ctg
                             in DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a ctg 
                                ≡  ( (zerovDense (D2τ' σ1) , dsem-r .fst) , dsem-r .snd)  )
                  ] (a .fst)

    DSemᵀ-case0 : {σ1 σ2 τ : Typ Pr}
              → (a : Rep (σ1 :+ σ2))
              → (f : Rep σ1 →  Rep τ) 
              → (g : Rep σ2 →  Rep τ) 
              → (ctg : LinRepDense (D2τ' τ))
              → let h : Rep (σ1 :+ σ2) → Rep τ
                    h = [ f , g ]
                    k : Rep (σ1 :+ σ2) → LinRepDense (D2τ' σ1) × LinRepDense (D2τ' σ2)
                    k = [ (λ x → (DSemᵀ {σ1} {τ} f x ctg) , (zerovDense (D2τ' σ2)))
                        , (λ y → (zerovDense (D2τ' σ1)) , (DSemᵀ {σ2} {τ} g y ctg)) ]
                in DSemᵀ {σ1 :+ σ2} {τ} h a ctg
                   ≡ k a

    -- Question: Zou een implementatie dit kunnen bewijzen? Ik denk van wel
    DSemᵀ-extensionality : {σ τ : Typ Pr}
              → (f : Rep σ →  Rep τ) 
              → (g : Rep σ →  Rep τ) 
              → (a : Rep σ)
              → (ctg : LinRepDense (D2τ' τ))
              → ( (x : Rep σ) → f x ≡ g x  )
              → DSemᵀ {σ} {τ} f a ctg
              ≡ DSemᵀ {σ} {τ} g a ctg

    -- ======================
    -- DSem on linear functions (Derivative of a linear function f is f)
    -- ======================
    DSemᵀ-identity : {τ : Typ Pr} 
            → (a : Rep τ)
            → (ctg : LinRepDense (D2τ' τ))
            → DSemᵀ {τ} {τ} id a ctg
              ≡ ctg

    DSemᵀ-inj₁ : {σ τ : Typ Pr}
            → (a : Rep σ)
            → (ctg : LinRepDense (D2τ' (σ :+ τ)))
            → DSemᵀ {σ} {σ :+ τ} inj₁ a ctg
              ≡ fst ctg

    DSemᵀ-inj₂ : {σ τ : Typ Pr}
            → (a : Rep σ)
            → (ctg : LinRepDense (D2τ' (τ :+ σ)))
            → DSemᵀ {σ} {τ :+ σ} inj₂ a ctg
              ≡ snd ctg

    -- ======================
    -- (primitive) Operations on Floats
    -- ======================
    DSemᵀ-prim-floatPlus : let  σ : Typ Pr ; σ = (R :* R) ; τ : Typ Pr ; τ = R 
            in (a : Rep σ)
            → (ctg : LinRepDense (D2τ' τ))
            → let (x , y) = a
              in DSemᵀ {σ} {τ} (uncurry primFloatPlus) (x , y) ctg
              ≡ (ctg , ctg)

    DSemᵀ-prim-floatTimes : let  σ : Typ Pr ; σ = (R :* R) ; τ : Typ Pr ; τ = R 
            in (a : Rep σ)
            → (ctg : LinRepDense (D2τ' τ))
            → let (x , y) = a
              in DSemᵀ {σ} {τ} (uncurry primFloatTimes) (x , y) ctg
              ≡ (primFloatTimes ctg y , primFloatTimes ctg x)

    DSemᵀ-prim-floatNegate : let  σ : Typ Pr ; σ = R ; τ : Typ Pr ; τ = R 
            in (a : Rep σ) 
            → (ctg : LinRepDense (D2τ' τ))
            → DSemᵀ {σ} {τ} primFloatNegate a ctg
              ≡ primFloatNegate ctg