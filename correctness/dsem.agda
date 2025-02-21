module correctness.dsem where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; Is-just; to-witness; just; nothing)
open import Data.List using (_∷_)
open import Function.Base using (id; _∘_; _$_; flip; case_of_)
open import Data.Product.Base using (uncurry; _×_; Σ)
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


-- Named after the operator from the haskell Control.Lens.Lens package
-- Applies an argument to a function inside a maybe.
_??_ : {A B : Set} → Maybe (A → B) → A → Maybe B
_??_ (just f) x = just (f x)
_??_ nothing _  = nothing

-- Todo: figure out how to do applicative style stuff
map₂ : {A B C : Set} → (A → B → C) → Maybe A → Maybe B → Maybe C
map₂ f (just x) (just y) = just (f x y)
map₂ _ _ _ = nothing

postulate
    -- ======================
    -- Definition
    -- ======================
    DSemᵀ :  {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep σ) 
            → Maybe ((ctg : LinRepDense (D2τ' τ)) → LinRepDense (D2τ' σ))

    -- ======================
    -- Misc. rules
    -- ======================
    DSemᵀ-ctg-zero : {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep σ)
            → (dsem : Is-just (DSemᵀ {σ} {τ} f a))
            → (to-witness dsem) (zerovDense (D2τ' τ)) ≡ zerovDense (D2τ' σ)

    DSemᵀ-chain : {τ1 τ2 τ3 : Typ Pr}
                → (f : Rep τ2 → Rep τ3)
                → (g : Rep τ1 → Rep τ2)
                → (a : Rep τ1)
                → (df∘g : Is-just (DSemᵀ {τ1} {τ3} (f ∘ g) a))
                → (ctg : LinRepDense (D2τ' τ3))
                → Σ (Is-just (DSemᵀ {τ1} {τ2} g a) × Is-just (DSemᵀ {τ2} {τ3} f (g a)))
                    (λ (dg , df) → (to-witness df∘g) ctg ≡ (to-witness dg) ((to-witness df $ ctg)))

    DSemᵀ-pair : {σ τ1 τ2 : Typ Pr}
            → (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → let h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
            in (a : Rep σ)
            → (ctg-f : LinRepDense (D2τ' τ1))
            → (ctg-g : LinRepDense (D2τ' τ2))
            → let ctg : LinRepDense (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
                  dh = DSemᵀ {σ} {τ1 :* τ2} h a
                  df = DSemᵀ {σ} {τ1} f a
                  dg = DSemᵀ {σ} {τ2} g a
              in ( (dh ?? ctg)
                   ≡ map₂ (plusvDense (D2τ' σ)) (df ?? ctg-f) (dg ?? ctg-g))

--     DSemᵀ-var : {Γ : Env Pr} {τ : Typ Pr}
--               → let σ = Etup Pr Γ
--               in (a : Rep σ)
--               → (idx : Idx Γ τ)
--               → (ctg : LinRepDense (D2τ' τ))
--               → DSemᵀ {σ} {τ} (flip valprj idx ∘ Etup-to-val) a ctg
--                 ≡ onehot idx ctg

--     DSemᵀ-case : {σ1 σ2 ρ τ : Typ Pr}
--               → (a : Rep ((σ1 :+ σ2) :* ρ))
--               → (l : Rep (σ1 :* ρ) → Rep τ) 
--               → (r : Rep (σ2 :* ρ) → Rep τ) 
--               → (ctg : LinRepDense (D2τ' τ))
--               → let f : (Rep ((σ1 :+ σ2) :* ρ) ) → Rep τ
--                     f = λ (xs , a') → [ (λ x → l (x , a'))
--                                       , (λ x → r (x , a'))
--                                      ] xs
--               in  [ (λ v → let dsem-l = DSemᵀ {σ1 :* ρ} {τ} l (v , snd a) ctg
--                              in DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a ctg 
--                                 ≡  ( (dsem-l .fst , zerovDense (D2τ' σ2)) , dsem-l .snd)  )
--                   , (λ v → let dsem-r = DSemᵀ {σ2 :* ρ} {τ} r (v , snd a) ctg
--                              in DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a ctg 
--                                 ≡  ( (zerovDense (D2τ' σ1) , dsem-r .fst) , dsem-r .snd)  )
--                   ] (a .fst)
                  
--     DSemᵀ-extensionality : {σ τ : Typ Pr}
--               → (f : Rep σ →  Rep τ) 
--               → (g : Rep σ →  Rep τ) 
--               → (a : Rep σ)
--               → (ctg : LinRepDense (D2τ' τ))
--               → ( (x : Rep σ) → f x ≡ g x  )
--               → DSemᵀ {σ} {τ} f a ctg
--               ≡ DSemᵀ {σ} {τ} g a ctg

--     -- ======================
--     -- DSem on linear functions (Derivative of a linear function f is f)
--     -- ======================
--     DSemᵀ-identity : {τ : Typ Pr} 
--             → (a : Rep τ)
--             → (ctg : LinRepDense (D2τ' τ))
--             → DSemᵀ {τ} {τ} id a ctg
--               ≡ ctg

--     DSemᵀ-inj₁ : {σ τ : Typ Pr}
--             → (a : Rep σ)
--             → (ctg : LinRepDense (D2τ' (σ :+ τ)))
--             → DSemᵀ {σ} {σ :+ τ} inj₁ a ctg
--               ≡ fst ctg

--     DSemᵀ-inj₂ : {σ τ : Typ Pr}
--             → (a : Rep σ)
--             → (ctg : LinRepDense (D2τ' (τ :+ σ)))
--             → DSemᵀ {σ} {τ :+ σ} inj₂ a ctg
--               ≡ snd ctg

--     -- ======================
--     -- (primitive) Operations on Floats
--     -- ======================
--     DSemᵀ-prim-floatPlus : let  σ : Typ Pr ; σ = (R :* R) ; τ : Typ Pr ; τ = R 
--             in (a : Rep σ)
--             → (ctg : LinRepDense (D2τ' τ))
--             → let (x , y) = a
--               in DSemᵀ {σ} {τ} (uncurry primFloatPlus) (x , y) ctg
--               ≡ (ctg , ctg)

--     DSemᵀ-prim-floatTimes : let  σ : Typ Pr ; σ = (R :* R) ; τ : Typ Pr ; τ = R 
--             in (a : Rep σ)
--             → (ctg : LinRepDense (D2τ' τ))
--             → let (x , y) = a
--               in DSemᵀ {σ} {τ} (uncurry primFloatTimes) (x , y) ctg
--               ≡ (primFloatTimes ctg y , primFloatTimes ctg x)

--     DSemᵀ-prim-floatNegate : let  σ : Typ Pr ; σ = R ; τ : Typ Pr ; τ = R 
--             in (a : Rep σ) 
--             → (ctg : LinRepDense (D2τ' τ))
--             → DSemᵀ {σ} {τ} primFloatNegate a ctg
--               ≡ primFloatNegate ctg