module correctness.dsem where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Float using (primFloatPlus; primFloatTimes; primFloatNegate)
open import Agda.Builtin.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; Is-just; to-witness; just; nothing)
open import Data.List using (_∷_)
open import Data.Product.Base using (uncurry; _×_; Σ)
open import Function.Base using (id; _∘_; _$_; flip; case_of_)
open import Function.Bundles using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≗_)

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

fmap₂ : {A B C : Set} → (A → B → C) → Maybe A → Maybe B → Maybe C
fmap₂ f (just x) (just y) = just (f x y)
fmap₂ _ _ _ = nothing

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

    -- TODO: Merge the chain rules. Note that f . g only exists if f and g exist (at point a ofc.)
    DSemᵀ-chain : {τ1 τ2 τ3 : Typ Pr}
                → (f : Rep τ2 → Rep τ3)
                → (g : Rep τ1 → Rep τ2)
                → (a : Rep τ1)
                → (df∘g : Is-just (DSemᵀ {τ1} {τ3} (f ∘ g) a))
                → (df : Is-just (DSemᵀ {τ2} {τ3} f (g a)))
                → (dg : Is-just (DSemᵀ {τ1} {τ2} g a))
                → (ctg : LinRepDense (D2τ' τ3))
                → to-witness df∘g ctg ≡ to-witness dg (to-witness df ctg)

    DSemᵀ-exists-chain : {τ1 τ2 τ3 : Typ Pr}
                → (f : Rep τ2 → Rep τ3)
                → (g : Rep τ1 → Rep τ2)
                → (a : Rep τ1)
                → (Is-just $ DSemᵀ {τ1} {τ3} (f ∘ g) a)
                  ⇔ (Is-just (DSemᵀ {τ1} {τ2} g a) × Is-just (DSemᵀ {τ2} {τ3} f (g a)))

    -- QUESTION: Welke stijl willen we voor de postualtions?
    -- Voorstel: Equality van de LinRepDense met behulp van 'Is-just' en dependent products, eventueel ook een extra 'exists' postulation (e.g. alles behalve DSemᵀ-pair)  
    -- Alternatief: Equality van de (Maybe LinRepDense) dus met fmap₂ en _??_ . (e.g. DSemᵀ-pair)
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
                   ≡ fmap₂ (plusvDense (D2τ' σ)) (df ?? ctg-f) (dg ?? ctg-g))

    DSemᵀ-var : {Γ : Env Pr} {τ : Typ Pr}
              → let σ = Etup Pr Γ
              in (a : Rep σ)
              → (idx : Idx Γ τ)
              → (ctg : LinRepDense (D2τ' τ))
              → Σ (Is-just $ DSemᵀ {σ} {τ} (flip valprj idx ∘ Etup-to-val) a)
                  (λ df → to-witness df ctg ≡ onehot idx ctg)

    DSemᵀ-case : {σ1 σ2 ρ τ : Typ Pr}
              → (a : Rep ρ)
              → (c : Rep ρ → Rep (σ1 :+ σ2))
              → (l : Rep σ1 → Rep ρ → Rep τ) 
              → (r : Rep σ2 → Rep ρ → Rep τ) 
              → (dc : Is-just $ DSemᵀ {ρ} {σ1 :+ σ2} c a)
              → (ctg : LinRepDense (D2τ' τ))
              → let f = case c a of [ l , r ]
              in case c a of
                  [ (λ v → (dl : Is-just $ DSemᵀ {ρ} {τ} (l v) a )
                         → Σ (Is-just $ DSemᵀ {ρ} {τ} f a)
                             ( λ df → to-witness df ctg ≡ to-witness dl ctg))
                  , (λ v → (dr : Is-just $ DSemᵀ {ρ} {τ} (r v) a )
                         → Σ (Is-just $ DSemᵀ {ρ} {τ} f a)
                             ( λ df → to-witness df ctg ≡ to-witness dr ctg))
                  ]
        --       → let f : (Rep ((σ1 :+ σ2) :* ρ) ) → Rep τ
                --     f = λ (xs , a') → [ (λ x → l (x , a'))
                --                       , (λ x → r (x , a'))
                --                      ] xs
        --       in  [ (λ v → let dsem-l = DSemᵀ {σ1 :* ρ} {τ} l (v , snd a) ctg
        --                      in DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a ctg 
        --                         ≡  ( (dsem-l .fst , zerovDense (D2τ' σ2)) , dsem-l .snd)  )
        --           , (λ v → let dsem-r = DSemᵀ {σ2 :* ρ} {τ} r (v , snd a) ctg
        --                      in DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a ctg 
        --                         ≡  ( (zerovDense (D2τ' σ1) , dsem-r .fst) , dsem-r .snd)  )
        --           ] (a .fst)
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
                  
    DSemᵀ-extensionality : {σ τ : Typ Pr}
              → (f : Rep σ →  Rep τ) 
              → (g : Rep σ →  Rep τ) 
              → (f ≗ g) -- f and g are equal for all inputs
              → (a : Rep σ)
              → (df : Is-just $ DSemᵀ {σ} {τ} f a)
              → (dg : Is-just $ DSemᵀ {σ} {τ} g a)
              → (ctg : LinRepDense (D2τ' τ))
              → (to-witness df ctg ≡ to-witness dg ctg)

    -- TODO: Give an actual proof for this
    DSemᵀ-exists-evaluation-f : {σ τ : Typ Pr}
              → (f : Rep σ →  Rep τ) 
              → (g : Rep σ →  Rep τ) 
              → (f ≡ g) -- Note that this is NOT pointwise equality. 
              → (a : Rep σ)
              → (df : Is-just $ DSemᵀ {σ} {τ} f a)
              → (ctg : LinRepDense (D2τ' τ))
              → Σ (Is-just $ DSemᵀ {σ} {τ} g a)
                  ( λ dg → to-witness df ctg ≡ to-witness dg ctg  )

    -- TODO: Give an actual proof for this
    DSemᵀ-exists-evaluation-a : {σ τ : Typ Pr}
              → (f : Rep σ →  Rep τ) 
              → (a : Rep σ)
              → (b : Rep σ)
              → (a ≡ b)
              → (df : Is-just $ DSemᵀ {σ} {τ} f a)
              → (ctg : LinRepDense (D2τ' τ))
              → Σ (Is-just $ DSemᵀ {σ} {τ} f b)
                  ( λ dg → to-witness df ctg ≡ to-witness dg ctg  )

--     -- ======================
--     -- DSem on linear functions (Derivative of a linear function f is f)
--     -- ======================
    DSemᵀ-identity : {τ : Typ Pr} 
            → (a : Rep τ)
            → (ctg : LinRepDense (D2τ' τ))
            → Σ (Is-just $ DSemᵀ {τ} {τ} id a)
                ( λ d-id → to-witness d-id ctg ≡ ctg)

    DSemᵀ-inj₁ : {σ τ : Typ Pr}
            → (a : Rep σ)
            → (ctg : LinRepDense (D2τ' (σ :+ τ)))
            → Σ (Is-just $ DSemᵀ {σ} {σ :+ τ} inj₁ a)
                ( λ df → to-witness df ctg ≡ fst ctg)

    DSemᵀ-inj₂ : {σ τ : Typ Pr}
            → (a : Rep σ)
            → (ctg : LinRepDense (D2τ' (τ :+ σ)))
            → Σ (Is-just $ DSemᵀ {σ} {τ :+ σ} inj₂ a)
                ( λ df → to-witness df ctg ≡ snd ctg)

    -- Check: Is dit echt nodig?
    DSemᵀ-fst : {σ τ : Typ Pr}
            → (a : Rep (σ :* τ))
            → (ctg : LinRepDense (D2τ' σ))
            → Σ (Is-just $ DSemᵀ {σ :* τ} {σ} fst a)
                ( λ df → to-witness df ctg ≡ (ctg , zerovDense (D2τ' τ)))

--     -- ======================
--     -- (primitive) Operations on Floats
--     -- ======================
    DSemᵀ-prim-floatPlus : let  σ : Typ Pr ; σ = (R :* R) ; τ : Typ Pr ; τ = R 
            in (a : Rep σ)
            → (ctg : LinRepDense (D2τ' τ))
            → let (x , y) = a
            in Σ ( Is-just $ DSemᵀ {σ} {τ} (uncurry primFloatPlus) a)
                 ( λ df → to-witness df ctg
                          ≡ (ctg , ctg) )

    DSemᵀ-prim-floatTimes : let  σ : Typ Pr ; σ = (R :* R) ; τ : Typ Pr ; τ = R 
            in (a : Rep σ)
            → (ctg : LinRepDense (D2τ' τ))
            → let (x , y) = a
            in Σ ( Is-just $ DSemᵀ {σ} {τ} (uncurry primFloatTimes) a)
                 ( λ df → to-witness df ctg
                         ≡ (primFloatTimes ctg y , primFloatTimes ctg x))

    DSemᵀ-prim-floatNegate : let  σ : Typ Pr ; σ = R ; τ : Typ Pr ; τ = R 
            in (a : Rep σ) 
            → (ctg : LinRepDense (D2τ' τ))
            → Σ (Is-just $ DSemᵀ {σ} {τ} primFloatNegate a)
                ( λ df → to-witness df ctg ≡ primFloatNegate ctg)