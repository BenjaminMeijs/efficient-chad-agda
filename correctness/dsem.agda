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

    DSemᵀ-exists-unit : {σ : Typ Pr} { f : Rep σ → ⊤ } → ( a : Rep σ ) → Is-just (DSemᵀ {σ} {Typ.Un} f a)

    DSemᵀ-chain : {τ1 τ2 τ3 : Typ Pr}
                → (f : Rep τ2 → Rep τ3)
                → (g : Rep τ1 → Rep τ2)
                → (a : Rep τ1)
                → (df : Is-just (DSemᵀ {τ2} {τ3} f (g a)))
                → (dg : Is-just (DSemᵀ {τ1} {τ2} g a))
                → (ctg : LinRepDense (D2τ' τ3))
                → Σ (Is-just (DSemᵀ {τ1} {τ3} (f ∘ g) a)) 
                    ( λ df∘g → to-witness df∘g ctg ≡ to-witness dg (to-witness df ctg))

    DSemᵀ-pair : {σ τ1 τ2 : Typ Pr}
            → (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → (a : Rep σ)
            → let h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
            in (dh : Is-just (DSemᵀ {σ} {τ1 :* τ2} h a))
            → (df : Is-just (DSemᵀ {σ} {τ1} f a))
            → (dg : Is-just (DSemᵀ {σ} {τ2} g a))
            → (ctg-f : LinRepDense (D2τ' τ1))
            → (ctg-g : LinRepDense (D2τ' τ2))
            → (to-witness dh) (ctg-f , ctg-g)
              ≡ plusvDense (D2τ' σ) (to-witness df ctg-f) (to-witness dg ctg-g)

    DSemᵀ-exists-pair : {σ τ1 τ2 : Typ Pr}
            → (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → (a : Rep σ)
            → let h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
           in Is-just (DSemᵀ {σ} {τ1 :* τ2} h a) 
              ⇔ (( Is-just (DSemᵀ {σ} {τ1} f a) × Is-just (DSemᵀ {σ} {τ2} g a)))

    DSemᵀ-var : {Γ : Env Pr} {τ : Typ Pr}
              → let σ = Etup Pr Γ
              in (a : Rep σ)
              → (idx : Idx Γ τ)
              → (ctg : LinRepDense (D2τ' τ))
              → Σ (Is-just $ DSemᵀ {σ} {τ} (flip valprj idx ∘ Etup-to-val) a)
                  (λ df → to-witness df ctg ≡ onehot idx ctg)

    DSemᵀ-case : {σ1 σ2 ρ τ : Typ Pr}
              → (a : Rep ((σ1 :+ σ2) :* ρ))
              → (l : Rep (σ1 :* ρ) → Rep τ) 
              → (r : Rep (σ2 :* ρ) → Rep τ) 
              → let f : (Rep ((σ1 :+ σ2) :* ρ) ) → Rep τ
                    f = λ (xs , a') → [ (λ x → l (x , a'))
                                      , (λ x → r (x , a'))
                                     ] xs
              in (df : Is-just $ DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a)
              → (ctg : LinRepDense (D2τ' τ))
              → [ (λ v → Σ (Is-just $ DSemᵀ {σ1 :* ρ} {τ} l (v , snd a))
                           ( λ dl → to-witness df ctg 
                                    ≡ ((to-witness dl ctg .fst , zerovDense (D2τ' σ2)) , to-witness dl ctg .snd))) 
                , (λ v → Σ (Is-just $ DSemᵀ {σ2 :* ρ} {τ} r (v , snd a))
                           ( λ dr → to-witness df ctg 
                                    ≡ ((zerovDense (D2τ' σ1) , to-witness dr ctg .fst) , to-witness dr ctg .snd))) 
                ] (a .fst)

    DSemᵀ-exists-case : {σ1 σ2 ρ τ : Typ Pr}
              → (a : Rep ((σ1 :+ σ2) :* ρ))
              → (l : Rep (σ1 :* ρ) → Rep τ) 
              → (r : Rep (σ2 :* ρ) → Rep τ) 
              → let f : (Rep ((σ1 :+ σ2) :* ρ) ) → Rep τ
                    f = λ (xs , a') → [ (λ x → l (x , a'))
                                      , (λ x → r (x , a'))
                                     ] xs
              in [ (λ v → (Is-just $ DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a)
                         ⇔ (Is-just $ DSemᵀ {σ1 :* ρ} {τ} l (v , snd a)))

                , (λ v → (Is-just $ DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a)
                         ⇔ (Is-just $ DSemᵀ {σ2 :* ρ} {τ} r (v , snd a)))
                ] (a .fst)
                  
    DSemᵀ-extensionality : {σ τ : Typ Pr}
              → (f : Rep σ →  Rep τ) 
              → (g : Rep σ →  Rep τ) 
              → (f ≗ g) -- f and g are equal for all inputs
              → (a : Rep σ)
              → (df : Is-just $ DSemᵀ {σ} {τ} f a)
              → (dg : Is-just $ DSemᵀ {σ} {τ} g a)
              → (ctg : LinRepDense (D2τ' τ))
              → (to-witness df ctg ≡ to-witness dg ctg)

    DSemᵀ-exists-extensionality : {σ τ : Typ Pr}
              → (f : Rep σ →  Rep τ) 
              → (g : Rep σ →  Rep τ) 
              → (f ≗ g) -- f and g are equal for all inputs
              → (a : Rep σ)
              → (Is-just $ DSemᵀ {σ} {τ} f a) -- Note that this last arrow could also be ⇔, as the statement is symmetrical.
              → (Is-just $ DSemᵀ {σ} {τ} g a)

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

    DSemᵀ-exists-inj₁ : {σ τ1 τ2 : Typ Pr}
            → (f : Rep σ → Rep τ1) 
            → (a : Rep σ)
            → (Is-just $ DSemᵀ {σ} {τ1} f a)
              ⇔ (Is-just $ DSemᵀ {σ} {τ1 :+ τ2} (inj₁ ∘ f) a)

    DSemᵀ-inj₂ : {σ τ : Typ Pr}
            → (a : Rep σ)
            → (ctg : LinRepDense (D2τ' (τ :+ σ)))
            → Σ (Is-just $ DSemᵀ {σ} {τ :+ σ} inj₂ a)
                ( λ df → to-witness df ctg ≡ snd ctg)

    DSemᵀ-fst : {σ τ : Typ Pr}
            → (a : Rep (σ :* τ))
            → (ctg : LinRepDense (D2τ' σ))
            → Σ (Is-just $ DSemᵀ {σ :* τ} {σ} fst a)
                ( λ df → to-witness df ctg ≡ (ctg , zerovDense (D2τ' τ)))

    DSemᵀ-snd : {σ τ : Typ Pr}
            → (a : Rep (σ :* τ))
            → (ctg : LinRepDense (D2τ' τ))
            → Σ (Is-just $ DSemᵀ {σ :* τ} {τ} snd a)
                ( λ df → to-witness df ctg ≡ (zerovDense (D2τ' σ) , ctg))

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
