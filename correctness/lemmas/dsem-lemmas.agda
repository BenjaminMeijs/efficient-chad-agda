{-# OPTIONS --allow-unsolved-metas #-}
module correctness.lemmas.dsem-lemmas where 

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_×_; uncurry; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; isInj₁; isInj₂)
import Data.Sum as Sum using (map)
open import Data.Maybe using (Maybe; Is-just; to-witness; just; nothing; maybe; from-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ)
import Data.Maybe.Relation.Unary.Any as Any
open import Function.Bundles using (_⇔_;  mk⇔; Equivalence)
-- import Data.Maybe.Relation.Unary.All as All
open import Function.Base using (_$_; _∘_; id; case_of_; flip)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import correctness.lemmas.LinRepDense-is-comm-monoid using (plusvDense-zeroR'; plusvDense-zeroL'; zerov-equiv-zerovDense)

open import spec
open import correctness.spec
open import correctness.dsem
import spec.LACM as LACM

-- ======================
-- internal helpers
-- ======================
private
    trans₂ : {A : Set} {x y a b : A} → x ≡ y → x ≡ a → y ≡ b → a ≡ b
    trans₂ refl refl refl = refl

    just-eq : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
    just-eq refl = refl

    just-nothing-absurd : {A : Set} {x : A} → just x ≡ nothing → ⊥
    just-nothing-absurd ()

-- DSemᵀ-lemma-cong-a : {σ τ : Typ Pr}
--           → (f : Rep σ →  Rep τ) 
--           → (a : Rep σ)
--           → (b : Rep σ)
--           → (a ≡ b)
--           → (df : Is-just $ DSemᵀ {σ} {τ} f a)
--           → (ctg : LinRepDense (D2τ' τ))
--           → Σ (Is-just $ DSemᵀ {σ} {τ} f b)
--               ( λ dg → to-witness df ctg ≡ to-witness dg ctg  )
-- DSemᵀ-lemma-cong-a f a b refl df ctg = df , refl
DSemᵀ-lemma-cong-a : {σ τ : Typ Pr}
          → (f : Rep σ →  Rep τ) 
          → (a : Rep σ)
          → (b : Rep σ)
          → (a ≡ b)
          → (df : Is-just $ DSemᵀ {σ} {τ} f a)
          → (dg : Is-just $ DSemᵀ {σ} {τ} f b)
          → (ctg : LinRepDense (D2τ' τ))
          → to-witness df ctg ≡ to-witness dg ctg
DSemᵀ-lemma-cong-a f a b refl df dg ctg = DSemᵀ-extensionality f f (λ _ → refl) a df dg ctg

DSemᵀ-lemma-cong-f : {σ τ : Typ Pr}
          → (f : Rep σ →  Rep τ) 
          → (g : Rep σ →  Rep τ) 
          → (f ≡ g) -- Note that this is NOT pointwise equality. 
          → (a : Rep σ)
          → (df : Is-just $ DSemᵀ {σ} {τ} f a)
          → (ctg : LinRepDense (D2τ' τ))
          → Σ (Is-just $ DSemᵀ {σ} {τ} g a)
              ( λ dg → to-witness df ctg ≡ to-witness dg ctg  )
DSemᵀ-lemma-cong-f f g refl a df ctg = df , refl



module Zero {σ τ : Typ Pr} { f : Rep σ  →  Rep τ } { a : Rep σ }
    { ctg : LinRepDense (D2τ' τ) }
    {{ w : ctg ≡ zerovDense (D2τ' τ)}}
    ( df : Is-just (DSemᵀ {σ} {τ} f a) )
    where
    DSemᵀ-lemma-ctg-zero' : (to-witness df) ctg ≡ zerovDense (D2τ' σ)
    DSemᵀ-lemma-ctg-zero'
      rewrite w
      = DSemᵀ-ctg-zero f a df 
module Pair { σ τ1 τ2 : Typ Pr } (f : Rep σ →  Rep τ1) (g : Rep σ →  Rep τ2) (a : Rep σ) where
    -- helper functions
    private
      h : Rep σ → Rep (τ1 :* τ2)
      h e = (f e , g e)

      helper : 
            (ctg-f : LinRepDense (D2τ' τ1))
          → (ctg-g : LinRepDense (D2τ' τ2))
          → {v1 : Maybe (LinRepDense (D2τ' (τ1 :* τ2)) → LinRepDense (D2τ' σ)) }
          → ( DSemᵀ h a ≡ v1  )
          → {v2 : Maybe (LinRepDense (D2τ' τ1) → LinRepDense (D2τ' σ))}
          → ( DSemᵀ f a ≡ v2  )
          → {v3 : Maybe (LinRepDense (D2τ' τ2) → LinRepDense (D2τ' σ))}
          → ( DSemᵀ g a ≡ v3  )
          → (v1 ?? (ctg-f , ctg-g)) ≡
            fmap₂ (plusvDense (D2τ' σ)) (v2 ?? ctg-f) (v3 ?? ctg-g)
      helper ctg-f ctg-g eq1 eq2 eq3 = trans₂ (DSemᵀ-pair {σ = σ} f g a ctg-f ctg-g)
                      (cong (λ x → x ?? (ctg-f , ctg-g)) eq1)
                      (cong₂ (λ x y → fmap₂ (plusvDense (D2τ' _)) (x ?? ctg-f) (y ?? ctg-g)) eq2 eq3)

      helper2 : 
        let ctg-f = zerovDense (D2τ' τ1)
            ctg-g = zerovDense (D2τ' τ2)
        in  {v1 : Maybe (LinRepDense (D2τ' (τ1 :* τ2)) → LinRepDense (D2τ' σ)) }
        → ( DSemᵀ h a ≡ v1  )
        → {v2 : Maybe (LinRepDense (D2τ' τ1) → LinRepDense (D2τ' σ))}
        → ( DSemᵀ f a ≡ v2  )
        → {v3 : Maybe (LinRepDense (D2τ' τ2) → LinRepDense (D2τ' σ))}
        → ( DSemᵀ g a ≡ v3  )
        → (v1 ?? (ctg-f , ctg-g)) ≡
          fmap₂ (plusvDense (D2τ' σ)) (v2 ?? ctg-f) (v3 ?? ctg-g)
      helper2 = helper (zerovDense (D2τ' τ1)) (zerovDense (D2τ' τ2))

    DSemᵀ-exists-lemma-pair₁ : 
        Is-just (DSemᵀ {σ} {τ1 :* τ2} h a) 
        → ( Is-just (DSemᵀ {σ} {τ1} f a) × Is-just (DSemᵀ {σ} {τ2} g a))
    DSemᵀ-exists-lemma-pair₁ x
      with DSemᵀ {σ} {τ1 :* τ2} (λ e → (f e , g e)) a in eq1
        | DSemᵀ {σ} {τ1} f a in eq2
        | DSemᵀ {σ} {τ2} g a in eq3
    DSemᵀ-exists-lemma-pair₁ () | nothing | _ | _
    ... | just _ | just _  | just _  = Any.just tt , Any.just tt
    ... | just _ | nothing | nothing = ⊥-elim (just-nothing-absurd (helper2 eq1 eq2 eq3))
    ... | just _ | just _  | nothing = ⊥-elim (just-nothing-absurd (helper2 eq1 eq2 eq3))
    ... | just _ | nothing | just _  = ⊥-elim (just-nothing-absurd (helper2 eq1 eq2 eq3))

    DSemᵀ-exists-lemma-pair₂ :
        ( Is-just (DSemᵀ {σ} {τ1} f a) × Is-just (DSemᵀ {σ} {τ2} g a))
        → Is-just (DSemᵀ {σ} {τ1 :* τ2} h a) 
    DSemᵀ-exists-lemma-pair₂ x
      with DSemᵀ {σ} {τ1 :* τ2} (λ e → (f e , g e)) a in eq1
        | DSemᵀ {σ} {τ1} f a in eq2
        | DSemᵀ {σ} {τ2} g a in eq3
    DSemᵀ-exists-lemma-pair₂ () | _ | nothing | _
    DSemᵀ-exists-lemma-pair₂ () | _ | _ | nothing
    ... | just _  | just _ | just _ = Any.just tt
    ... | nothing | just _ | just _ = ⊥-elim (just-nothing-absurd (sym (helper2 eq1 eq2 eq3)))

    DSemᵀ-exists-lemma-pair :
              Is-just (DSemᵀ {σ} {τ1 :* τ2} h a) 
              ⇔ (( Is-just (DSemᵀ {σ} {τ1} f a) × Is-just (DSemᵀ {σ} {τ2} g a)))
    DSemᵀ-exists-lemma-pair = mk⇔ DSemᵀ-exists-lemma-pair₁ DSemᵀ-exists-lemma-pair₂

    DSemᵀ-lemma-pair : 
              (dh : Is-just (DSemᵀ {σ} {τ1 :* τ2} h a))
            → (df : Is-just (DSemᵀ {σ} {τ1} f a))
            → (dg : Is-just (DSemᵀ {σ} {τ2} g a))
            → (ctg-f : LinRepDense (D2τ' τ1))
            → (ctg-g : LinRepDense (D2τ' τ2))
            → (to-witness dh) (ctg-f , ctg-g)
              ≡ plusvDense (D2τ' σ) (to-witness df ctg-f) (to-witness dg ctg-g)
    DSemᵀ-lemma-pair Wdh Wdf Wdg ctg-f ctg-g
      using h ← λ e → (f e , g e)
      with DSemᵀ {σ} {τ1 :* τ2} h a in eq1
        | DSemᵀ {σ} {τ1} f a in eq2
        | DSemᵀ {σ} {τ2} g a in eq3
    DSemᵀ-lemma-pair (Any.just _) (Any.just _) (Any.just _) ctg-f ctg-g
      | just dh | just df | just dg 
      rewrite just-eq (helper ctg-f ctg-g eq1 eq2 eq3)
      = refl

    DSemᵀ-lemma-pair-zeroR : 
              (dh : Is-just (DSemᵀ {σ} {τ1 :* τ2} h a))
              (df : Is-just (DSemᵀ {σ} {τ1} f a))
              (dg : Is-just (DSemᵀ {σ} {τ2} g a))
              (ctg-f : LinRepDense (D2τ' τ1))
            → let 
                  ctg-g = sparse2dense (zerov (D2τ' τ2) .fst)
                  ctg : LinRepDense (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
              in (to-witness dh ctg) ≡ (to-witness df ctg-f)
    DSemᵀ-lemma-pair-zeroR dh df dg ctg-f
      = let ctg-g = sparse2dense (zerov (D2τ' τ2) .fst)
        in trans (DSemᵀ-lemma-pair dh df dg ctg-f ctg-g)
                 (plusvDense-zeroR' {{Zero.DSemᵀ-lemma-ctg-zero' {{zerov-equiv-zerovDense (D2τ' τ2)}} dg}})

    DSemᵀ-lemma-pair-zeroL : 
              (dh : Is-just (DSemᵀ {σ} {τ1 :* τ2} h a))
              (df : Is-just (DSemᵀ {σ} {τ1} f a))
              (dg : Is-just (DSemᵀ {σ} {τ2} g a))
              (ctg-g : LinRepDense (D2τ' τ2))
            → let 
                  ctg-f = sparse2dense (zerov (D2τ' τ1) .fst)
                  ctg : LinRepDense (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
              in (to-witness dh ctg) ≡ (to-witness dg ctg-g)
    DSemᵀ-lemma-pair-zeroL dh df dg ctg-g
      = let ctg-f = sparse2dense (zerov (D2τ' τ1) .fst)
        in trans (DSemᵀ-lemma-pair dh df dg ctg-f ctg-g)
                 (plusvDense-zeroL' {{Zero.DSemᵀ-lemma-ctg-zero' {{zerov-equiv-zerovDense (D2τ' τ1)}} df}})

DSemᵀ-lemma-chain : {τ1 τ2 τ3 : Typ Pr}
            → (f : Rep τ2 → Rep τ3)
            → (g : Rep τ1 → Rep τ2)
            → (a : Rep τ1)
            → (df∘g : Is-just (DSemᵀ {τ1} {τ3} (f ∘ g) a))
            → (df : Is-just (DSemᵀ {τ2} {τ3} f (g a)))
            → (dg : Is-just (DSemᵀ {τ1} {τ2} g a))
            → (ctg : LinRepDense (D2τ' τ3))
            → to-witness df∘g ctg ≡ to-witness dg (to-witness df ctg)
DSemᵀ-lemma-chain f g a df∘g df dg ctg 
  = let (df∘g' , eq1) = DSemᵀ-chain f g a df dg ctg
        eq2 = DSemᵀ-extensionality _ _ (λ _ → refl) a df∘g' df∘g ctg
    in trans₂ eq1 eq2 refl

DSemᵀ-exists-lemma-chain : {τ1 τ2 τ3 : Typ Pr}
            → (f : Rep τ2 → Rep τ3)
            → (g : Rep τ1 → Rep τ2)
            → (a : Rep τ1)
            → (df : Is-just (DSemᵀ {τ2} {τ3} f (g a)))
            → (dg : Is-just (DSemᵀ {τ1} {τ2} g a))
            → Is-just (DSemᵀ {τ1} {τ3} (f ∘ g) a)
DSemᵀ-exists-lemma-chain {τ3 = τ3} f g a df dg
  = DSemᵀ-chain f g a df dg (zerovDense (D2τ' τ3)) .fst

DSemᵀ-lemma-inj₁ : {σ τ ρ : Typ Pr}
        → (f : Rep σ →  Rep τ) → (a : Rep σ)
        → (df : Is-just (DSemᵀ {σ} {τ} f a))
        → (dg : Is-just (DSemᵀ {σ} {τ :+ ρ} (inj₁ ∘ f) a))
        → (ctgL : LinRepDense (D2τ' τ)) → (ctgR : LinRepDense (D2τ' ρ))
        → to-witness df ctgL ≡ to-witness dg (ctgL , ctgR)
DSemᵀ-lemma-inj₁ {σ} {τ} {ρ} f a df dg ctgL ctgR = 
  let (d-inj , eq) = DSemᵀ-inj₁ (f a) ((ctgL , ctgR))
  in begin
  to-witness df ctgL
  ≡⟨ cong (to-witness df) (sym eq) ⟩
  to-witness df (to-witness d-inj (ctgL , ctgR))
  ≡⟨ sym ( DSemᵀ-lemma-chain inj₁ f a dg d-inj df (ctgL , ctgR)) ⟩
  to-witness dg (ctgL , ctgR)
  ∎

private 
    unpack-isInj₁ : {A B : Set} (x : A) (y : A ⊎ B)
          → (y ≡ inj₁ x)
          → (w : Is-just (isInj₁ y)) 
          → (x ≡ to-witness w)
    unpack-isInj₁ _ _ refl (Any.just _) = refl

    unpack-isInj₂ : {A B : Set} (x : B) (y : A ⊎ B)
          → (y ≡ inj₂ x)
          → (w : Is-just (isInj₂ y)) 
          → (x ≡ to-witness w)
    unpack-isInj₂ _ _ refl (Any.just _) = refl

DSemᵀ-lemma-case-inj₁ : {σ1 σ2 ρ τ : Typ Pr}
          → (a : Rep ((σ1 :+ σ2) :* ρ))
          → (l : Rep (σ1 :* ρ) → Rep τ) 
          → (r : Rep (σ2 :* ρ) → Rep τ) 
          → (v : Rep σ1) → (fst a ≡ inj₁ v)
          → let f : (Rep ((σ1 :+ σ2) :* ρ) ) → Rep τ
                f = λ (xs , a') → [ (λ x → l (x , a'))
                                  , (λ x → r (x , a'))
                                  ] xs
          in (df : Is-just $ DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a)
          → (dl : Is-just $ DSemᵀ {σ1 :* ρ} {τ} l (v , snd a))
          → (ctg : LinRepDense (D2τ' τ))
          → to-witness df ctg ≡ ((to-witness dl ctg .fst , zerovDense (D2τ' σ2)) , to-witness dl ctg .snd)
DSemᵀ-lemma-case-inj₁ {σ1 = σ1} {σ2 = σ2} a l r v w df dl ctg = ans
  where isLeft : Is-just (isInj₁ (fst a))
        isLeft rewrite w = Any.just tt
        rule = DSemᵀ-case-inj₁ a l r isLeft df ctg
        -- convincing agda that d-rule ≡ dl by propagating the fact that 'fst a ≡ inj₁ v'
        d-rule≡dl = DSemᵀ-lemma-cong-a l (v , snd a) (to-witness isLeft , snd a) (cong₂ _,_ (unpack-isInj₁ v (fst a) w isLeft) refl) dl (rule .fst) ctg
        ans : to-witness df ctg ≡ ((to-witness dl ctg .fst , zerovDense (D2τ' σ2)) , to-witness dl ctg .snd)
        ans rewrite snd rule rewrite d-rule≡dl = refl
        
DSemᵀ-lemma-case-inj₂ : {σ1 σ2 ρ τ : Typ Pr}
          → (a : Rep ((σ1 :+ σ2) :* ρ))
          → (l : Rep (σ1 :* ρ) → Rep τ) 
          → (r : Rep (σ2 :* ρ) → Rep τ) 
          → (v : Rep σ2) → (fst a ≡ inj₂ v)
          → let f : (Rep ((σ1 :+ σ2) :* ρ) ) → Rep τ
                f = λ (xs , a') → [ (λ x → l (x , a'))
                                  , (λ x → r (x , a'))
                                  ] xs
          in (df : Is-just $ DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a)
          → (dr : Is-just $ DSemᵀ {σ2 :* ρ} {τ} r (v , snd a))
          → (ctg : LinRepDense (D2τ' τ))
          → to-witness df ctg ≡ (( zerovDense (D2τ' σ1) , to-witness dr ctg .fst) , to-witness dr ctg .snd)
DSemᵀ-lemma-case-inj₂ {σ1 = σ1} {σ2 = σ2} a l r v w df dr ctg = ans
  where isRight : Is-just (isInj₂ (fst a))
        isRight rewrite w = Any.just tt
        rule = DSemᵀ-case-inj₂ a l r isRight df ctg
        -- convincing agda that d-rule ≡ dl by propagating the fact that 'fst a ≡ inj₂ v'
        d-rule≡dl = DSemᵀ-lemma-cong-a r (v , snd a) (to-witness isRight , snd a) (cong₂ _,_ (unpack-isInj₂ v (fst a) w isRight) refl) dr (rule .fst) ctg
        ans : to-witness df ctg ≡ (( zerovDense (D2τ' σ1) , to-witness dr ctg .fst) , to-witness dr ctg .snd)
        ans rewrite snd rule rewrite d-rule≡dl = refl


-- DSemᵀ-lemma-inj₂ : {σ τ ρ : Typ Pr}
--         → (f : Rep σ →  Rep τ) → (a : Rep σ)
--         → (ctgL : LinRepDense (D2τ' ρ)) → (ctgR : LinRepDense (D2τ' τ))
--         → DSemᵀ {σ} {τ} f a ctgR
--           ≡ DSemᵀ {σ} {ρ :+ τ} (inj₂ ∘ f) a ( ctgL , ctgR ) 
-- DSemᵀ-lemma-inj₂ {σ} {τ} {ρ} f a ctgL ctgR =
--   begin
--   DSemᵀ f a ctgR
--     ≡⟨ cong (DSemᵀ f a) (sym (DSemᵀ-inj₂ (f a) (ctgL , ctgR))) ⟩
--   DSemᵀ f a (DSemᵀ inj₂ (f a) (ctgL , ctgR))
--     ≡⟨ sym (DSemᵀ-chain inj₂ f a (ctgL , ctgR)) ⟩
--   DSemᵀ {σ} {ρ :+ τ} (inj₂ ∘ f) a (ctgL , ctgR)
--   ∎

-- -- ======================
-- -- Lemmas derivable from the postulations, that *do* include interp
-- -- ======================

-- private
--   -- This proof is used within the poslution DSemᵀ-extensionality to simplify interp (case' e l r) (Etup-to-val y)
--   -- The simplification is to ignore the costs of eval
--   interp-case-extensionality : {Γ : Env Pr} {σ τ ρ : Typ Pr}
--         → (e : Term Pr Γ (σ :+ τ))
--         → (l : Term Pr (σ ∷ Γ) ρ)
--         → (r : Term Pr (τ ∷ Γ) ρ)
--         → (y : Rep (Etup Pr Γ)) 
--         → let f = λ (zs , a) → [ (λ z → interp l (Etup-to-val (z , a))) 
--                                ,(λ z → interp r (Etup-to-val (z , a)))
--                                ] zs
--               g = λ a → ( interp e (Etup-to-val a) , a)
--         in (f ∘ g) y ≡ interp (case' e l r) (Etup-to-val y)
--   interp-case-extensionality e l r y with interp e (Etup-to-val y)
--   ... | inj₁ _  = refl
--   ... | inj₂ _  = refl


-- DSemᵀ-lemma-interp-case : {Γ : Env Pr} {σ τ ρ : Typ Pr}
--   → (a : Rep (Etup Pr Γ))
--   → (ctg : LinRepDense (D2τ' ρ))
--   → (e : Term Pr Γ (σ :+ τ))
--   → (l : Term Pr (σ ∷ Γ) ρ)
--   → (r : Term Pr (τ ∷ Γ) ρ)
--   → [ (λ x → let dsem-l = DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a) ctg
--                  dsem-e = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (dsem-l .fst , zerovDense (D2τ' τ))
--              in Etup2EV dsem-e ev+ Etup2EV (dsem-l .snd)
--                 ≡ Etup2EV (DSemᵀ (interp (case' e l r) ∘ Etup-to-val) a ctg))
--     , (λ x → let dsem-r = DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a) ctg
--                  dsem-e = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (zerovDense (D2τ' σ),  dsem-r .fst)
--              in Etup2EV dsem-e ev+ Etup2EV (dsem-r .snd)
--                 ≡ Etup2EV (DSemᵀ (interp (case' e l r) ∘ Etup-to-val) a ctg))
--     ] (interp e (Etup-to-val a))
-- -- This proof consists of two 'mirror' cases (inj₁ and inj₂)
-- -- For the inj₁ case we use ≡-reasoning since its verbosity makes clear how the proof works.
-- -- For the inj­₂ case we use rewrites for brevity
-- DSemᵀ-lemma-interp-case {Γ} {σ} {τ} {ρ} a ctg e l r
--   using f ← λ (zs , a) → [ (λ z → interp l (Etup-to-val (z , a))) 
--                           ,(λ z → interp r (Etup-to-val (z , a)))
--                          ] zs
--   using g ← λ a → ( interp e (Etup-to-val a) , a)
--   with interp e (Etup-to-val a) in interp-e-val≡inj-x  
-- ... | (inj₁ x) = 
--   let dsem-l = DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a) ctg
--       dsem-e = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (dsem-l .fst , zerovDense (D2τ' τ))
--       dsem-f = DSemᵀ {(σ :+ τ) :* (Etup Pr Γ)} {ρ} f (inj₁ x , a) ctg
--       dsem-g = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (dsem-f .fst)

--       case-lemma : ( (dsem-l .fst , zerovDense (D2τ' τ)) , dsem-l .snd) ≡ dsem-f
--       case-lemma = sym (DSemᵀ-case {σ} {τ} {Etup Pr Γ} {ρ} (inj₁ x , a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) ctg)
--   in begin
--   Etup2EV dsem-e ev+ Etup2EV (dsem-l .snd)
--     ≡⟨ cong₂ _ev+_ (cong Etup2EV (cong (DSemᵀ (interp e ∘ Etup-to-val) a) (cong fst case-lemma))) (cong Etup2EV (cong snd case-lemma)) ⟩
--   Etup2EV dsem-g ev+ Etup2EV (dsem-f .snd)
--     ≡⟨ ev+congR (cong Etup2EV (sym (DSemᵀ-identity a (dsem-f .snd)))) ⟩
--   Etup2EV dsem-g ev+ Etup2EV (DSemᵀ {Etup Pr Γ} {Etup Pr Γ} id a (dsem-f .snd))
--     ≡⟨ DSemᵀ-lemma-pair (interp e ∘ Etup-to-val) id a (dsem-f .fst) (dsem-f .snd) ⟩
--   Etup2EV (DSemᵀ {Etup Pr Γ} {(σ :+ τ) :* (Etup Pr Γ)} g a dsem-f)
--     ≡⟨ cong Etup2EV (cong (DSemᵀ g a) (cong (λ q → DSemᵀ {(σ :+ τ) :* (Etup Pr Γ)} {ρ} f q ctg) (cong₂ (_,_) (sym interp-e-val≡inj-x) refl))) ⟩
--   Etup2EV (DSemᵀ {Etup Pr Γ} {(σ :+ τ) :* (Etup Pr Γ)} g a (DSemᵀ {(σ :+ τ) :* (Etup Pr Γ)} {ρ} f (g a) ctg))
--     ≡⟨ cong Etup2EV (sym (DSemᵀ-chain f g a ctg)) ⟩
--   Etup2EV (DSemᵀ (f ∘ g) a ctg)
--     ≡⟨ cong Etup2EV (DSemᵀ-extensionality {Etup Pr Γ} {ρ} (f ∘ g) (interp (case' e l r) ∘ Etup-to-val) a ctg (interp-case-extensionality e l r)) ⟩
--   Etup2EV (DSemᵀ (λ a' → interp (case' e l r) (Etup-to-val a')) a ctg)
--     ≡⟨⟩
--   Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = ρ} (interp (case' e l r) ∘ Etup-to-val) a ctg)
--   ∎
-- ... | (inj₂ x) 
--   rewrite sym (DSemᵀ-extensionality {Etup Pr Γ} {ρ} (f ∘ g) (interp (case' e l r) ∘ Etup-to-val) a ctg (interp-case-extensionality e l r))
--   rewrite DSemᵀ-chain {Etup Pr Γ} {(σ :+ τ) :* Etup Pr Γ} {ρ} f g a ctg
--   rewrite interp-e-val≡inj-x
--   using dsem-t ← DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a) ctg
--   using dsem-e ← DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (zerovDense (D2τ' σ) , dsem-t .fst)
--   using dsem-f ← DSemᵀ {(σ :+ τ) :* (Etup Pr Γ)} {ρ} f (inj₂ x , a) ctg
--   using dsem-g ← DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (dsem-f .fst)
--   rewrite sym (DSemᵀ-lemma-pair {Γ} {σ :+ τ} {Etup Pr Γ} (interp e ∘ Etup-to-val) id a (dsem-f .fst) (dsem-f .snd))
--   rewrite DSemᵀ-identity {Etup Pr Γ} a (dsem-f .snd)  
--   rewrite DSemᵀ-case {σ} {τ} {Etup Pr Γ} {ρ} (inj₂ x , a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) ctg 
--   = refl

