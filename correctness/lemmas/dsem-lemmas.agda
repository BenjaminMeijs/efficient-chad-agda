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
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import correctness.lemmas.LinRepDense-is-comm-monoid
open import correctness.lemmas.value-compatibility-lemmas

open import spec
open import correctness.spec
open import correctness.dsem
import spec.LACM as LACM

-- TODO: Clean up this file

-- ======================
-- internal helpers
-- ======================
private
    trans₂ : {A : Set} {x y a b : A} → x ≡ y → x ≡ a → y ≡ b → a ≡ b
    trans₂ refl refl refl = refl

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

DSemᵀ-exists-lemma-identity : {τ : Typ Pr} 
            → (a : Rep τ)
            → Is-just $ DSemᵀ {τ} {τ} id a
DSemᵀ-exists-lemma-identity {τ} a = DSemᵀ-identity a (zerovDense (D2τ' τ)) .fst


module Zero {σ τ : Typ Pr} { f : Rep σ  →  Rep τ } { a : Rep σ }
  { ctg : LinRepDense (D2τ' τ) }
  {{ w : ctg ≡ zerovDense (D2τ' τ)}}
  ( df : Is-just (DSemᵀ {σ} {τ} f a) )
  where
  DSemᵀ-lemma-ctg-zero' : (to-witness df) ctg ≡ zerovDense (D2τ' σ)
  DSemᵀ-lemma-ctg-zero'
    rewrite w
    = DSemᵀ-ctg-zero f a df 
open Zero public 

module Ev-zero {Γ : Env Pr} {τ : Typ Pr} { f : Rep (Etup Pr Γ)  →  Rep τ } { a : Rep (Etup Pr Γ) }
    { ctg : LinRepDense (D2τ' τ) }
    {{ w : ctg ≡ zerovDense (D2τ' τ)}}
    ( df : Is-just (DSemᵀ {Etup Pr Γ} {τ} f a) )
    where

    DSemᵀ-ev-lemma-ctg-zero' : Etup2EV (to-witness df ctg) ≡ zero-EV (map D2τ' Γ)
    DSemᵀ-ev-lemma-ctg-zero'
      = trans (cong (Etup2EV ∘ to-witness df) w) 
              (trans (cong Etup2EV (DSemᵀ-lemma-ctg-zero' df)) Etup-zerovDense-equiv-zero-EV)

    DSemᵀ-ev-lemma-ctg-zero-evIn' : { evIn : LEtup (map D2τ' Γ)  }
                    → LEtup2EV {map D2τ' Γ} evIn 
                      ≡ Etup2EV (to-witness df ctg) ev+ LEtup2EV {map D2τ' Γ} evIn
    DSemᵀ-ev-lemma-ctg-zero-evIn' {evIn} = sym (ev+zeroL' DSemᵀ-ev-lemma-ctg-zero')
open Ev-zero public

module Onehot where
    private
        onehot-equiv-addLEτ : {Γ : Env Pr} {τ : Typ Pr}
            → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
            in (ctg : LinRep (D2τ' τ))
            → (evIn : LEtup (map D2τ' Γ) )
            → Compatible-idx-LEtup (idx , ctg) evIn
            → LEtup2EV (addLEτ idx' ctg evIn)
              ≡ (Etup2EV (onehot idx (sparse2dense ctg)) ev+ LEtup2EV evIn)
        onehot-equiv-addLEτ {τ ∷ Γ}  Z      ctg (x , xs) w = cong₂ _,_ (plusv-equiv-plusvDense ctg x w) (sym (ev+zeroL' Etup-zerovDense-equiv-zero-EV))
        onehot-equiv-addLEτ {τ ∷ Γ} (S idx) ctg (x , xs) w = cong₂ _,_ (sym plusvDense-zeroL') (onehot-equiv-addLEτ idx ctg xs w)

    onehot-equiv-addLEτ-lemma : {Γ : Env Pr} {τ : Typ Pr}
        → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
        in (ctg : LinRep (D2τ' τ))
        → (evIn : LEtup (map D2τ' Γ) )
        → (val : Val Pr Γ) → (ctg ≃τ valprj val idx) → (evIn ≃Γ val)
        → LEtup2EV (addLEτ idx' ctg evIn)
          ≡ (Etup2EV (onehot idx (sparse2dense ctg)) ev+ LEtup2EV evIn)
    onehot-equiv-addLEτ-lemma idx ctg evIn val ~τ ~Γ = onehot-equiv-addLEτ idx ctg evIn (≃τ-and-≃Γ-implies-Compatible-idx-LEtup idx ctg evIn val ~τ ~Γ)
open Onehot public

module Pair { σ τ1 τ2 : Typ Pr } (f : Rep σ →  Rep τ1) (g : Rep σ →  Rep τ2) (a : Rep σ) where
    -- helper functions
    private
      just-eq : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
      just-eq refl = refl

      just-nothing-absurd : {A : Set} {x : A} → just x ≡ nothing → ⊥
      just-nothing-absurd ()

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
                 (plusvDense-zeroR' {{DSemᵀ-lemma-ctg-zero' {{zerov-equiv-zerovDense (D2τ' τ2)}} dg}})

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
                 (plusvDense-zeroL' {{DSemᵀ-lemma-ctg-zero' {{zerov-equiv-zerovDense (D2τ' τ1)}} df}})
open Pair public

module Ev-pair {Γ : Env Pr} {τ1 τ2 : Typ Pr } (f : Rep (Etup Pr Γ) →  Rep τ1) (g : Rep (Etup Pr Γ) →  Rep τ2) (a : Rep (Etup Pr Γ))
            (ctg-f : LinRepDense (D2τ' τ1)) (ctg-g : LinRepDense (D2τ' τ2))
            (df : Is-just (DSemᵀ {Etup Pr Γ} {τ1} f a))
            (dg : Is-just (DSemᵀ {Etup Pr Γ} {τ2} g a))
            (dh : Is-just (DSemᵀ {Etup Pr Γ} {τ1 :* τ2} (λ e → (f e , g e) ) a))
    where
    private
      h : Rep (Etup Pr Γ) → Rep (τ1 :* τ2)
      h e = (f e , g e)

    DSemᵀ-ev-lemma-pair : (Etup2EV (to-witness df ctg-f) ev+ Etup2EV (to-witness dg ctg-g)) 
                           ≡ Etup2EV (to-witness dh (ctg-f , ctg-g))
    DSemᵀ-ev-lemma-pair 
      = let rule = DSemᵀ-lemma-pair f g a dh df dg ctg-f ctg-g
        in sym (trans₂ (cong Etup2EV rule) refl (plusvDense-equiv-ev+ (to-witness df ctg-f) (to-witness dg ctg-g)))
open Ev-pair public

module Chain 
   {τ1 τ2 τ3 : Typ Pr}
   (f : Rep τ2 → Rep τ3)
   (g : Rep τ1 → Rep τ2)
   (a : Rep τ1)
   (df : Is-just (DSemᵀ {τ2} {τ3} f (g a)))
   (dg : Is-just (DSemᵀ {τ1} {τ2} g a))
  where
    DSemᵀ-lemma-chain : (df∘g : Is-just (DSemᵀ {τ1} {τ3} (f ∘ g) a)) → (ctg : LinRepDense (D2τ' τ3))
                → to-witness df∘g ctg ≡ to-witness dg (to-witness df ctg)
    DSemᵀ-lemma-chain df∘g ctg 
      = let (df∘g' , eq1) = DSemᵀ-chain f g a df dg ctg
            eq2 = DSemᵀ-extensionality _ _ (λ _ → refl) a df∘g' df∘g ctg
        in trans₂ eq1 eq2 refl

    DSemᵀ-exists-lemma-chain : Is-just (DSemᵀ {τ1} {τ3} (f ∘ g) a)
    DSemᵀ-exists-lemma-chain = DSemᵀ-chain f g a df dg (zerovDense (D2τ' τ3)) .fst
open Chain public

module Inj where 
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
      ≡⟨ sym ( DSemᵀ-lemma-chain inj₁ f a d-inj df dg (ctgL , ctgR)) ⟩
      to-witness dg (ctgL , ctgR)
      ∎

    DSemᵀ-lemma-inj₂ : {σ τ ρ : Typ Pr}
            → (f : Rep σ →  Rep ρ) → (a : Rep σ)
            → (df : Is-just (DSemᵀ {σ} {ρ} f a))
            → (dg : Is-just (DSemᵀ {σ} {τ :+ ρ} (inj₂ ∘ f) a))
            → (ctgL : LinRepDense (D2τ' τ)) → (ctgR : LinRepDense (D2τ' ρ))
            → to-witness df ctgR ≡ to-witness dg (ctgL , ctgR)
    DSemᵀ-lemma-inj₂ {σ} {τ} {ρ} f a df dg ctgL ctgR = 
      let (d-inj , eq) = DSemᵀ-inj₂ (f a) ((ctgL , ctgR))
      in begin
      to-witness df ctgR
      ≡⟨ cong (to-witness df) (sym eq) ⟩
      to-witness df (to-witness d-inj (ctgL , ctgR))
      ≡⟨ sym ( DSemᵀ-lemma-chain inj₂ f a d-inj df dg (ctgL , ctgR)) ⟩
      to-witness dg (ctgL , ctgR)
      ∎
open Inj public


module unpack-isInj where
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


module Case 
      {σ1 σ2 ρ τ : Typ Pr}
      (a : Rep ((σ1 :+ σ2) :* ρ))
      (l : Rep (σ1 :* ρ) → Rep τ) 
      (r : Rep (σ2 :* ρ) → Rep τ) 
  where
    open unpack-isInj
    private
      f : (Rep ((σ1 :+ σ2) :* ρ) ) → Rep τ
      f = λ (xs , a') → [ (λ x → l (x , a'))
                        , (λ x → r (x , a'))
                        ] xs

    DSemᵀ-lemma-case-inj₁ : (v : Rep σ1) → (fst a ≡ inj₁ v)
              → (df : Is-just $ DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a)
              → (dl : Is-just $ DSemᵀ {σ1 :* ρ} {τ} l (v , snd a))
              → (ctg : LinRepDense (D2τ' τ))
              → to-witness df ctg ≡ ((to-witness dl ctg .fst , zerovDense (D2τ' σ2)) , to-witness dl ctg .snd)
    DSemᵀ-lemma-case-inj₁  v w df dl ctg = ans
      where isLeft : Is-just (isInj₁ (fst a))
            isLeft rewrite w = Any.just tt
            rule = DSemᵀ-case-inj₁ a l r isLeft df ctg
            -- convincing agda that d-rule ≡ dl by propagating the fact that 'fst a ≡ inj₁ v'
            d-rule≡dl = DSemᵀ-lemma-cong-a l (v , snd a) (to-witness isLeft , snd a) (cong₂ _,_ (unpack-isInj₁ v (fst a) w isLeft) refl) dl (rule .fst) ctg
            ans : to-witness df ctg ≡ ((to-witness dl ctg .fst , zerovDense (D2τ' σ2)) , to-witness dl ctg .snd)
            ans rewrite snd rule rewrite d-rule≡dl = refl
            
    DSemᵀ-lemma-case-inj₂ : (v : Rep σ2) → (fst a ≡ inj₂ v)
              → (df : Is-just $ DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a)
              → (dr : Is-just $ DSemᵀ {σ2 :* ρ} {τ} r (v , snd a))
              → (ctg : LinRepDense (D2τ' τ))
              → to-witness df ctg ≡ (( zerovDense (D2τ' σ1) , to-witness dr ctg .fst) , to-witness dr ctg .snd)
    DSemᵀ-lemma-case-inj₂ v w df dr ctg = ans
      where isRight : Is-just (isInj₂ (fst a))
            isRight rewrite w = Any.just tt
            rule = DSemᵀ-case-inj₂ a l r isRight df ctg
            -- convincing agda that d-rule ≡ dl by propagating the fact that 'fst a ≡ inj₂ v'
            d-rule≡dl = DSemᵀ-lemma-cong-a r (v , snd a) (to-witness isRight , snd a) (cong₂ _,_ (unpack-isInj₂ v (fst a) w isRight) refl) dr (rule .fst) ctg
            ans : to-witness df ctg ≡ (( zerovDense (D2τ' σ1) , to-witness dr ctg .fst) , to-witness dr ctg .snd)
            ans rewrite snd rule rewrite d-rule≡dl = refl
open Case public
