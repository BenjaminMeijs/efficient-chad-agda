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
open import Function.Base using (_$_; _∘_; id; case_of_; flip)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)
open import Relation.Nullary.Negation using (¬_)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import correctness.lemmas.LinRepDense-is-comm-monoid
open import correctness.lemmas.value-compatibility-lemmas

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

module Ev-zero {Γ : Env Pr} {τ : Typ Pr} { f : Rep (ET Pr Γ)  →  Rep τ } { a : Rep (ET Pr Γ) }
    { ctg : LinRepDense (D2τ' τ) }
    {{ w : ctg ≡ zerovDense (D2τ' τ)}}
    ( df : Is-just (DSemᵀ {ET Pr Γ} {τ} f a) )
    where

    DSemᵀ-ev-lemma-ctg-zero' : LRD-ET2LETd (to-witness df ctg) ≡ zero-LETd (map D2τ' Γ)
    DSemᵀ-ev-lemma-ctg-zero'
      = trans (cong (LRD-ET2LETd ∘ to-witness df) w) 
              (trans (cong LRD-ET2LETd (DSemᵀ-lemma-ctg-zero' df)) ET-zerovDense-equiv-zero-LETd)

    DSemᵀ-ev-lemma-ctg-zero-evIn' : { evIn : LETs (map D2τ' Γ)  }
                    → LETs2d {map D2τ' Γ} evIn 
                      ≡ LRD-ET2LETd (to-witness df ctg) ev+ LETs2d {map D2τ' Γ} evIn
    DSemᵀ-ev-lemma-ctg-zero-evIn' {evIn} = sym (ev+zeroL' DSemᵀ-ev-lemma-ctg-zero')
open Ev-zero public

module Onehot where
    private
        onehot-equiv-addLEτ : {Γ : Env Pr} {τ : Typ Pr}
            → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
            in (ctg : LinRep (D2τ' τ))
            → (evIn : LETs (map D2τ' Γ) )
            → Compatible-idx-LETs (idx , ctg) evIn
            → LETs2d (addLEτ idx' ctg evIn)
              ≡ (LRD-ET2LETd (onehot idx (sparse2dense ctg)) ev+ LETs2d evIn)
        onehot-equiv-addLEτ {τ ∷ Γ}  Z      ctg (x , xs) w = cong₂ _,_ (plusv-equiv-plusvDense ctg x w) (sym (ev+zeroL' ET-zerovDense-equiv-zero-LETd))
        onehot-equiv-addLEτ {τ ∷ Γ} (S idx) ctg (x , xs) w = cong₂ _,_ (sym plusvDense-zeroL') (onehot-equiv-addLEτ idx ctg xs w)

    onehot-equiv-addLEτ-lemma : {Γ : Env Pr} {τ : Typ Pr}
        → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
        in (ctg : LinRep (D2τ' τ))
        → (evIn : LETs (map D2τ' Γ) )
        → (val : Val Pr Γ) → (ctg ≃τ valprj val idx) → (evIn ≃Γ val)
        → LETs2d (addLEτ idx' ctg evIn)
          ≡ (LRD-ET2LETd (onehot idx (sparse2dense ctg)) ev+ LETs2d evIn)
    onehot-equiv-addLEτ-lemma idx ctg evIn val ~τ ~Γ = onehot-equiv-addLEτ idx ctg evIn (≃τ-and-≃Γ-implies-Compatible-idx-LETs idx ctg evIn val ~τ ~Γ)
open Onehot public

module Pair { σ τ1 τ2 : Typ Pr } (f : Rep σ →  Rep τ1) (g : Rep σ →  Rep τ2) (a : Rep σ) where
    -- helper functions
    private
      h : Rep σ → Rep (τ1 :* τ2)
      h e = (f e , g e)

    DSemᵀ-exists-lemma-pair₁ : 
        Is-just (DSemᵀ {σ} {τ1 :* τ2} h a) 
        → ( Is-just (DSemᵀ {σ} {τ1} f a) × Is-just (DSemᵀ {σ} {τ2} g a))
    DSemᵀ-exists-lemma-pair₁ = Equivalence.to $ DSemᵀ-exists-pair f g a

    DSemᵀ-exists-lemma-pair₂ :
        ( Is-just (DSemᵀ {σ} {τ1} f a) × Is-just (DSemᵀ {σ} {τ2} g a))
        → Is-just (DSemᵀ {σ} {τ1 :* τ2} h a) 
    DSemᵀ-exists-lemma-pair₂ = Equivalence.from $ DSemᵀ-exists-pair f g a

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
        in trans ((DSemᵀ-pair f g a dh df dg ctg-f ctg-g))
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
        in trans ((DSemᵀ-pair f g a dh df dg ctg-f ctg-g))
                 (plusvDense-zeroL' {{DSemᵀ-lemma-ctg-zero' {{zerov-equiv-zerovDense (D2τ' τ1)}} df}})
open Pair public

module Ev-pair {Γ : Env Pr} {τ1 τ2 : Typ Pr } (f : Rep (ET Pr Γ) →  Rep τ1) (g : Rep (ET Pr Γ) →  Rep τ2) (a : Rep (ET Pr Γ))
            (ctg-f : LinRepDense (D2τ' τ1)) (ctg-g : LinRepDense (D2τ' τ2))
            (df : Is-just (DSemᵀ {ET Pr Γ} {τ1} f a))
            (dg : Is-just (DSemᵀ {ET Pr Γ} {τ2} g a))
            (dh : Is-just (DSemᵀ {ET Pr Γ} {τ1 :* τ2} (λ e → (f e , g e) ) a))
    where
    private
      h : Rep (ET Pr Γ) → Rep (τ1 :* τ2)
      h e = (f e , g e)

    DSemᵀ-ev-lemma-pair : (LRD-ET2LETd (to-witness df ctg-f) ev+ LRD-ET2LETd (to-witness dg ctg-g)) 
                           ≡ LRD-ET2LETd (to-witness dh (ctg-f , ctg-g))
    DSemᵀ-ev-lemma-pair 
      = let rule = DSemᵀ-pair f g a dh df dg ctg-f ctg-g
        in sym (trans₂ (cong LRD-ET2LETd rule) refl (plusvDense-equiv-ev+ (to-witness df ctg-f) (to-witness dg ctg-g)))
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


module apply-cong[,] where
    apply-cong[-,] : { A B : Set } 
            → (l : A → Set) (r : B → Set) (cond : A ⊎ B) 
            → [ l , r ] cond
            → (x : A) → (inj₁ x ≡ cond)
            → l x
    apply-cong[-,] {A} {B} _ _ (inj₁ _) f _ refl = f

    apply-cong[,-] : { A B : Set } 
            → (l : A → Set) (r : B → Set) (cond : A ⊎ B) 
            → [ l , r ] cond
            → (x : B) → (inj₂ x ≡ cond)
            → r x
    apply-cong[,-] {A} {B} _ _ (inj₂ _) f _ refl = f


module Case 
      {σ1 σ2 ρ τ : Typ Pr}
      (a : Rep ((σ1 :+ σ2) :* ρ))
      (l : Rep (σ1 :* ρ) → Rep τ) 
      (r : Rep (σ2 :* ρ) → Rep τ) 
      (df : Is-just $ DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} (λ (xs , a') → [ (λ x → l (x , a')) , (λ x → r (x , a')) ] xs) a)
      (ctg : LinRepDense (D2τ' τ))
  where
    open apply-cong[,]
    private
      f : (Rep ((σ1 :+ σ2) :* ρ) ) → Rep τ
      f = λ (xs , a') → [ (λ x → l (x , a'))
                        , (λ x → r (x , a'))
                        ] xs

      Fl : (v : Rep σ1) → Set
      Fr : (v : Rep σ2) → Set
      Fl = (λ v → Σ (Is-just $ DSemᵀ {σ1 :* ρ} {τ} l (v , snd a)) ( λ dl → to-witness df ctg ≡ ((to-witness dl ctg .fst , zerovDense (D2τ' σ2)) , to-witness dl ctg .snd))) 
      Fr = (λ v → Σ (Is-just $ DSemᵀ {σ2 :* ρ} {τ} r (v , snd a)) ( λ dr → to-witness df ctg ≡ ((zerovDense (D2τ' σ1) , to-witness dr ctg .fst) , to-witness dr ctg .snd))) 

      case-rule : [ Fl , Fr ] (a . fst)
      case-rule = DSemᵀ-case {σ1} {σ2} {ρ} {τ} a l r df ctg

      apply₁-case-rule : (x : Rep σ1) → inj₁ x ≡ fst a → Fl x
      apply₁-case-rule = apply-cong[-,] Fl Fr (fst a) case-rule

      apply₂-case-rule : (x : Rep σ2) → inj₂ x ≡ fst a → Fr x
      apply₂-case-rule = apply-cong[,-] Fl Fr (fst a) case-rule

    DSemᵀ-lemma-case-inj₁ : (v : Rep σ1) → (fst a ≡ inj₁ v)
              → (dl : Is-just $ DSemᵀ {σ1 :* ρ} {τ} l (v , snd a))
              → to-witness df ctg ≡ ((to-witness dl ctg .fst , zerovDense (D2τ' σ2)) , to-witness dl ctg .snd)
    DSemᵀ-lemma-case-inj₁  v eq1 dl = ans
      where rule = apply₁-case-rule v (sym eq1)
            dl2 = fst rule
            dl≡dl2 : to-witness dl ctg ≡ to-witness dl2 ctg
            dl≡dl2 = DSemᵀ-extensionality _ _ (λ _ → refl) (v , snd a) dl dl2 ctg
            ans : to-witness df ctg ≡ ((to-witness dl ctg .fst , zerovDense (D2τ' σ2)) , to-witness dl ctg .snd)
            ans rewrite dl≡dl2 = snd rule

    DSemᵀ-lemma-case-inj₂ : (v : Rep σ2) → (fst a ≡ inj₂ v)
              → (dr : Is-just $ DSemᵀ {σ2 :* ρ} {τ} r (v , snd a))
              → to-witness df ctg ≡ ((zerovDense (D2τ' σ1), to-witness dr ctg .fst) , to-witness dr ctg .snd)
    DSemᵀ-lemma-case-inj₂ v eq1 dr = ans
      where rule = apply₂-case-rule v (sym eq1)
            dr2 = fst rule -- fst rule
            dr≡dr2 : to-witness dr ctg ≡ to-witness dr2 ctg
            dr≡dr2 = DSemᵀ-extensionality _ _ (λ _ → refl) (v , snd a) dr dr2 ctg
            ans : to-witness df ctg ≡ ((zerovDense (D2τ' σ1), to-witness dr ctg .fst) , to-witness dr ctg .snd)
            ans rewrite dr≡dr2 = rule .snd

open Case public

module Exists-Case
    {σ1 σ2 ρ τ : Typ Pr}
    (a : Rep ((σ1 :+ σ2) :* ρ))
    (l : Rep (σ1 :* ρ) → Rep τ) 
    (r : Rep (σ2 :* ρ) → Rep τ) 
  where
    private
      f : (Rep ((σ1 :+ σ2) :* ρ) ) → Rep τ
      f = λ (xs , a') → [ (λ x → l (x , a'))
                        , (λ x → r (x , a'))
                        ] xs

      Fl : (v : Rep σ1) → Set
      Fr : (v : Rep σ2) → Set
      Fl = (λ v → (Is-just $ DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a) ⇔ (Is-just $ DSemᵀ {σ1 :* ρ} {τ} l (v , snd a)))
      Fr = (λ v → (Is-just $ DSemᵀ {(σ1 :+ σ2) :* ρ} {τ} f a) ⇔ (Is-just $ DSemᵀ {σ2 :* ρ} {τ} r (v , snd a)))

      case-rule : [ Fl , Fr ] (a . fst)
      case-rule = DSemᵀ-exists-case {σ1} {σ2} {ρ} {τ} a l r

    DSemᵀ-exists-lemma-case-inj₁ : (v : Rep σ1) → (fst a ≡ inj₁ v) → Fl v
    DSemᵀ-exists-lemma-case-inj₁ v refl = case-rule

    DSemᵀ-exists-lemma-case-inj₂ : (v : Rep σ2) → (fst a ≡ inj₂ v) → Fr v
    DSemᵀ-exists-lemma-case-inj₂ v refl = case-rule

open Exists-Case public