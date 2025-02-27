{-# OPTIONS --allow-unsolved-metas #-}
module correctness.lemmas.dsem-ev-lemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_×_; uncurry; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Maybe using (Maybe; Is-just; to-witness; just; nothing; maybe; from-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; _+_)
import Data.Maybe.Relation.Unary.Any as Any
open import Function.Bundles using (_⇔_;  mk⇔; Equivalence)
open import Function.Base using (_$_; _∘_; id; case_of_; flip)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import correctness.lemmas.LinRepDense-is-comm-monoid
open import correctness.lemmas.dsem-lemmas

open import spec
open import correctness.spec
open import correctness.lemmas.value-compatibility-lemmas using (≃τ-and-≃Γ-implies-Compatible-idx-LEtup)
open import correctness.dsem
import spec.LACM as LACM

private
    trans₂ : {A : Set} {x y a b : A} → x ≡ y → x ≡ a → y ≡ b → a ≡ b
    trans₂ refl refl refl = refl

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

module Ev-zero {Γ : Env Pr} {τ : Typ Pr} { f : Rep (Etup Pr Γ)  →  Rep τ } { a : Rep (Etup Pr Γ) }
    { ctg : LinRepDense (D2τ' τ) }
    {{ w : ctg ≡ zerovDense (D2τ' τ)}}
    ( df : Is-just (DSemᵀ {Etup Pr Γ} {τ} f a) )
    where

    DSemᵀ-ev-lemma-ctg-zero' : Etup2EV (to-witness df ctg) ≡ zero-EV (map D2τ' Γ)
    DSemᵀ-ev-lemma-ctg-zero'
      = trans (cong (Etup2EV ∘ to-witness df) w) 
              (trans (cong Etup2EV (Zero.DSemᵀ-lemma-ctg-zero' df)) Etup-zerovDense-equiv-zero-EV)

    DSemᵀ-ev-lemma-ctg-zero-evIn' : { evIn : LEtup (map D2τ' Γ)  }
                    → LEtup2EV {map D2τ' Γ} evIn 
                      ≡ Etup2EV (to-witness df ctg) ev+ LEtup2EV {map D2τ' Γ} evIn
    DSemᵀ-ev-lemma-ctg-zero-evIn' {evIn} = sym (ev+zeroL' DSemᵀ-ev-lemma-ctg-zero')

module Ev-pair {Γ : Env Pr} {τ1 τ2 : Typ Pr } (f : Rep (Etup Pr Γ) →  Rep τ1) (g : Rep (Etup Pr Γ) →  Rep τ2) (a : Rep (Etup Pr Γ))
            (ctg-f : LinRepDense (D2τ' τ1)) (ctg-g : LinRepDense (D2τ' τ2))
            (df : Is-just (DSemᵀ {Etup Pr Γ} {τ1} f a))
            (dg : Is-just (DSemᵀ {Etup Pr Γ} {τ2} g a))
            (dh : Is-just (DSemᵀ {Etup Pr Γ} {τ1 :* τ2} (λ e → (f e , g e) ) a))
    where
    private
      h : Rep (Etup Pr Γ) → Rep (τ1 :* τ2)
      h e = (f e , g e)

    DSemᵀ-ev-lemma-pair : (Etup2EV ((to-witness df) ctg-f) ev+ Etup2EV ((to-witness dg) ctg-g)) 
                           ≡ Etup2EV ((to-witness dh) (ctg-f , ctg-g))
    DSemᵀ-ev-lemma-pair 
      = let rule = Pair.DSemᵀ-lemma-pair f g a dh df dg ctg-f ctg-g
        in sym (trans₂ (cong Etup2EV rule) refl (plusvDense-equiv-ev+ (to-witness df ctg-f) (to-witness dg ctg-g)))

DSemᵀ-lemma-interp-let : {Γ : Env Pr} {σ τ : Typ Pr}
  → (a : Rep (Etup Pr Γ))
  → (ctg : LinRepDense (D2τ' τ))
  → (rhs : Term Pr Γ σ)
  → (body : Term Pr (σ ∷ Γ) τ)
  → (d-let : Is-just $ DSemᵀ {σ = Etup Pr Γ} {τ = τ} (interp (let' rhs body) ∘ Etup-to-val) a )
  → (d-rhs : Is-just $ DSemᵀ {σ = Etup Pr Γ } {τ = σ} (interp rhs ∘ Etup-to-val) a )
  → (d-body : Is-just $ DSemᵀ {σ = σ :* (Etup Pr Γ)} {τ = τ} (interp body ∘ Etup-to-val) (interp rhs (Etup-to-val a) , a) )
  → let ctg-body = to-witness d-body ctg
    in (Etup2EV (to-witness d-rhs (ctg-body .fst)) ev+ Etup2EV (ctg-body .snd))
       ≡ Etup2EV (to-witness d-let ctg)
DSemᵀ-lemma-interp-let {Γ} {σ} {τ} a ctg rhs body d-let d-rhs d-body =
  let ctg-body = to-witness d-body ctg
      g : (env : Rep (Etup Pr Γ)) → Rep σ × Rep (Etup Pr Γ) -- Note that g constructs a pair, thus we can use the pair rule on it
      g = (λ env → (interp rhs (Etup-to-val env) , env))
      dg : Is-just (DSemᵀ {Etup Pr Γ } {σ :* (Etup Pr Γ)} g a)
      dg = Equivalence.to (DSemᵀ-exists-chain (interp body ∘ Etup-to-val) g a) d-let .fst
      (d-id , eq1) = DSemᵀ-identity a (snd ctg-body)
  in begin
  Etup2EV (to-witness d-rhs (fst ctg-body)) ev+ Etup2EV (snd ctg-body)
    ≡⟨ ev+congR (cong Etup2EV (sym eq1)) ⟩
  Etup2EV (to-witness d-rhs (fst ctg-body)) ev+ Etup2EV (to-witness d-id (snd ctg-body))
    ≡⟨ Ev-pair.DSemᵀ-ev-lemma-pair (interp rhs ∘ Etup-to-val) id a (fst ctg-body) (snd ctg-body) d-rhs d-id dg ⟩
  Etup2EV (to-witness dg ctg-body)
    ≡⟨ cong Etup2EV (sym (DSemᵀ-chain _ g a d-let d-body dg ctg)) ⟩
  Etup2EV (to-witness d-let ctg)
  ∎
  
module Ev-case {Γ : Env Pr} {σ τ ρ : Typ Pr}
  (a : Rep (Etup Pr Γ))
  (e : Term Pr Γ (σ :+ τ))
  (l : Term Pr (σ ∷ Γ) ρ)
  (r : Term Pr (τ ∷ Γ) ρ)
  (de : Is-just $ DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a)
  (d-case : Is-just $ DSemᵀ {Etup Pr Γ} {ρ} (interp (case' e l r) ∘ Etup-to-val) a)
  (ctg : LinRepDense (D2τ' ρ))
  where

  private
    -- This proof is used within the poslution DSemᵀ-extensionality to simplify interp (case' e l r) (Etup-to-val y)
    -- The simplification is to ignore the costs of eval
    interp-case-extensionality : 
            (y : Rep (Etup Pr Γ)) 
          → let f = λ (zs , a) → [ (λ z → interp l (Etup-to-val (z , a))) 
                                  , (λ z → interp r (Etup-to-val (z , a)))
                                  ] zs
                g = λ a → ( interp e (Etup-to-val a) , a)
          in (f ∘ g) y ≡ interp (case' e l r) (Etup-to-val y)
    interp-case-extensionality y with interp e (Etup-to-val y)
    ... | inj₁ _  = refl
    ... | inj₂ _  = refl

    lemma-cong-DSemᵀ-case : {σ1 σ2 ρ τ : Typ Pr}
              → (a : Rep ρ)
              → (c : Rep ρ → Rep (σ1 :+ σ2))
              → (v : Rep (σ1 :+ σ2)) (w : c a ≡ v )
              → (l : Rep σ1 → Rep ρ → Rep τ) 
              → (r : Rep σ2 → Rep ρ → Rep τ) 
              → (dc : Is-just $ DSemᵀ {ρ} {σ1 :+ σ2} c a)
              → (ctg : LinRepDense (D2τ' τ))
              → let f = case c a of [ l , r ]
              in case v of
                  [ (λ v → (dl : Is-just $ DSemᵀ {ρ} {τ} (l v) a )
                         → Σ (Is-just $ DSemᵀ {ρ} {τ} f a)
                             ( λ df → to-witness df ctg ≡ to-witness dl ctg))
                  , (λ v → (dr : Is-just $ DSemᵀ {ρ} {τ} (r v) a )
                         → Σ (Is-just $ DSemᵀ {ρ} {τ} f a)
                             ( λ df → to-witness df ctg ≡ to-witness dr ctg))
                  ]
    lemma-cong-DSemᵀ-case a c v refl = DSemᵀ-case a c


    DSemᵀ-lemma-interp-case-left : (x : Rep σ) → (interp-e-val≡inj-x : interp e (Etup-to-val a) ≡ inj₁ x)
             → (dl : Is-just $ DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a))
             → Etup2EV (to-witness d-case ctg)
               ≡ (Etup2EV (to-witness de (to-witness dl ctg .fst , zerovDense (D2τ' τ))) ev+ Etup2EV (to-witness dl ctg .snd))
    DSemᵀ-lemma-interp-case-left x interp-e-val≡inj-x dl
      -- using foo ← DSemᵀ-exists-evaluation-f (interp (case' e l r) ∘ Etup-to-val) (fst ∘ (flip eval (case' e l r)) ∘ Etup-to-val) refl a d-case ctg
      -- using bar ← Equivalence.to (DSemᵀ-exists-chain {τ2 = ρ :* Inte} fst ((flip eval (case' e l r)) ∘ Etup-to-val) a) (fst foo)
      -- using eq1 ← DSemᵀ-chain {τ2 = ρ :* Inte} fst ((flip eval (case' e l r)) ∘ Etup-to-val) a (fst foo) (snd bar) (fst bar) ctg
      -- rewrite snd foo
      -- rewrite eq1
      = let -- aaaaaaa = {!   !}
            Temp1 : Rep (ρ :* Inte)
            Temp1 = ((λ { (inj₁ x) → eval (push x (Etup-to-val a)) l .fst , one + eval (Etup-to-val a) e .snd + eval (push x (Etup-to-val a)) l .snd
                        ; (inj₂ y) → eval (push y (Etup-to-val a)) r .fst , one + eval (Etup-to-val a) e .snd + eval (push y (Etup-to-val a)) r .snd
                    }) (eval (Etup-to-val a) e .fst))
            Temp2 : Rep (ρ :* Inte)
            Temp2 = eval (push x (Etup-to-val a)) l .fst , one + eval (Etup-to-val a) e .snd + eval (push x (Etup-to-val a)) l .snd
            TempL = λ v' a' → interp l (Etup-to-val (v' , a' )) , one + eval (Etup-to-val a') e .snd + eval (push v' (Etup-to-val a')) l .snd
            TempR = λ v' a' → interp r (Etup-to-val (v' , a' )) , one + eval (Etup-to-val a') e .snd + eval (push v' (Etup-to-val a')) r .snd
            foo = DSemᵀ-exists-evaluation-f (interp (case' e l r) ∘ Etup-to-val) (fst ∘ (flip eval (case' e l r)) ∘ Etup-to-val) refl a d-case ctg
            bar = Equivalence.to (DSemᵀ-exists-chain {τ2 = ρ :* Inte} fst ((flip eval (case' e l r)) ∘ Etup-to-val) a) (fst foo)
            eq1 = DSemᵀ-chain {τ2 = ρ :* Inte} fst ((flip eval (case' e l r)) ∘ Etup-to-val) a (fst foo) (snd bar) (fst bar) ctg
            baz = DSemᵀ-fst Temp1 ctg
            bix = {!   !}
            biz = lemma-cong-DSemᵀ-case {τ = ρ :* Inte} a (interp e ∘ Etup-to-val) (inj₁ x) interp-e-val≡inj-x TempL TempR de (ctg , zerovDense LUn) bix

            -- bbbbbbb = {! snd biz  !}
            -- ccccccc = {! fst bar  !}
        in begin
        Etup2EV (to-witness d-case ctg)
          ≡⟨ cong Etup2EV (snd foo) ⟩
        Etup2EV (to-witness (fst foo) ctg)
          ≡⟨ cong Etup2EV eq1 ⟩
        Etup2EV (to-witness (fst bar) (to-witness (snd bar) ctg))
          ≡⟨ cong Etup2EV (cong (to-witness (fst bar)) (trans (DSemᵀ-extensionality _ _ (λ _ → refl) Temp1 (snd bar) (fst baz) ctg) (snd baz))) ⟩
        Etup2EV (to-witness (fst bar) (ctg , zerovDense LUn))
          ≡⟨ cong Etup2EV (DSemᵀ-extensionality _ _ ext-proof a (fst bar) bix (ctg , tt)) ⟩
        Etup2EV (to-witness bix ((ctg , zerovDense LUn)))
          ≡⟨ {!   !} ⟩
        (Etup2EV (to-witness de (to-witness dl ctg .fst , zerovDense (D2τ' τ))) ev+ Etup2EV (to-witness dl ctg .snd))
        ∎
        where ext-proof : (x₁ : Rep (Etup Pr Γ)) → eval (Etup-to-val x₁) (case' e l r) ≡ (interp l (Etup-to-val (x , x₁)) , one + eval (Etup-to-val x₁) e .snd + eval (push x (Etup-to-val x₁)) l .snd)
              ext-proof a' with interp e (Etup-to-val a') in eq2
              ... | inj₁ x = {!   !}
              ... | inj₂ y = {!   !}

  -- DSemᵀ-lemma-interp-case : 
  --     [ (λ x  → (dl : Is-just $ DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a))
  --             → let ctg-l = to-witness dl ctg
  --             in Etup2EV (to-witness de ( ctg-l .fst , zerovDense (D2τ' τ))) ev+ Etup2EV (ctg-l .snd)
  --               ≡ Etup2EV (to-witness d-case ctg))
  --     , (λ x  → (dr : Is-just $ DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a))
  --             → let ctg-r = to-witness dr ctg
  --             in Etup2EV (to-witness de (zerovDense (D2τ' σ) , ctg-r .fst)) ev+ Etup2EV (ctg-r .snd)
  --               ≡ Etup2EV (to-witness d-case ctg))
  --     ] (interp e (Etup-to-val a))
  -- -- This proof consists of two 'mirror' cases (inj₁ and inj₂)
  -- -- For the inj₁ case we use ≡-reasoning since its verbosity makes clear how the proof works.
  -- -- For the inj­₂ case we use rewrites for brevity
  -- DSemᵀ-lemma-interp-case 
  --   with interp e (Etup-to-val a) in interp-e-val≡inj-x  
  -- ... | (inj₁ x) = sym ∘ DSemᵀ-lemma-interp-case-left x interp-e-val≡inj-x
  -- ... | (inj₂ x) = {!   !}


  -- -- -- This lemma combines DSemᵀ-lemma-interp-case together with a cong on 'interp e (Etup-to-val a)'
  -- -- -- This is convenient, as this lemma is used when we've made a case distinction on 'interp e (Etup-to-val a)', and thus this disctinction needs to be propagated
  -- DSemᵀ-lemma-interp-case-cong : 
  --   (c : Rep (σ :+ τ)) → (w : interp e (Etup-to-val a) ≡ c)
  --   → [ (λ x  → (dl : Is-just $ DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a))
  --             → let ctg-l = to-witness dl ctg
  --             in Etup2EV (to-witness de ( ctg-l .fst , zerovDense (D2τ' τ))) ev+ Etup2EV (ctg-l .snd)
  --               ≡ Etup2EV (to-witness d-case ctg))
  --     , (λ x  → (dr : Is-just $ DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a))
  --             → let ctg-r = to-witness dr ctg
  --             in Etup2EV (to-witness de (zerovDense (D2τ' σ) , ctg-r .fst)) ev+ Etup2EV (ctg-r .snd)
  --               ≡ Etup2EV (to-witness d-case ctg))
  --     ] c
  -- DSemᵀ-lemma-interp-case-cong c refl = DSemᵀ-lemma-interp-case




    -- let Temp1 = ((one + eval (Etup-to-val a) e .snd) + eval (push x (Etup-to-val a)) l .snd)
    --     Temp2 =  ( λ α → (λ { (inj₁ x) → eval (push x (Etup-to-val a)) l .fst , one + eval (Etup-to-val a) e .snd + eval (push x (Etup-to-val a)) l .snd
    --                  ; (inj₂ y) → eval (push y (Etup-to-val a)) r .fst , one + eval (Etup-to-val a) e .snd + eval (push y (Etup-to-val a)) r .snd })
    --               α)
    --     (d-foo , eq1) = DSemᵀ-exists-evaluation-f (interp (case' e l r) ∘ Etup-to-val) (fst ∘ (flip eval (case' e l r)) ∘ Etup-to-val) refl a d-case ctg
    --     ctg-l = to-witness dl ctg
    --     ctg-e = to-witness de (ctg-l .fst , zerovDense (D2τ' τ))
    --     (d-bar , d-baz) = Equivalence.to (DSemᵀ-exists-chain {τ2 = ρ :* Inte} fst ((flip eval (case' e l r)) ∘ Etup-to-val) a) d-foo
    --     foobar = DSemᵀ-exists-evaluation-a fst _ ( interp l (Etup-to-val (x , a)) , Temp1) (cong Temp2 (interp-e-val≡inj-x)) d-baz ctg
    -- in begin
    -- Etup2EV ctg-e ev+ Etup2EV (ctg-l .snd)
    -- ≡⟨ {!   !} ⟩
    -- {! d-baz  !}
    -- ≡⟨ {!   !} ⟩
    -- Etup2EV (to-witness d-bar (to-witness d-baz ctg))
    -- ≡⟨ cong Etup2EV (sym (DSemᵀ-chain {τ2 = ρ :* Inte} fst ((flip eval (case' e l r)) ∘ Etup-to-val) a d-foo d-baz d-bar ctg)) ⟩
    -- Etup2EV (to-witness d-foo ctg)
    -- ≡⟨ cong Etup2EV (sym eq1) ⟩
    -- Etup2EV (to-witness d-case ctg)
    -- ∎
-- DSemᵀ-lemma-interp-case {Γ} {σ} {τ} {ρ} a e l r de d-case ctg | (inj₂ x)
--   = {!  !}
  -- let foo = {! Equivalence.to (DSemᵀ-exists-chain f g a) d-f∘g   !}
  --     ctg-l = to-witness dl ctg
  --     ctg-e = to-witness de (ctg-l .fst , zerovDense (D2τ' τ))

  --     d-f∘g = DSemᵀ-exists-extensionality (interp (case' e l r) ∘ Etup-to-val) (f ∘ g) (sym ∘ interp-case-extensionality e l r) a d-case
  --     (d-g , d-f) = Equivalence.to (DSemᵀ-exists-chain {τ2 = (σ :+ τ) :* Etup Pr Γ} f g a) d-f∘g 
  --     -- d-id = DSemᵀ-identity a (zerovDense (D2τ' (Etup Pr Γ))) .fst

  --     -- d-h = Pair.DSemᵀ-exists-lemma-pair₂ (interp e ∘ Etup-to-val) id a (de , d-id)
  -- in begin
  -- Etup2EV ctg-e ev+ Etup2EV (ctg-l .snd)
  --   ≡⟨ {!   !} ⟩
  -- {!   !}
  --   ≡⟨ {!   !} ⟩
  -- Etup2EV (to-witness d-g (to-witness d-f ctg))
  --   ≡⟨ cong Etup2EV (sym (DSemᵀ-chain f g a d-f∘g d-f d-g ctg)) ⟩
  -- Etup2EV (to-witness d-f∘g ctg)
  --   ≡⟨ cong Etup2EV (DSemᵀ-extensionality {Etup Pr Γ} {ρ} (f ∘ g) (interp (case' e l r) ∘ Etup-to-val) (interp-case-extensionality e l r) a d-f∘g d-case ctg) ⟩
  -- Etup2EV (to-witness d-case ctg)
  -- ∎
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
-- DSemᵀ-lemma-interp-case {Γ} {σ} {τ} {ρ} a e l r de d-case ctg | (inj₂ x)
--   = {!  !}
  -- using d-f∘g ← DSemᵀ-exists-extensionality (interp (case' e l r) ∘ Etup-to-val) (f ∘ g) (sym ∘ interp-case-extensionality e l r) a d-case
  -- rewrite DSemᵀ-extensionality {Etup Pr Γ} {ρ} (f ∘ g) (interp (case' e l r) ∘ Etup-to-val) (interp-case-extensionality e l r) a d-f∘g d-case ctg
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