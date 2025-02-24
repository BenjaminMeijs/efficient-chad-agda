{-# OPTIONS --allow-unsolved-metas #-}
module correctness.lemmas.dsem-ev-lemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_×_; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Maybe using (Maybe; Is-just; to-witness; just; nothing; maybe; from-just)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Maybe.Relation.Unary.Any as Any
open import Function.Bundles using (_⇔_;  mk⇔)
open import Function.Base using (_$_; _∘_; id; case_of_; flip)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import correctness.lemmas.environment-vector-lemmas
open import correctness.lemmas.dsem-lemmas

open import spec
open import correctness.spec
open import correctness.dsem
import spec.LACM as LACM

private
    trans₂ : {A : Set} {x y a b : A} → x ≡ y → x ≡ a → y ≡ b → a ≡ b
    trans₂ refl refl refl = refl

onehot-equiv-addLEτ-lemma : {Γ : Env Pr} {τ : Typ Pr}
    → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
    in (ctg : LinRep (D2τ' τ))
    → (evIn : LEtup (map D2τ' Γ) )
    → Compatible-idx-LEtup (idx , ctg) evIn
    → LEtup2EV (addLEτ idx' ctg evIn)
      ≡ (Etup2EV (onehot idx (sparse2dense ctg)) ev+ LEtup2EV evIn)
onehot-equiv-addLEτ-lemma {τ ∷ Γ}  Z      ctg (x , xs) w = cong₂ _,_ (plusv-equiv-plusvDense ctg x w) (sym (ev+zeroL' Etup-zerovDense-equiv-zero-EV))
onehot-equiv-addLEτ-lemma {τ ∷ Γ} (S idx) ctg (x , xs) w = cong₂ _,_ (sym plusvDense-zeroL') (onehot-equiv-addLEτ-lemma idx ctg xs w)

-- module Zero where
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
