module correctness.chad-equiv-dsem where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Agda.Builtin.Maybe using (just; nothing)

open import Data.List using (map; _∷_)
open import Data.Product using (_×_)
open import Function.Base using (_∘_; flip)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import spec
open import correctness.spec
open import correctness.dsem
open import correctness.lemmas

chad-preserves-≃₂ : {Γ : Env Pr} {τ : Typ Pr} 
                → (val : Val Pr Γ)
                  (evIn : LEtup (map D2τ' Γ) )
                  (ctg : LinRep (D2τ' τ))
                  (t : Term Pr Γ τ)
                → ctg ≃₁ (interp t val)
                → evIn ≃₂ val
                → LACMexec (interp (chad t) (primalVal val) .snd ctg .fst ) evIn ≃₂ val
chad-preserves-≃₂ _ evIn _ unit _ w2
  rewrite LACMexec-pure tt evIn = w2
chad-preserves-≃₂ {Γ} val evIn ctg (var x) w1 w2
  using idx ← convIdx D2τ' x
  rewrite LACMexec-add idx ctg evIn
  = let ≃₄evIn = ≃₁-and-≃₂-implies-≃₄ x ctg evIn val w1 w2 
        ≃₅evIn = ≃₁-and-≃₂-implies-≃₅ x ctg evIn val w1 w2 
    in addLEτ-preserves-≃₂ x ctg evIn val w2 ≃₄evIn ≃₅evIn
chad-preserves-≃₂ {Γ} val evIn (just (ctgL , ctgR)) (pair l r) w1 w2
  using m1 ← interp (chad l) (primalVal val) .snd ctgL .fst
  using m2 ← interp (chad r) (primalVal val) .snd ctgR .fst
  rewrite LACMexec-sequence m1 m2 evIn
  = let m3 =  (LACMexec (interp (chad l) (primalVal val) .snd ctgL .fst) evIn)
        ihl = chad-preserves-≃₂ val evIn ctgL l (w1 .fst) w2
    in chad-preserves-≃₂ val m3 ctgR r (w1 .snd) ihl
    
chad-preserves-≃₂ {Γ} val evIn ctg t w1 w2 = {!   !}

onehot-equiv-addLEτ-lemma : {Γ : Env Pr} {τ : Typ Pr}
    → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
    in (ctg : LinRep (D2τ' τ))
    → (evIn : LEtup (map D2τ' Γ) )
    → (idx , ctg) ≃₄ evIn
    → LEtup2EV (addLEτ idx' ctg evIn)
      ≡ (Etup2EV (onehot idx (sparse2dense ctg)) ev+ LEtup2EV evIn)
onehot-equiv-addLEτ-lemma {τ ∷ Γ}  Z      ctg (x , xs) w = cong₂ _,_ (plusv-equiv-plusvDense ctg x w) (sym (ev+zeroL' Etup-zerovDense-equiv-zero-EV))
onehot-equiv-addLEτ-lemma {τ ∷ Γ} (S idx) ctg (x , xs) w = cong₂ _,_ (sym plusvDense-zeroL') (onehot-equiv-addLEτ-lemma idx ctg xs w)

chad-equiv-DSemᵀ : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep σ)
                  (evIn : LEtup LΓ )
                  (ctg : LinRep (D2τ' τ))
                  (t : Term Pr Γ τ)
                → ctg  ≃₁ (interp t (Etup-to-val a))
                → evIn ≃₂ Etup-to-val a  
                → LEtup2EV {LΓ} (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst ) evIn)
                  ≡ Etup2EV {Γ} (DSemᵀ {σ} {τ} (interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV {LΓ} evIn
chad-equiv-DSemᵀ {Γ} a evIn ctg unit _ _ =
    begin
    LEtup2EV (LACMexec (interp (chad unit) (Etup-to-val-primal a) .snd ctg .fst) evIn)
      ≡⟨ cong LEtup2EV (LACMexec-pure tt evIn) ⟩
    LEtup2EV evIn
      ≡⟨ sym (ev+zeroL' DSemᵀ-lemma-ctg-zeroLEnv') ⟩
    Etup2EV (DSemᵀ (interp {Γ = Γ} unit ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
    ∎
chad-equiv-DSemᵀ {Γ} a evIn ctg (var x) w1 w2 =
  let idx = convIdx D2τ' x
  in begin
  LEtup2EV (LACMexec (interp (chad (var x)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ cong LEtup2EV (LACMexec-add idx ctg evIn) ⟩
  LEtup2EV (addLEτ idx ctg evIn)
    ≡⟨ onehot-equiv-addLEτ-lemma x ctg evIn (≃₁-and-≃₂-implies-≃₄ x ctg evIn (Etup-to-val a) w1 w2) ⟩
  Etup2EV (onehot x (sparse2dense ctg)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (sym (cong Etup2EV (DSemᵀ-var a x (sparse2dense ctg)))) ⟩
  Etup2EV (DSemᵀ (flip valprj x ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn nothing (pair {σ = σ} {τ = τ} l r) w1 w2 =
  let m1 = interp (chad l) (Etup-to-val-primal a) .snd (zerov (D2τ' σ) .fst) .fst
      m2 = interp (chad r) (Etup-to-val-primal a) .snd (zerov (D2τ' τ) .fst) .fst
      ihl = trans (chad-equiv-DSemᵀ a evIn (zerov (D2τ' σ) .fst) l (≃₁-zerov σ (interp l (Etup-to-val a))) w2)
                  (ev+zeroL' (DSemᵀ-lemma-ctg-zeroLEnv' {{zerov-equiv-zerovDense (D2τ' σ)}}))
      ihr = trans (chad-equiv-DSemᵀ a (LACMexec m1 evIn) (zerov (D2τ' τ) .fst) r (≃₁-zerov τ (interp r (Etup-to-val a))) {! w2  !})
                  (ev+zeroL' (DSemᵀ-lemma-ctg-zeroLEnv' {{zerov-equiv-zerovDense (D2τ' τ)}}))
  in begin
  LEtup2EV (LACMexec (interp (chad (pair l r)) (Etup-to-val-primal a) .snd nothing .fst) evIn)
    ≡⟨ cong LEtup2EV (LACMexec-sequence m1 m2 evIn) ⟩
  LEtup2EV (LACMexec m2 (LACMexec m1 evIn))
    ≡⟨ trans ihr ihl ⟩
  LEtup2EV evIn 
    ≡⟨ sym (ev+zeroL' DSemᵀ-lemma-ctg-zeroLEnv') ⟩
  Etup2EV (DSemᵀ (interp (pair l r) ∘ Etup-to-val) a (zerovDense (D2τ' σ) , zerovDense (D2τ' τ))) ev+ LEtup2EV evIn
  ∎ 
chad-equiv-DSemᵀ {Γ} a evIn ctg t _ _ = {!   !}