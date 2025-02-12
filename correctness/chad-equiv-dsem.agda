module correctness.chad-equiv-dsem where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Agda.Builtin.Maybe using (just; nothing)

open import Data.Integer using (ℤ)
open import Data.List using (map; _∷_; [])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import Function.Base using (_∘_; flip)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import spec
import spec.LACM as LACM
open import correctness.spec
open import correctness.dsem
open import correctness.lemmas
open import chad-preserves-primal

dprim'-preserves-≃₁ : {Γ : Env Pr} {σ τ : Typ Pr}
      (val : Val Pr Γ) (ctg : LinRep (D2τ' τ)) (op : Primop Pr σ τ) (t : Term Pr Γ σ) 
    → ctg ≃₁ evalprim op (interp t val)
    → let d-op-env = push ctg (push (primal σ (interp t val)) empty)
      in interp (dprim' op) d-op-env ≃₁ interp t val
dprim'-preserves-≃₁ val ctg ADD t w = tt , tt
dprim'-preserves-≃₁ val ctg MUL t w = tt , tt
dprim'-preserves-≃₁ val ctg NEG t w = tt
dprim'-preserves-≃₁ val ctg (LIT x) t w = tt
dprim'-preserves-≃₁ val ctg IADD t w = tt , tt
dprim'-preserves-≃₁ val ctg IMUL t w = tt , tt
dprim'-preserves-≃₁ val ctg INEG t w = tt
dprim'-preserves-≃₁ val ctg SIGN t w = tt

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
chad-preserves-≃₂ {Γ} val evIn nothing (pair {σ = σ} {τ = τ} l r) w1 w2
  using m1 ← interp (chad l) (primalVal val) .snd (zerov (D2τ' σ) .fst) .fst
  using m2 ← interp (chad r) (primalVal val) .snd (zerov (D2τ' τ) .fst) .fst
  rewrite LACMexec-sequence m1 m2 evIn
  = let ihl = chad-preserves-≃₂ val evIn (zerov (D2τ' σ) .fst) l (≃₁-zerov σ (interp l val)) w2
    in chad-preserves-≃₂ val (LACMexec m1 evIn) (zerov (D2τ' τ) .fst) r (≃₁-zerov τ (interp r val)) ihl
chad-preserves-≃₂ {Γ} val evIn (just (ctgL , ctgR)) (pair l r) w1 w2
  using m1 ← interp (chad l) (primalVal val) .snd ctgL .fst
  using m2 ← interp (chad r) (primalVal val) .snd ctgR .fst
  rewrite LACMexec-sequence m1 m2 evIn
  = let ihl = chad-preserves-≃₂ val evIn ctgL l (w1 .fst) w2
    in chad-preserves-≃₂ val (LACMexec m1 evIn) ctgR r (w1 .snd) ihl
chad-preserves-≃₂ {Γ} val evIn ctg (fst' {σ = σ} {τ = τ} t) w1 w2
  rewrite simplify-exec-chad-fst val evIn ctg t
  = chad-preserves-≃₂ val evIn (just (ctg , zerov (D2τ' τ) .fst)) t (w1 , (≃₁-zerov τ (interp t val .snd))) w2
chad-preserves-≃₂ {Γ} val evIn ctg (snd' {σ = σ} {τ = τ} t) w1 w2
  rewrite simplify-exec-chad-snd val evIn ctg t
  = chad-preserves-≃₂ val evIn (just (zerov (D2τ' σ) .fst , ctg)) t ((≃₁-zerov σ (interp t val .fst)) , w1) w2
chad-preserves-≃₂ {Γ} val evIn ctg (let' {σ = σ} {τ = τ} rhs body) w1 w2
  rewrite simplify-exec-chad-let-val val evIn ctg rhs body
  =  let ev = (zerov (D2τ' σ) .fst , evIn)
         ih = chad-preserves-≃₂ (push (interp rhs val) val) ev ctg body
                                 w1 (≃₂-intro-zero {Γ} {σ} evIn val (interp rhs val) w2)
         body' = LACMexec ((interp (chad body) (push (primal σ (interp rhs val)) (primalVal val)) .snd ctg .fst)) ev 
     in chad-preserves-≃₂ val (body' .snd) (body' .fst) rhs
        (≃₂-fst body' (interp rhs val) val ih) (≃₂-snd body' (interp rhs val) val ih)
chad-preserves-≃₂ {Γ} val evIn ctg (prim {σ = σ} {τ = τ} op t) w1 w2
  rewrite simplify-exec-chad-primop val evIn ctg t op
  = let d-op-env = push ctg (push (primal σ (interp t val)) empty)
    in chad-preserves-≃₂ val evIn (interp (dprim' op) d-op-env) t (dprim'-preserves-≃₁ val ctg op t w1) w2
chad-preserves-≃₂ {Γ} val evIn nothing (inl {σ = σ} {τ = τ} t) w1 w2
  = chad-preserves-≃₂ val evIn (zerov (D2τ' σ) .fst) t (≃₁-zerov σ (interp t val)) w2
chad-preserves-≃₂ {Γ} val evIn (just (inj₁ ctg)) (inl t) w1 w2
  = chad-preserves-≃₂ val evIn ctg t w1 w2
chad-preserves-≃₂ {Γ} val evIn nothing (inr {σ = σ} {τ = τ} t) w1 w2
  = chad-preserves-≃₂ val evIn (zerov (D2τ' τ) .fst) t (≃₁-zerov τ (interp t val)) w2
chad-preserves-≃₂ {Γ} val evIn (just (inj₂ ctg)) (inr t) w1 w2
  = chad-preserves-≃₂ val evIn ctg t w1 w2
chad-preserves-≃₂ {Γ} val evIn ctg (case' t t₁ t₂) w1 w2 = {!   !}

onehot-equiv-addLEτ-lemma : {Γ : Env Pr} {τ : Typ Pr}
    → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
    in (ctg : LinRep (D2τ' τ))
    → (evIn : LEtup (map D2τ' Γ) )
    → (idx , ctg) ≃₄ evIn
    → LEtup2EV (addLEτ idx' ctg evIn)
      ≡ (Etup2EV (onehot idx (sparse2dense ctg)) ev+ LEtup2EV evIn)
onehot-equiv-addLEτ-lemma {τ ∷ Γ}  Z      ctg (x , xs) w = cong₂ _,_ (plusv-equiv-plusvDense ctg x w) (sym (ev+zeroL' Etup-zerovDense-equiv-zero-EV))
onehot-equiv-addLEτ-lemma {τ ∷ Γ} (S idx) ctg (x , xs) w = cong₂ _,_ (sym plusvDense-zeroL') (onehot-equiv-addLEτ-lemma idx ctg xs w)

gnoc : {A B : Set} {x y : A} → (x ≡ y) → (f : A → B ) → f x ≡ f y
gnoc refl f = refl

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
      ≡⟨ gnoc (LACMexec-pure tt evIn) LEtup2EV ⟩
    LEtup2EV evIn
      ≡⟨ sym (ev+zeroL' DSemᵀ-lemma-ctg-zeroLEnv') ⟩
    Etup2EV (DSemᵀ (interp {Γ = Γ} unit ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
    ∎
chad-equiv-DSemᵀ {Γ} a evIn ctg (var x) w1 w2 =
  let idx = convIdx D2τ' x
  in begin
  LEtup2EV (LACMexec (interp (chad (var x)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (LACMexec-add idx ctg evIn) LEtup2EV ⟩
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
      ihr = trans (chad-equiv-DSemᵀ a (LACMexec m1 evIn) (zerov (D2τ' τ) .fst) r (≃₁-zerov τ (interp r (Etup-to-val a))) (chad-preserves-≃₂ (Etup-to-val a) evIn (zerov (D2τ' σ) .fst) l (≃₁-zerov σ (interp l (Etup-to-val a))) w2 ))
                  (ev+zeroL' (DSemᵀ-lemma-ctg-zeroLEnv' {{zerov-equiv-zerovDense (D2τ' τ)}}))
  in begin
  LEtup2EV (LACMexec (interp (chad (pair l r)) (Etup-to-val-primal a) .snd nothing .fst) evIn)
    ≡⟨ gnoc (LACMexec-sequence m1 m2 evIn) LEtup2EV ⟩
  LEtup2EV (LACMexec m2 (LACMexec m1 evIn))
    ≡⟨ trans ihr ihl ⟩
  LEtup2EV evIn  
    ≡⟨ sym (ev+zeroL' DSemᵀ-lemma-ctg-zeroLEnv') ⟩
  Etup2EV (DSemᵀ (interp (pair l r) ∘ Etup-to-val) a (zerovDense (D2τ' σ) , zerovDense (D2τ' τ))) ev+ LEtup2EV evIn
  ∎ 
chad-equiv-DSemᵀ {Γ} a evIn ctg t _ _ = {!   !}