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
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; cong-app; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import spec
import spec.LACM as LACM
open import correctness.spec
open import correctness.dsem
open import correctness.lemmas
open import correctness.chad-preserves-congruence
open import chad-preserves-primal

gnoc : {A B : Set} {x y : A} → (x ≡ y) → (f : A → B ) → f x ≡ f y
gnoc refl f = refl

evalprim-equiv-DSem : {σ τ : Typ Pr}
                      → (x : Rep σ)
                      → (ctg : LinRep (D2τ' τ))
                      → (op : Primop Pr σ τ )
                      → sparse2dense (interp (dprim' op) (push ctg (push (primal σ x) empty)))
                        ≡ DSemᵀ (evalprim op) x (sparse2dense ctg)
evalprim-equiv-DSem (x , y) ctg ADD = sym (DSemᵀ-prim-floatPlus (x , y) ctg) 
evalprim-equiv-DSem (x , y) ctg MUL = sym (DSemᵀ-prim-floatTimes (x , y) ctg) 
evalprim-equiv-DSem {σ} {τ} x ctg NEG = sym (DSemᵀ-prim-floatNegate x ctg) 
evalprim-equiv-DSem tt ctg (LIT x) = refl
evalprim-equiv-DSem x ctg IADD = cong₂ _,_ refl refl 
evalprim-equiv-DSem x ctg IMUL = cong₂ _,_ refl refl 
evalprim-equiv-DSem x tt INEG = refl
evalprim-equiv-DSem x ctg SIGN = sym DSemᵀ-lemma-ctg-zero'

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
chad-equiv-DSemᵀ {Γ} a evIn (just ctg) (pair {σ = σ} {τ = τ} l r) w1 w2
  = let ctgL = _ ; ctgR = _
        m1 = interp (chad l) (Etup-to-val-primal a) .snd ctgL .fst
        m2 = interp (chad r) (Etup-to-val-primal a) .snd ctgR .fst
        ihr = chad-equiv-DSemᵀ a (LACMexec m1 evIn) ctgR r (w1 .snd) (chad-preserves-≃₂ (Etup-to-val a) evIn ctgL l (w1 .fst) w2)
        ihl = chad-equiv-DSemᵀ a evIn ctgL l (w1 .fst) w2 
    in begin
    LEtup2EV (LACMexec (LACMsequence m1 m2) evIn)
      ≡⟨ gnoc (LACMexec-sequence m1 m2 evIn) LEtup2EV ⟩
    LEtup2EV (LACMexec m2 (LACMexec m1 evIn))
      ≡⟨ trans ihr (trans (ev+congR ihl) (trans (sym (ev+assoc _ _ _)  ) (ev+congL (ev+comm _ _)) ))  ⟩
    (Etup2EV (DSemᵀ (interp l ∘ Etup-to-val) a (sparse2dense (ctg .fst))) ev+ Etup2EV (DSemᵀ (interp r ∘ Etup-to-val) a (sparse2dense (ctg .snd))) ) ev+ LEtup2EV evIn
      ≡⟨ ev+congL (DSemᵀ-lemma-pair _ _ a _ _) ⟩
    Etup2EV (DSemᵀ (interp (pair l r) ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} (just ctg))) ev+ LEtup2EV evIn
    ∎
chad-equiv-DSemᵀ {Γ} a evIn ctg (fst' {σ = σ} {τ = τ} t) w1 w2 =
  let ctg' = (just (ctg , zerov (D2τ' τ) .fst))
  in begin
  LEtup2EV (LACMexec (interp (chad (fst' t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-fst (Etup-to-val a) evIn ctg t) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad t) (primalVal (Etup-to-val a)) .snd ctg'  .fst) evIn)
    ≡⟨ chad-equiv-DSemᵀ a evIn ctg' t (w1 , ≃₁-zerov τ (interp t (Etup-to-val a) .snd)) w2 ⟩
  Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} ctg')) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-fst _ _ a _) Etup2EV) ⟩
  Etup2EV (DSemᵀ (interp (fst' t) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn ctg (snd' {σ = σ} {τ = τ} t) w1 w2 =
  let ctg' = (just (zerov (D2τ' σ) .fst , ctg))
  in begin
  LEtup2EV (LACMexec (interp (chad (snd' t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-snd (Etup-to-val a) evIn ctg t) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad t) (primalVal (Etup-to-val a)) .snd ctg' .fst) evIn)
    ≡⟨ chad-equiv-DSemᵀ a evIn ctg' t ((≃₁-zerov σ (interp t (Etup-to-val a) .fst)) , w1)  w2 ⟩
  Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} ctg')) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-snd _ _ a _) Etup2EV) ⟩
  Etup2EV (DSemᵀ (interp (snd' t) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn ctg (let' {σ = σ} {τ = τ} rhs body) w1 w2 =
  let a' = (interp rhs (Etup-to-val a)) , a
      body' = interp (chad body) (Etup-to-val-primal a') .snd ctg .fst
      ev-body = LACMexec body' (zerov (D2τ' σ) .fst , evIn)
      ih-body = trans (chad-equiv-DSemᵀ a' (zerov (D2τ' σ) .fst , evIn) ctg body w1 (≃₂-intro-zero {τ = σ} evIn (Etup-to-val a) (interp rhs (Etup-to-val a)) w2))
                      (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' σ) }}) refl)
      preserves-≃₂ = chad-preserves-≃₂ (Etup-to-val a') (zerov (D2τ' σ) .fst , evIn) ctg body w1 (≃₂-intro-zero {τ = σ} evIn (Etup-to-val a) (interp rhs (Etup-to-val a)) w2)
      ih-rhs = chad-equiv-DSemᵀ a (ev-body .snd) (ev-body .fst) rhs (≃₂-fst ev-body (interp rhs (Etup-to-val a)) (Etup-to-val a) preserves-≃₂) (≃₂-snd ev-body (interp rhs (Etup-to-val a)) (Etup-to-val a) preserves-≃₂) -- (≃₁-zerov σ (interp rhs (Etup-to-val a))) w2 
      ih = trans ih-rhs (trans (ev+congR (cong snd ih-body)) (ev+congL (gnoc (gnoc (cong fst ih-body) (DSemᵀ (interp rhs ∘ Etup-to-val) a)) Etup2EV  ) ))

      dsem-body = DSemᵀ {σ = σ :* (Etup Pr Γ)} {τ = τ} (interp body ∘ Etup-to-val) a' (sparse2dense ctg)
      dsem-rhs = DSemᵀ (interp rhs ∘ Etup-to-val) a (Etup2EV dsem-body .fst)
  in begin
  LEtup2EV (LACMexec (interp (chad (let' rhs body)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-let a evIn ctg rhs body) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad rhs) (Etup-to-val-primal a) .snd (ev-body .fst) .fst) (ev-body .snd))
    ≡⟨ trans ih (sym (ev+assoc _ _ _)) ⟩
  (Etup2EV dsem-rhs  ev+ Etup2EV dsem-body .snd ) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (DSemᵀ-lemma-interp-let a (sparse2dense ctg) rhs body) ⟩
  Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = τ} (interp (let' rhs body) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn ctg (prim {σ = σ} {τ = τ} op t) w1 w2 =
  let d-op = interp (dprim' op) (Etup-to-val (ctg , (primal σ (interp t (Etup-to-val a)), tt))) 
  in begin
  LEtup2EV (LACMexec (interp (chad (prim op t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-primop (Etup-to-val a) evIn ctg t op) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd d-op .fst) evIn)
    ≡⟨ chad-equiv-DSemᵀ a evIn d-op t (dprim'-preserves-≃₁ (Etup-to-val a) ctg op t w1) w2 ⟩
  Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense d-op)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (gnoc (evalprim-equiv-DSem (interp t (Etup-to-val a)) ctg op) (DSemᵀ _ a)) Etup2EV) ⟩
  Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = σ} (interp t ∘ Etup-to-val) a (DSemᵀ {σ = σ} {τ = τ} (evalprim op) (interp t (Etup-to-val a)) (sparse2dense ctg))) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (sym (cong-app (DSemᵀ-chain (evalprim op) (interp t ∘ Etup-to-val) a) (sparse2dense ctg))) Etup2EV) ⟩
  Etup2EV (DSemᵀ (evalprim op ∘ interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn nothing (inl {σ = σ} {τ = τ} t) w1 w2 = 
  begin
  LEtup2EV (LACMexec (interp (chad (inl {σ = σ} {τ = τ} t)) (Etup-to-val-primal a) .snd nothing .fst) evIn)
    ≡⟨ chad-equiv-DSemᵀ a evIn (zerov (D2τ' σ) .fst) t (≃₁-zerov σ (interp t (Etup-to-val a))) w2 ⟩
  Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense (zerov (D2τ' σ) .fst))) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (DSemᵀ-lemma-ctg-zeroLEnv' {{zerov-equiv-zerovDense (D2τ' σ)}})  ⟩
  zero-EV (map D2τ' Γ) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (sym DSemᵀ-lemma-ctg-zeroLEnv')  ⟩
  Etup2EV (DSemᵀ (interp (inl {σ = σ} {τ = τ} t) ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} nothing)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn (just (inj₁ ctg)) (inl {σ = σ} {τ = τ} t) w1 w2 =
  begin
  LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ chad-equiv-DSemᵀ a evIn ctg t w1 w2 ⟩
  Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-inj₁ (interp t ∘ Etup-to-val) a (sparse2dense ctg) (zerovDense (D2τ' τ))) Etup2EV) ⟩
  Etup2EV (DSemᵀ (inj₁ ∘ interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :+! D2τ' τ} (just (inj₁ ctg)))) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn nothing (inr {σ = σ} {τ = τ} t) w1 w2 = 
  begin
  LEtup2EV (LACMexec (interp (chad (inr {σ = σ} {τ = τ} t)) (Etup-to-val-primal a) .snd nothing .fst) evIn)
    ≡⟨ chad-equiv-DSemᵀ a evIn (zerov (D2τ' τ) .fst) t (≃₁-zerov τ (interp t (Etup-to-val a))) w2 ⟩
  Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense (zerov (D2τ' τ) .fst))) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (DSemᵀ-lemma-ctg-zeroLEnv' {{zerov-equiv-zerovDense (D2τ' τ)}})  ⟩
  zero-EV (map D2τ' Γ) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (sym DSemᵀ-lemma-ctg-zeroLEnv')  ⟩
  Etup2EV (DSemᵀ (interp (inr {σ = σ} {τ = τ} t) ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} nothing)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn (just (inj₂ ctg)) (inr {σ = σ} {τ = τ} t) w1 w2 =
  begin
  LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ chad-equiv-DSemᵀ a evIn ctg t w1 w2 ⟩
  Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-inj₂ (interp t ∘ Etup-to-val) a (zerovDense (D2τ' σ)) (sparse2dense ctg)) Etup2EV) ⟩
  Etup2EV (DSemᵀ (inj₂ ∘ interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :+! D2τ' τ} (just (inj₂ ctg)))) ev+ LEtup2EV evIn
  ∎  
chad-equiv-DSemᵀ {Γ} a evIn ctg (case' e l r) w1 w2 = {!   !}