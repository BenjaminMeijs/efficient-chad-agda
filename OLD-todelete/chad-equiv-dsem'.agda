module correctness.chad-equiv-dsem' where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)

open import Data.Integer using (ℤ)
open import Data.List using (map; _∷_; [])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Product using (_×_)
open import Function.Base using (_∘_; flip; _$_; case_of_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import spec
import spec.LACM as LACM
open import correctness.spec
open import correctness.dsem
open import correctness.lemmas
open import correctness.chad-preserves-compatibility
open import correctness.chad-ctg-zero
open import chad-preserves-primal

gnoc : {A B : Set} {x y : A} → (x ≡ y) → (f : A → B ) → f x ≡ f y
gnoc refl f = refl

evalprim-equiv-DSem : {σ τ : Typ Pr}
                      → (x : Rep σ)
                      → (ctg : LinRep (D2τ' τ))
                      → (op : Primop Pr σ τ )
                      → sparse2dense (interp (dprim' op) (push ctg (push (primal σ x) empty)))
                        ≡ DSem'ᵀ (evalprim op) x (sparse2dense ctg)
evalprim-equiv-DSem (x , y) ctg ADD = sym (DSem'ᵀ-prim-floatPlus (x , y) ctg) 
evalprim-equiv-DSem (x , y) ctg MUL = sym (DSem'ᵀ-prim-floatTimes (x , y) ctg) 
evalprim-equiv-DSem {σ} {τ} x ctg NEG = sym (DSem'ᵀ-prim-floatNegate x ctg) 
evalprim-equiv-DSem tt ctg (LIT x) = refl
evalprim-equiv-DSem x ctg IADD = cong₂ _,_ refl refl 
evalprim-equiv-DSem x ctg IMUL = cong₂ _,_ refl refl 
evalprim-equiv-DSem x tt INEG = refl
evalprim-equiv-DSem x ctg SIGN = sym DSem'ᵀ-lemma-ctg-zero'


chad-equiv-DSem'ᵀ : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep σ)
                  (evIn : LEtup LΓ )
                  (ctg : LinRep (D2τ' τ))
                  (t : Term Pr Γ τ)
                → ctg  ≃τ (interp t (Etup-to-val a))
                → evIn ≃Γ Etup-to-val a  
                -- → (dsem : IsJust (DSem'ᵀ {σ} {τ} (interp t ∘ Etup-to-val) a) )
                -- → (LEtup2EV {LΓ} (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst ) evIn)
                --   ≡ Etup2EV {Γ} ( to-witness dsem (sparse2dense ctg)) ev+ LEtup2EV {LΓ} evIn)
                → (LEtup2EV {LΓ} (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst ) evIn)
                  ≡ Etup2EV {Γ} (DSem'ᵀ {σ} {τ} (interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV {LΓ} evIn)
chad-equiv-DSem'ᵀ {Γ} a evIn tt unit w1 w2
  rewrite chad-ctg-zero (Etup-to-val a) evIn tt unit tt w2 refl
  = DSem'ᵀ-lemma-ctg-zero-evIn'
chad-equiv-DSem'ᵀ {Γ} a evIn ctg (var x) w1 w2 =
  let idx = convIdx D2τ' x
  in begin
  LEtup2EV (LACMexec (interp (chad (var x)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (LACMexec-add idx ctg evIn) LEtup2EV ⟩
  LEtup2EV (addLEτ idx ctg evIn)
    ≡⟨ onehot-equiv-addLEτ-lemma x ctg evIn (≃τ-and-≃Γ-implies-Compatible-idx-LEtup x ctg evIn (Etup-to-val a) w1 w2) ⟩
  Etup2EV (onehot x (sparse2dense ctg)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (sym (cong Etup2EV (DSem'ᵀ-var a x (sparse2dense ctg)))) ⟩
  Etup2EV (DSem'ᵀ (flip valprj x ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSem'ᵀ {Γ} a evIn nothing (pair {σ = σ} {τ = τ} l r) w1 w2
  rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (pair l r) tt w2 refl 
  = DSem'ᵀ-lemma-ctg-zero-evIn'
chad-equiv-DSem'ᵀ {Γ} a evIn (just ctg) (pair {σ = σ} {τ = τ} l r) w1 w2 =
  let ctgL = _ ; ctgR = _
      m1 = interp (chad l) (Etup-to-val-primal a) .snd ctgL .fst
      m2 = interp (chad r) (Etup-to-val-primal a) .snd ctgR .fst
      ihr = chad-equiv-DSem'ᵀ a (LACMexec m1 evIn) ctgR r (w1 .snd) (chad-preserves-≃Γ (Etup-to-val a) evIn ctgL l (w1 .fst) w2)
      ihl = chad-equiv-DSem'ᵀ a evIn ctgL l (w1 .fst) w2 
  in begin
  LEtup2EV (LACMexec (LACMsequence m1 m2) evIn)
    ≡⟨ gnoc (LACMexec-sequence m1 m2 evIn) LEtup2EV ⟩
  LEtup2EV (LACMexec m2 (LACMexec m1 evIn))
    ≡⟨ trans ihr (trans (ev+congR ihl) (trans (sym (ev+assoc _ _ _)  ) (ev+congL (ev+comm _ _)) ))  ⟩
  (Etup2EV (DSem'ᵀ (interp l ∘ Etup-to-val) a (sparse2dense (ctg .fst))) ev+ Etup2EV (DSem'ᵀ (interp r ∘ Etup-to-val) a (sparse2dense (ctg .snd))) ) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (DSem'ᵀ-lemma-pair _ _ a _ _) ⟩
  Etup2EV (DSem'ᵀ (interp (pair l r) ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} (just ctg))) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSem'ᵀ {Γ} a evIn ctg (fst' {σ = σ} {τ = τ} t) w1 w2 =
  let ctg' = (just (ctg , zerov (D2τ' τ) .fst))
  in begin
  LEtup2EV (LACMexec (interp (chad (fst' t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-fst (Etup-to-val a) evIn ctg t) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad t) (primalVal (Etup-to-val a)) .snd ctg'  .fst) evIn)
    ≡⟨ chad-equiv-DSem'ᵀ a evIn ctg' t (w1 , ≃τ-zerov' τ) w2 ⟩
  Etup2EV (DSem'ᵀ (interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} ctg')) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (DSem'ᵀ-lemma-pair-zeroR _ _ a _) Etup2EV) ⟩
  Etup2EV (DSem'ᵀ (interp (fst' t) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSem'ᵀ {Γ} a evIn ctg (snd' {σ = σ} {τ = τ} t) w1 w2 =
  let ctg' = (just (zerov (D2τ' σ) .fst , ctg))
  in begin
  LEtup2EV (LACMexec (interp (chad (snd' t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-snd (Etup-to-val a) evIn ctg t) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad t) (primalVal (Etup-to-val a)) .snd ctg' .fst) evIn)
    ≡⟨ chad-equiv-DSem'ᵀ a evIn ctg' t ((≃τ-zerov' σ) , w1)  w2 ⟩
  Etup2EV (DSem'ᵀ (interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} ctg')) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (DSem'ᵀ-lemma-pair-zeroL _ _ a _) Etup2EV) ⟩
  Etup2EV (DSem'ᵀ (interp (snd' t) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSem'ᵀ {Γ} a evIn ctg (let' {σ = σ} {τ = τ} rhs body) w1 w2 =
  let a' = (interp rhs (Etup-to-val a)) , a
      body' = interp (chad body) (Etup-to-val-primal a') .snd ctg .fst
      ev-body = LACMexec body' (zerov (D2τ' σ) .fst , evIn)
      ih-body = trans (chad-equiv-DSem'ᵀ a' (zerov (D2τ' σ) .fst , evIn) ctg body w1 (≃Γ-intro-zero' σ evIn w2))
                      (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' σ) }}) refl)
      preserves-≃Γ = chad-preserves-≃Γ (Etup-to-val a') (zerov (D2τ' σ) .fst , evIn) ctg body w1 (≃Γ-intro-zero' σ evIn w2)
      ih-rhs = chad-equiv-DSem'ᵀ a (ev-body .snd) (ev-body .fst) rhs (fst preserves-≃Γ) (snd preserves-≃Γ)
      ih = trans ih-rhs (trans (ev+congR (cong snd ih-body)) (ev+congL (gnoc (gnoc (cong fst ih-body) (DSem'ᵀ (interp rhs ∘ Etup-to-val) a)) Etup2EV  ) ))

      dsem-body = DSem'ᵀ {σ = σ :* (Etup Pr Γ)} {τ = τ} (interp body ∘ Etup-to-val) a' (sparse2dense ctg)
      dsem-rhs = DSem'ᵀ (interp rhs ∘ Etup-to-val) a (Etup2EV dsem-body .fst)
  in begin
  LEtup2EV (LACMexec (interp (chad (let' rhs body)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-let a Etup-to-val evIn ctg rhs body) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad rhs) (Etup-to-val-primal a) .snd (ev-body .fst) .fst) (ev-body .snd))
    ≡⟨ trans ih (sym (ev+assoc _ _ _)) ⟩
  (Etup2EV dsem-rhs  ev+ Etup2EV dsem-body .snd ) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (DSem'ᵀ-lemma-interp-let a (sparse2dense ctg) rhs body) ⟩
  Etup2EV (DSem'ᵀ {σ = Etup Pr Γ} {τ = τ} (interp (let' rhs body) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSem'ᵀ {Γ} a evIn ctg (prim {σ = σ} {τ = τ} op t) w1 w2 =
  let d-op = interp (dprim' op) (Etup-to-val (ctg , (primal σ (interp t (Etup-to-val a)), tt))) 
  in begin
  LEtup2EV (LACMexec (interp (chad (prim op t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-primop (Etup-to-val a) evIn ctg t op) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd d-op .fst) evIn)
    ≡⟨ chad-equiv-DSem'ᵀ a evIn d-op t (dprim'-preserves-≃τ (Etup-to-val a) ctg op t w1) w2 ⟩
  Etup2EV (DSem'ᵀ (interp t ∘ Etup-to-val) a (sparse2dense d-op)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (gnoc (evalprim-equiv-DSem (interp t (Etup-to-val a)) ctg op) (DSem'ᵀ _ a)) Etup2EV) ⟩
  Etup2EV (DSem'ᵀ {σ = Etup Pr Γ} {τ = σ} (interp t ∘ Etup-to-val) a (DSem'ᵀ {σ = σ} {τ = τ} (evalprim op) (interp t (Etup-to-val a)) (sparse2dense ctg))) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (sym (DSem'ᵀ-chain (evalprim op) (interp t ∘ Etup-to-val) a (sparse2dense ctg))) Etup2EV) ⟩
  Etup2EV (DSem'ᵀ (evalprim op ∘ interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSem'ᵀ {Γ} a evIn nothing (inl {σ = σ} {τ = τ} t) w1 w2
  rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (inl {σ = σ} {τ = τ} t ) tt w2 refl 
  = DSem'ᵀ-lemma-ctg-zero-evIn'
chad-equiv-DSem'ᵀ {Γ} a evIn nothing (inr {σ = σ} {τ = τ} t) w1 w2
  rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (inr {σ = σ} {τ = τ} t ) tt w2 refl 
  = DSem'ᵀ-lemma-ctg-zero-evIn'
chad-equiv-DSem'ᵀ {Γ} a evIn (just (inj₁ ctg)) (inl {σ = σ} {τ = τ} t) w1 w2 =
  begin
  LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ chad-equiv-DSem'ᵀ a evIn ctg t w1 w2 ⟩
  Etup2EV (DSem'ᵀ (interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (DSem'ᵀ-lemma-inj₁ (interp t ∘ Etup-to-val) a (sparse2dense ctg) (zerovDense (D2τ' τ))) Etup2EV) ⟩
  Etup2EV (DSem'ᵀ (inj₁ ∘ interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :+! D2τ' τ} (just (inj₁ ctg)))) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSem'ᵀ {Γ} a evIn (just (inj₂ ctg)) (inr {σ = σ} {τ = τ} t) w1 w2 =
  begin
  LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ chad-equiv-DSem'ᵀ a evIn ctg t w1 w2 ⟩
  Etup2EV (DSem'ᵀ (interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (DSem'ᵀ-lemma-inj₂ (interp t ∘ Etup-to-val) a (zerovDense (D2τ' σ)) (sparse2dense ctg)) Etup2EV) ⟩
  Etup2EV (DSem'ᵀ (inj₂ ∘ interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :+! D2τ' τ} (just (inj₂ ctg)))) ev+ LEtup2EV evIn
  ∎  
chad-equiv-DSem'ᵀ {Γ} a evIn ctg (case' {σ = σ} {τ = τ} {ρ = ρ} e l r) w1 w2
  rewrite chad-preserves-primal (Etup-to-val a) e
  with interp e (Etup-to-val a) in interp-e-val≡inj-x
... | inj₁ x
  rewrite simplify-exec-chad-case (Etup-to-val a) evIn ctg e l x inj₁
  = let ev' = (zerov (D2τ' σ) .fst , evIn)
        l' = LACMexec (interp (chad l) (Etup-to-val-primal (x , a)) .snd ctg .fst) ev'

        ev'≃ev = (≃Γ-intro-zero' σ evIn w2)
        l'-preserves≃Γ = chad-preserves-≃Γ (Etup-to-val (x , a)) ev' ctg l w1 ev'≃ev
        l'-preserves≃τ = ≃τ-congR (σ :+ τ) (just (inj₁ (l' .fst))) (inj₁ x) (interp e (Etup-to-val a)) (sym interp-e-val≡inj-x) (fst l'-preserves≃Γ)

        ih-e = chad-equiv-DSem'ᵀ a (l' .snd) (just (inj₁ (l' .fst))) e l'-preserves≃τ (snd l'-preserves≃Γ)
        ih-l = trans (chad-equiv-DSem'ᵀ (x , a) ev' ctg l w1 ev'≃ev )
                     (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' σ)}}) refl)
        ih = trans ih-e (cong₂ _ev+_ (gnoc (cong fst ih-l) (λ q → Etup2EV (DSem'ᵀ (interp e ∘ Etup-to-val) a (q , zerovDense (D2τ' τ))))) (cong snd ih-l)) 

        dsem-l = DSem'ᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a) (sparse2dense ctg)
        dsem-e = DSem'ᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a ( dsem-l .fst , zerovDense (D2τ' τ))
        lemma-dsem-case = DSem'ᵀ-lemma-interp-case-cong a (sparse2dense ctg) e l r (inj₁ x) interp-e-val≡inj-x
    in begin
    LEtup2EV (LACMexec (interp (chad e) (Etup-to-val-primal a) .snd (just (inj₁ (l' .fst))) .fst) (l' .snd))
      ≡⟨ trans ih (sym $ ev+assoc _ _ _) ⟩
    (Etup2EV dsem-e ev+ Etup2EV (dsem-l .snd)) ev+ LEtup2EV evIn
      ≡⟨ ev+congL lemma-dsem-case ⟩
    Etup2EV (DSem'ᵀ {Etup Pr Γ} {ρ} (interp (case' e l r) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
    ∎

... | inj₂ x
  rewrite simplify-exec-chad-case (Etup-to-val a) evIn ctg e r x inj₂
  = let ev' = (zerov (D2τ' τ) .fst , evIn)
        body = LACMexec (interp (chad r) (Etup-to-val-primal (x , a)) .snd ctg .fst) ev'

        ev'≃ev = (≃Γ-intro-zero' τ evIn w2)
        body-preserves≃Γ = chad-preserves-≃Γ (Etup-to-val (x , a)) ev' ctg r w1 ev'≃ev
        body-preserves≃τ = ≃τ-congR (σ :+ τ) (just (inj₂ (body .fst))) (inj₂ x) (interp e (Etup-to-val a)) (sym interp-e-val≡inj-x) (fst body-preserves≃Γ)

        ih-e = chad-equiv-DSem'ᵀ a (body .snd) (just (inj₂ (body .fst))) e body-preserves≃τ (snd body-preserves≃Γ)
        ih-l = trans (chad-equiv-DSem'ᵀ (x , a) ev' ctg r w1 ev'≃ev )
                     (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' τ)}}) refl)
        ih = trans ih-e (cong₂ _ev+_ (gnoc (cong fst ih-l) (λ q → Etup2EV (DSem'ᵀ (interp e ∘ Etup-to-val) a (zerovDense (D2τ' σ) , q))) ) (cong snd ih-l))

        dsem-body = DSem'ᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a) (sparse2dense ctg)
        dsem-e = DSem'ᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a ( zerovDense (D2τ' σ) , dsem-body .fst)

        lemma-dsem-case = DSem'ᵀ-lemma-interp-case-cong a (sparse2dense ctg) e l r (inj₂ x) interp-e-val≡inj-x
    in begin
    LEtup2EV (LACMexec (interp (chad e) (Etup-to-val-primal a) .snd (just (inj₂ (body .fst))) .fst) (body .snd))
      ≡⟨ trans ih (sym $ ev+assoc _ _ _) ⟩
    (Etup2EV dsem-e ev+ Etup2EV (dsem-body .snd)) ev+ LEtup2EV evIn
      ≡⟨ ev+congL lemma-dsem-case ⟩
    Etup2EV (DSem'ᵀ {Etup Pr Γ} {ρ} (interp (case' e l r) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
    ∎
