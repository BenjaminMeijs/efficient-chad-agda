module correctness.chad-equiv-dsem where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Agda.Builtin.Float using (primFloatPlus; primFloatTimes; primFloatNegate)

open import Data.Integer using (ℤ)
open import Data.List using (map; _∷_; [])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness)
open import Data.Product using (_×_)
open import Function.Base using (_∘_; flip; _$_; case_of_; id)
open import Function.Bundles using (Equivalence; _⇔_ )
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
                      → (a : Rep σ)
                      → (ctg : LinRep (D2τ' τ))
                      → (op : Primop Pr σ τ )
                      → (d-op : Is-just $ DSemᵀ {σ} {τ} (evalprim op) a)
                      → sparse2dense (interp (dprim' op) (push ctg (push (primal σ a) empty)))
                        ≡ (to-witness d-op $ sparse2dense ctg)
evalprim-equiv-DSem (x , y) ctg ADD d-op
  = let (d-op2 , rule) = DSemᵀ-prim-floatPlus (x , y) ctg
        ext = DSemᵀ-extensionality _ (evalprim {tag = Pr} ADD) (λ _ → refl) (x , y) d-op2 d-op ctg 
    in trans (sym rule) ext
evalprim-equiv-DSem (x , y) ctg MUL d-op
  = let (d-op2 , rule) = DSemᵀ-prim-floatTimes (x , y) ctg
        ext = DSemᵀ-extensionality _ (evalprim {tag = Pr} MUL) (λ _ → refl) (x , y) d-op2 d-op ctg 
    in trans (sym rule) ext
evalprim-equiv-DSem {σ} {τ} x ctg NEG d-op
  = let (d-op2 , rule) = DSemᵀ-prim-floatNegate x ctg
        ext = DSemᵀ-extensionality primFloatNegate (evalprim {tag = Pr} NEG) (λ _ → refl) x d-op2 d-op ctg 
  in (trans (sym rule) ext)
evalprim-equiv-DSem x ctg SIGN d-op = sym (Zero.DSemᵀ-lemma-ctg-zero' d-op) 
evalprim-equiv-DSem tt ctg (LIT x) d-op = refl
evalprim-equiv-DSem x  ctg IADD    d-op = refl
evalprim-equiv-DSem x  ctg IMUL    d-op = refl
evalprim-equiv-DSem x  ctg INEG    d-op = refl


chad-equiv-DSemᵀ : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep σ)
                  (evIn : LEtup LΓ )
                  (ctg : LinRep (D2τ' τ))
                  (t : Term Pr Γ τ)
                → ctg  ≃τ (interp t (Etup-to-val a))
                → evIn ≃Γ Etup-to-val a  
                → (dsem : Is-just (DSemᵀ {σ} {τ} (interp t ∘ Etup-to-val) a) )
                → (LEtup2EV {LΓ} (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst ) evIn)
                  ≡ Etup2EV {Γ} ( to-witness dsem (sparse2dense ctg)) ev+ LEtup2EV {LΓ} evIn)
-- Cases where ctg is (semantically) zero
chad-equiv-DSemᵀ {Γ} a evIn tt unit ~τ ~Γ dt 
  rewrite chad-ctg-zero (Etup-to-val a) evIn tt unit tt ~Γ refl
  = Ev-zero.DSemᵀ-ev-lemma-ctg-zero-evIn' dt
chad-equiv-DSemᵀ {Γ} a evIn nothing (pair {σ = σ} {τ = τ} l r) ~τ ~Γ dt
  rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (pair l r) tt ~Γ refl 
  = Ev-zero.DSemᵀ-ev-lemma-ctg-zero-evIn' dt
chad-equiv-DSemᵀ {Γ} a evIn nothing (inl {σ = σ} {τ = τ} t) ~τ ~Γ d-inl
  rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (inl {σ = σ} {τ = τ} t) tt ~Γ refl 
  = Ev-zero.DSemᵀ-ev-lemma-ctg-zero-evIn' d-inl
chad-equiv-DSemᵀ {Γ} a evIn nothing (inr {σ = σ} {τ = τ} t) ~τ ~Γ d-inr
  rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (inr {σ = σ} {τ = τ} t) tt ~Γ refl 
  = Ev-zero.DSemᵀ-ev-lemma-ctg-zero-evIn' d-inr
-- Cases where ctg is NOT (semantically) zero
chad-equiv-DSemᵀ {Γ} a evIn ctg (var idx) ~τ ~Γ dt 
  = let idx' = convIdx D2τ' idx
        (d-var , eq) = DSemᵀ-var a idx (sparse2dense ctg)
  in begin
  LEtup2EV (LACMexec (interp (chad (var idx)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (LACMexec-add idx' ctg evIn) LEtup2EV ⟩
  LEtup2EV (addLEτ idx' ctg evIn)
    ≡⟨ Onehot.onehot-equiv-addLEτ-lemma idx ctg evIn (Etup-to-val a) ~τ ~Γ ⟩
  Etup2EV (onehot idx $ sparse2dense ctg) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (sym eq) Etup2EV) ⟩
  Etup2EV (to-witness d-var (sparse2dense ctg)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (DSemᵀ-extensionality _ _ (λ _ → refl) a d-var dt (sparse2dense ctg)) Etup2EV) ⟩
  Etup2EV (to-witness dt (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn (just ctg) (pair {σ = σ} {τ = τ} l r) ~τ ~Γ dt
  = let ctgL = _ ; ctgR = _
        m1 = interp (chad l) (Etup-to-val-primal a) .snd ctgL .fst
        m2 = interp (chad r) (Etup-to-val-primal a) .snd ctgR .fst

        (dl , dr) = Pair.DSemᵀ-exists-lemma-pair₁ (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) a dt
        ihr = chad-equiv-DSemᵀ a (LACMexec m1 evIn) ctgR r (~τ .snd) (chad-preserves-≃Γ (Etup-to-val a) evIn ctgL l (~τ .fst) ~Γ) dr
        ihl = chad-equiv-DSemᵀ a evIn ctgL l (~τ .fst) ~Γ dl
  in begin
  LEtup2EV (LACMexec (LACMsequence m1 m2) evIn)
    ≡⟨ gnoc (LACMexec-sequence m1 m2 evIn) LEtup2EV ⟩
  LEtup2EV (LACMexec m2 (LACMexec m1 evIn))
    ≡⟨ trans ihr (trans (ev+congR ihl) (trans (sym (ev+assoc _ _ _)) (ev+congL (ev+comm _ _)))) ⟩
  (Etup2EV (to-witness dl (sparse2dense $ fst ctg )) ev+ Etup2EV (to-witness dr (sparse2dense $ snd ctg))) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (Ev-pair.DSemᵀ-ev-lemma-pair (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) a (sparse2dense $ fst ctg) (sparse2dense $ snd ctg) dl dr dt) ⟩
  (Etup2EV (to-witness dt (sparse2dense {D2τ' σ :*! D2τ' τ} (just ctg))) ev+ LEtup2EV evIn)
  ∎
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (fst' {σ = σ} {τ = τ} t) w1 w2 =
--   let ctg' = (just (ctg , zerov (D2τ' τ) .fst))
--   in begin
--   LEtup2EV (LACMexec (interp (chad (fst' t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ gnoc (simplify-exec-chad-fst (Etup-to-val a) evIn ctg t) LEtup2EV ⟩
--   LEtup2EV (LACMexec (interp (chad t) (primalVal (Etup-to-val a)) .snd ctg'  .fst) evIn)
--     ≡⟨ chad-equiv-DSemᵀ a evIn ctg' t (w1 , ≃τ-zerov' τ) w2 ⟩
--   Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} ctg')) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-pair-zeroR _ _ a _) Etup2EV) ⟩
--   Etup2EV (DSemᵀ (interp (fst' t) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
--   ∎
chad-equiv-DSemᵀ {Γ} a evIn ctg (fst' {σ = σ} {τ = τ} t) ~τ ~Γ d-fst
  = let ctg' = (just (ctg , zerov (D2τ' τ) .fst))
        d-t : Is-just (DSemᵀ {Etup Pr Γ} {σ :* τ} (interp t ∘ Etup-to-val) a)
        d-t = Equivalence.to (DSemᵀ-exists-chain {τ2 = σ :* τ} fst (interp t ∘ Etup-to-val) a) d-fst .fst
        d-snd : Is-just (DSemᵀ {Etup Pr Γ} {τ} (interp (snd' t) ∘ Etup-to-val) a)
        d-snd = Pair.DSemᵀ-exists-lemma-pair₁ _ _ a d-t .snd
  in begin
  LEtup2EV (LACMexec (interp (chad (fst' t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-fst (Etup-to-val a) evIn ctg t) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad t) (primalVal (Etup-to-val a)) .snd ctg'  .fst) evIn)
    ≡⟨ chad-equiv-DSemᵀ a evIn ctg' t (~τ , ≃τ-zerov' τ) ~Γ d-t ⟩
  Etup2EV (to-witness d-t (sparse2dense ctg , sparse2dense (zerov (D2τ' τ) .fst))) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (Pair.DSemᵀ-lemma-pair-zeroR (interp (fst' t) ∘ Etup-to-val) _ a d-t d-fst d-snd (sparse2dense ctg)) Etup2EV) ⟩
  Etup2EV (to-witness d-fst $ sparse2dense ctg) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn ctg (snd' {σ = σ} {τ = τ} t) ~τ ~Γ d-snd = {!   !}
chad-equiv-DSemᵀ {Γ} a evIn ctg (let' {σ = σ} {τ = τ} rhs body) ~τ ~Γ dt =
  let -- DSems of subterms are defined
      g = (λ env → (interp rhs (Etup-to-val env) , env))
      defined = Equivalence.to (DSemᵀ-exists-chain {Etup Pr Γ} {σ :* Etup Pr Γ} {τ} (interp body ∘ Etup-to-val) g a) dt
      d-rhs = Pair.DSemᵀ-exists-lemma-pair₁ (interp rhs ∘ Etup-to-val) id a (defined .fst) .fst
      d-body = defined .snd
      -- Helpful shorthands
      a' = (interp rhs (Etup-to-val a)) , a
      ctg-body = to-witness d-body (sparse2dense ctg)
      ev-body = LACMexec (interp (chad body) (Etup-to-val-primal a') .snd ctg .fst) (zerov (D2τ' σ) .fst , evIn)
      -- Induction hypothesis
      preserves-≃Γ = chad-preserves-≃Γ (Etup-to-val a') (zerov (D2τ' σ) .fst , evIn) ctg body ~τ (≃Γ-intro-zero' σ evIn ~Γ)
      ih-body = trans (chad-equiv-DSemᵀ a' (zerov (D2τ' σ) .fst , evIn) ctg body ~τ (≃Γ-intro-zero' σ evIn ~Γ) d-body)
                      (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' σ) }}) refl)
      ih-rhs = chad-equiv-DSemᵀ a (ev-body .snd) (ev-body .fst) rhs (fst preserves-≃Γ) (snd preserves-≃Γ) d-rhs
      ih = trans ih-rhs (trans (ev+congR (cong snd ih-body)) (ev+congL (gnoc (gnoc (cong fst ih-body) (to-witness d-rhs)) Etup2EV)))
  in begin
  LEtup2EV (LACMexec (interp (chad (let' rhs body)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-let a Etup-to-val evIn ctg rhs body) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad rhs) (Etup-to-val-primal a) .snd (ev-body .fst) .fst) (ev-body .snd))
    ≡⟨ trans ih (sym $ ev+assoc _ _ _) ⟩
  (Etup2EV (to-witness d-rhs (fst ctg-body)) ev+ Etup2EV (snd ctg-body)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (DSemᵀ-lemma-interp-let a (sparse2dense ctg) rhs body dt d-rhs d-body) ⟩
  Etup2EV (to-witness dt (sparse2dense ctg)) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn ctg (prim {σ = σ} {τ = τ} op t) ~τ ~Γ d-prim =
  let d-chad-op = interp (dprim' op) (Etup-to-val (ctg , (primal σ (interp t (Etup-to-val a)), tt))) 
      (d-t , d-op) = Equivalence.to (DSemᵀ-exists-chain {τ2 = σ} (evalprim op) (interp t ∘ Etup-to-val) a) d-prim
  in begin
  LEtup2EV (LACMexec (interp (chad (prim op t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
    ≡⟨ gnoc (simplify-exec-chad-primop (Etup-to-val a) evIn ctg t op) LEtup2EV ⟩
  LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd d-chad-op .fst) evIn)
    ≡⟨ chad-equiv-DSemᵀ a evIn d-chad-op t (dprim'-preserves-≃τ (Etup-to-val a) ctg op t ~τ) ~Γ d-t ⟩
  Etup2EV (to-witness d-t $ sparse2dense d-chad-op) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (gnoc (evalprim-equiv-DSem (interp t (Etup-to-val a)) ctg op d-op) (to-witness d-t)) Etup2EV) ⟩
  Etup2EV (to-witness d-t (to-witness d-op $ sparse2dense ctg)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (gnoc (sym (DSemᵀ-chain (evalprim op) (interp t ∘ Etup-to-val) a d-prim d-op d-t (sparse2dense ctg))) Etup2EV) ⟩
  Etup2EV (to-witness d-prim $ sparse2dense ctg) ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn (just (inj₁ ctg)) (inl {σ = σ} {τ = τ} t) ~τ ~Γ d-inl =
  let ctg' = sparse2dense {D2τ' σ :+! D2τ' τ} (just (inj₁ ctg))
      dt = Equivalence.from (DSemᵀ-exists-lemma-inj₁ (interp t ∘ Etup-to-val) a) d-inl
  in begin
  LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst) evIn)
  ≡⟨ chad-equiv-DSemᵀ a evIn ctg t ~τ ~Γ dt ⟩
  Etup2EV (to-witness dt (sparse2dense ctg)) ev+ LEtup2EV evIn
  ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-inj₁ _ a dt d-inl _ _) Etup2EV) ⟩
  Etup2EV (to-witness d-inl ctg') ev+ LEtup2EV evIn
  ∎
chad-equiv-DSemᵀ {Γ} a evIn (just (inj₂ ctg)) (inr {σ = σ} {τ = τ} t) ~τ ~Γ d-inr = {!   !}
chad-equiv-DSemᵀ {Γ} a evIn ctg (case' {σ = σ} {τ = τ} {ρ = ρ}  e l r) ~τ ~Γ d-case
  rewrite chad-preserves-primal (Etup-to-val a) e
  with interp e (Etup-to-val a) in interp-e-val≡inj-x
... | inj₁ x 
  rewrite simplify-exec-chad-case (Etup-to-val a) evIn ctg e l x inj₁
    = let -- DSemᵀ of subterms is defined
          dl : Is-just (DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a))
          dl = {!   !}
          de : Is-just (DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a )
          de = {!   !}
          -- Useful names
          ev'  = (zerov (D2τ' σ) .fst , evIn)
          body = LACMexec (interp (chad l) (Etup-to-val-primal (x , a)) .snd ctg .fst) ev'
          ctg-l = to-witness dl (sparse2dense ctg)
          -- Compatibility is preserved
          ev'≃ev = (≃Γ-intro-zero' σ evIn ~Γ)
          body-preserves≃Γ = chad-preserves-≃Γ (Etup-to-val (x , a)) ev' ctg l ~τ ev'≃ev
          body-preserves≃τ = ≃τ-congR (σ :+ τ) (just (inj₁ (body .fst))) (inj₁ x) (interp e (Etup-to-val a)) (sym interp-e-val≡inj-x) (fst body-preserves≃Γ)
          -- Induction hypothesis
          ih-e = chad-equiv-DSemᵀ a (body .snd) (just ∘ inj₁ $ body .fst) e body-preserves≃τ (snd body-preserves≃Γ) de
          ih-l = trans (chad-equiv-DSemᵀ (x , a) ev' ctg l ~τ ev'≃ev dl) 
                       (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' σ)}}) refl)
          ih = trans ih-e (cong₂ _ev+_ (gnoc (cong fst ih-l) λ q → Etup2EV (to-witness de (q , zerovDense (D2τ' τ)))) (cong snd ih-l))

          -- lemma-dsem-case = DSem'ᵀ-lemma-interp-case-cong a (sparse2dense ctg) e l r (inj₁ x) interp-e-val≡inj-x
    in begin
    LEtup2EV (LACMexec (interp (chad e) (Etup-to-val-primal a) .snd (just (inj₁ (body .fst))) .fst) (body .snd))
    ≡⟨ trans ih (sym $ ev+assoc _ _ _) ⟩
    (Etup2EV (to-witness de (ctg-l .fst , zerovDense (D2τ' τ))) ev+ Etup2EV (ctg-l .snd)) ev+ LEtup2EV evIn
    ≡⟨ ev+congL (DSemᵀ-lemma-interp-case-cong a e l r de d-case (inj₁ x) interp-e-val≡inj-x (sparse2dense ctg) dl) ⟩
    Etup2EV (to-witness d-case (sparse2dense ctg)) ev+ LEtup2EV evIn
    ∎
... | inj₂ x = {!   !}
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (snd' {σ = σ} {τ = τ} t) w1 w2 =
--   let ctg' = (just (zerov (D2τ' σ) .fst , ctg))
--   in begin
--   LEtup2EV (LACMexec (interp (chad (snd' t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ gnoc (simplify-exec-chad-snd (Etup-to-val a) evIn ctg t) LEtup2EV ⟩
--   LEtup2EV (LACMexec (interp (chad t) (primalVal (Etup-to-val a)) .snd ctg' .fst) evIn)
--     ≡⟨ chad-equiv-DSemᵀ a evIn ctg' t ((≃τ-zerov' σ) , w1)  w2 ⟩
--   Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} ctg')) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-pair-zeroL _ _ a _) Etup2EV) ⟩
--   Etup2EV (DSemᵀ (interp (snd' t) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (let' {σ = σ} {τ = τ} rhs body) w1 w2 =
--   let a' = (interp rhs (Etup-to-val a)) , a
--       body' = interp (chad body) (Etup-to-val-primal a') .snd ctg .fst
--       ev-body = LACMexec body' (zerov (D2τ' σ) .fst , evIn)
--       ih-body = trans (chad-equiv-DSemᵀ a' (zerov (D2τ' σ) .fst , evIn) ctg body w1 (≃Γ-intro-zero' σ evIn w2))
--                       (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' σ) }}) refl)
--       preserves-≃Γ = chad-preserves-≃Γ (Etup-to-val a') (zerov (D2τ' σ) .fst , evIn) ctg body w1 (≃Γ-intro-zero' σ evIn w2)
--       ih-rhs = chad-equiv-DSemᵀ a (ev-body .snd) (ev-body .fst) rhs (fst preserves-≃Γ) (snd preserves-≃Γ)
--       ih = trans ih-rhs (trans (ev+congR (cong snd ih-body)) (ev+congL (gnoc (gnoc (cong fst ih-body) (DSemᵀ (interp rhs ∘ Etup-to-val) a)) Etup2EV  ) ))

--       dsem-body = DSemᵀ {σ = σ :* (Etup Pr Γ)} {τ = τ} (interp body ∘ Etup-to-val) a' (sparse2dense ctg)
--       dsem-rhs = DSemᵀ (interp rhs ∘ Etup-to-val) a (Etup2EV dsem-body .fst)
--   in begin
--   LEtup2EV (LACMexec (interp (chad (let' rhs body)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ gnoc (simplify-exec-chad-let a Etup-to-val evIn ctg rhs body) LEtup2EV ⟩
--   LEtup2EV (LACMexec (interp (chad rhs) (Etup-to-val-primal a) .snd (ev-body .fst) .fst) (ev-body .snd))
--     ≡⟨ trans ih (sym (ev+assoc _ _ _)) ⟩
--   (Etup2EV dsem-rhs  ev+ Etup2EV dsem-body .snd ) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (DSemᵀ-lemma-interp-let a (sparse2dense ctg) rhs body) ⟩
--   Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = τ} (interp (let' rhs body) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (prim {σ = σ} {τ = τ} op t) w1 w2 =
--   let d-op = interp (dprim' op) (Etup-to-val (ctg , (primal σ (interp t (Etup-to-val a)), tt))) 
--   in begin
--   LEtup2EV (LACMexec (interp (chad (prim op t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ gnoc (simplify-exec-chad-primop (Etup-to-val a) evIn ctg t op) LEtup2EV ⟩
--   LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd d-op .fst) evIn)
--     ≡⟨ chad-equiv-DSemᵀ a evIn d-op t (dprim'-preserves-≃τ (Etup-to-val a) ctg op t w1) w2 ⟩
--   Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense d-op)) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (gnoc (evalprim-equiv-DSem (interp t (Etup-to-val a)) ctg op) (DSemᵀ _ a)) Etup2EV) ⟩
--   Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = σ} (interp t ∘ Etup-to-val) a (DSemᵀ {σ = σ} {τ = τ} (evalprim op) (interp t (Etup-to-val a)) (sparse2dense ctg))) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (sym (DSemᵀ-chain (evalprim op) (interp t ∘ Etup-to-val) a (sparse2dense ctg))) Etup2EV) ⟩
--   Etup2EV (DSemᵀ (evalprim op ∘ interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn nothing (inl {σ = σ} {τ = τ} t) w1 w2
--   rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (inl {σ = σ} {τ = τ} t ) tt w2 refl 
--   = DSemᵀ-lemma-ctg-zero-evIn'
-- chad-equiv-DSemᵀ {Γ} a evIn nothing (inr {σ = σ} {τ = τ} t) w1 w2
--   rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (inr {σ = σ} {τ = τ} t ) tt w2 refl 
--   = DSemᵀ-lemma-ctg-zero-evIn'
-- chad-equiv-DSemᵀ {Γ} a evIn (just (inj₁ ctg)) (inl {σ = σ} {τ = τ} t) w1 w2 =
--   begin
--   LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ chad-equiv-DSemᵀ a evIn ctg t w1 w2 ⟩
--   Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-inj₁ (interp t ∘ Etup-to-val) a (sparse2dense ctg) (zerovDense (D2τ' τ))) Etup2EV) ⟩
--   Etup2EV (DSemᵀ (inj₁ ∘ interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :+! D2τ' τ} (just (inj₁ ctg)))) ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn (just (inj₂ ctg)) (inr {σ = σ} {τ = τ} t) w1 w2 =
--   begin
--   LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ chad-equiv-DSemᵀ a evIn ctg t w1 w2 ⟩
--   Etup2EV (DSemᵀ (interp t ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-inj₂ (interp t ∘ Etup-to-val) a (zerovDense (D2τ' σ)) (sparse2dense ctg)) Etup2EV) ⟩
--   Etup2EV (DSemᵀ (inj₂ ∘ interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :+! D2τ' τ} (just (inj₂ ctg)))) ev+ LEtup2EV evIn
--   ∎  
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (case' {σ = σ} {τ = τ} {ρ = ρ} e l r) w1 w2
--   rewrite chad-preserves-primal (Etup-to-val a) e
--   with interp e (Etup-to-val a) in interp-e-val≡inj-x
-- ... | inj₁ x
--   rewrite simplify-exec-chad-case (Etup-to-val a) evIn ctg e l x inj₁
--   = let ev' = (zerov (D2τ' σ) .fst , evIn)
--         l' = LACMexec (interp (chad l) (Etup-to-val-primal (x , a)) .snd ctg .fst) ev'

--         ev'≃ev = (≃Γ-intro-zero' σ evIn w2)
--         l'-preserves≃Γ = chad-preserves-≃Γ (Etup-to-val (x , a)) ev' ctg l w1 ev'≃ev
--         l'-preserves≃τ = ≃τ-congR (σ :+ τ) (just (inj₁ (l' .fst))) (inj₁ x) (interp e (Etup-to-val a)) (sym interp-e-val≡inj-x) (fst l'-preserves≃Γ)

--         ih-e = chad-equiv-DSemᵀ a (l' .snd) (just (inj₁ (l' .fst))) e l'-preserves≃τ (snd l'-preserves≃Γ)
--         ih-l = trans (chad-equiv-DSemᵀ (x , a) ev' ctg l w1 ev'≃ev )
--                      (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' σ)}}) refl)
--         ih = trans ih-e (cong₂ _ev+_ (gnoc (cong fst ih-l) (λ q → Etup2EV (DSemᵀ (interp e ∘ Etup-to-val) a (q , zerovDense (D2τ' τ))))) (cong snd ih-l)) 

--         dsem-l = DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a) (sparse2dense ctg)
--         dsem-e = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a ( dsem-l .fst , zerovDense (D2τ' τ))
--         lemma-dsem-case = DSemᵀ-lemma-interp-case-cong a (sparse2dense ctg) e l r (inj₁ x) interp-e-val≡inj-x
--     in begin
--     LEtup2EV (LACMexec (interp (chad e) (Etup-to-val-primal a) .snd (just (inj₁ (l' .fst))) .fst) (l' .snd))
--       ≡⟨ trans ih (sym $ ev+assoc _ _ _) ⟩
--     (Etup2EV dsem-e ev+ Etup2EV (dsem-l .snd)) ev+ LEtup2EV evIn
--       ≡⟨ ev+congL lemma-dsem-case ⟩
--     Etup2EV (DSemᵀ {Etup Pr Γ} {ρ} (interp (case' e l r) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
--     ∎

-- ... | inj₂ x
--   rewrite simplify-exec-chad-case (Etup-to-val a) evIn ctg e r x inj₂
--   = let ev' = (zerov (D2τ' τ) .fst , evIn)
--         body = LACMexec (interp (chad r) (Etup-to-val-primal (x , a)) .snd ctg .fst) ev'

--         ev'≃ev = (≃Γ-intro-zero' τ evIn w2)
--         body-preserves≃Γ = chad-preserves-≃Γ (Etup-to-val (x , a)) ev' ctg r w1 ev'≃ev
--         body-preserves≃τ = ≃τ-congR (σ :+ τ) (just (inj₂ (body .fst))) (inj₂ x) (interp e (Etup-to-val a)) (sym interp-e-val≡inj-x) (fst body-preserves≃Γ)

--         ih-e = chad-equiv-DSemᵀ a (body .snd) (just (inj₂ (body .fst))) e body-preserves≃τ (snd body-preserves≃Γ)
--         ih-l = trans (chad-equiv-DSemᵀ (x , a) ev' ctg r w1 ev'≃ev )
--                      (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' τ)}}) refl)
--         ih = trans ih-e (cong₂ _ev+_ (gnoc (cong fst ih-l) (λ q → Etup2EV (DSemᵀ (interp e ∘ Etup-to-val) a (zerovDense (D2τ' σ) , q))) ) (cong snd ih-l))

--         dsem-body = DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a) (sparse2dense ctg)
--         dsem-e = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a ( zerovDense (D2τ' σ) , dsem-body .fst)

--         lemma-dsem-case = DSemᵀ-lemma-interp-case-cong a (sparse2dense ctg) e l r (inj₂ x) interp-e-val≡inj-x
--     in begin
--     LEtup2EV (LACMexec (interp (chad e) (Etup-to-val-primal a) .snd (just (inj₂ (body .fst))) .fst) (body .snd))
--       ≡⟨ trans ih (sym $ ev+assoc _ _ _) ⟩
--     (Etup2EV dsem-e ev+ Etup2EV (dsem-body .snd)) ev+ LEtup2EV evIn
--       ≡⟨ ev+congL lemma-dsem-case ⟩
--     Etup2EV (DSemᵀ {Etup Pr Γ} {ρ} (interp (case' e l r) ∘ Etup-to-val) a (sparse2dense ctg)) ev+ LEtup2EV evIn
--     ∎
 