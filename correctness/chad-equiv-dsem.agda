module correctness.chad-equiv-dsem where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Float using (primFloatPlus; primFloatTimes; primFloatNegate; primFloatLess)

open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)
open import Data.List using (map; _∷_; [])
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; _>>=_)
open import Data.Product using (_×_)
open import Function.Base using (_∘_; flip; _$_; case_of_; id)
open import Function.Bundles using (Equivalence; _⇔_ )
open import Relation.Binary.PropositionalEquality using (sym; inspect; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import spec
import spec.LACM as LACM
open import correctness.spec
open import correctness.dsem
open import correctness.dsyn-defined
open import correctness.lemmas
open import correctness.chad-preserves-compatibility
open import correctness.chad-ctg-zero
open import chad-preserves-primal

private 
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
evalprim-equiv-DSem x ctg SIGN d-op = sym (DSemᵀ-lemma-ctg-zero' d-op) 
evalprim-equiv-DSem tt ctg (LIT x) d-op = refl
evalprim-equiv-DSem x  ctg IADD    d-op = refl
evalprim-equiv-DSem x  ctg IMUL    d-op = refl
evalprim-equiv-DSem x  ctg INEG    d-op = refl

chad-equiv-DSemᵀ : {Γ : Env Pr} {τ : Typ Pr} 
    → let σ  = Etup Pr Γ 
          LΓ = map D2τ' Γ in
      (a : Rep σ) -- input of function
      (evIn : LEtup LΓ ) -- incoming LEtup
      (ctg : LinRep (D2τ' τ)) -- incoming cotangent
      (t : Term Pr Γ τ) -- primal function
    → ctg  ≃τ (interp t (Etup-to-val a)) -- compatible incoming cotangent
    → evIn ≃Γ Etup-to-val a -- compatible incoming LEtup
    → (∃-dsyn : DSyn-Exists (Etup-to-val a) t) -- function is differentiable at input
    → let dsem : Is-just (DSemᵀ (interp t ∘ Etup-to-val) a)
          dsem = DSyn-Exists→DSem-Exists a t ∃-dsyn
    in (LEtup2EV {LΓ} (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst ) evIn)
      ≡ Etup2EV {Γ} ( to-witness dsem (sparse2dense ctg)) ev+ LEtup2EV {LΓ} evIn)
chad-equiv-DSemᵀ = {!   !}
-- Cases where ctg is (semantically) zero
-- chad-equiv-DSemᵀ {Γ} a evIn tt unit ~τ ~Γ (∃dsyn dsyn) 
--   rewrite chad-ctg-zero (Etup-to-val a) evIn tt unit tt ~Γ refl
--   = DSemᵀ-ev-lemma-ctg-zero-evIn' (∃DSyn→∃DSem a unit tt)
-- chad-equiv-DSemᵀ {Γ} a evIn nothing (pair {σ = σ} {τ = τ} l r) ~τ ~Γ (∃dsyn dsyn)
--   rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (pair l r) tt ~Γ refl 
--   = DSemᵀ-ev-lemma-ctg-zero-evIn' (∃DSyn→∃DSem a (pair l r) dsyn)
-- chad-equiv-DSemᵀ {Γ} a evIn nothing (inl {σ = σ} {τ = τ} t) ~τ ~Γ (∃dsyn dsyn)
--   rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (inl {σ = σ} {τ = τ} t) tt ~Γ refl 
--   = DSemᵀ-ev-lemma-ctg-zero-evIn' (∃DSyn→∃DSem a (inl t) dsyn)
-- chad-equiv-DSemᵀ {Γ} a evIn nothing (inr {σ = σ} {τ = τ} t) ~τ ~Γ (∃dsyn dsyn)
--   rewrite chad-ctg-zero (Etup-to-val a) evIn nothing (inr {σ = σ} {τ = τ} t) tt ~Γ refl 
--   = DSemᵀ-ev-lemma-ctg-zero-evIn' (∃DSyn→∃DSem a (inr t) dsyn)
-- -- Cases where ctg is NOT (semantically) zero
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (var idx) ~τ ~Γ (∃dsyn dsyn) 
--   = let idx' = convIdx D2τ' idx
--         (d-var , eq) = DSemᵀ-var a idx (sparse2dense ctg)
--         dt = ∃DSyn→∃DSem a (var idx) dsyn
--   in begin
--   LEtup2EV (LACMexec (interp (chad (var idx)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ gnoc (LACMexec-add idx' ctg evIn) LEtup2EV ⟩
--   LEtup2EV (addLEτ idx' ctg evIn)
--     ≡⟨ onehot-equiv-addLEτ-lemma idx ctg evIn (Etup-to-val a) ~τ ~Γ ⟩
--   Etup2EV (onehot idx $ sparse2dense ctg) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (sym eq) Etup2EV) ⟩
--   Etup2EV (to-witness d-var (sparse2dense ctg)) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (DSemᵀ-extensionality _ _ (λ _ → refl) a d-var dt (sparse2dense ctg)) Etup2EV) ⟩
--   Etup2EV (to-witness dt (sparse2dense ctg)) ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn (just ctg) (pair {σ = σ} {τ = τ} l r) ~τ ~Γ (∃dsyn dsyn)
--   = let ctgL = _ ; ctgR = _
--         m1 = interp (chad l) (Etup-to-val-primal a) .snd ctgL .fst
--         m2 = interp (chad r) (Etup-to-val-primal a) .snd ctgR .fst

--         dt = ∃DSyn→∃DSem a (pair l r) dsyn
--         dl = ∃DSyn→∃DSem a l (dsyn .fst) 
--         dr = ∃DSyn→∃DSem a r (dsyn .snd)
--         ihr = chad-equiv-DSemᵀ a (LACMexec m1 evIn) ctgR r (~τ .snd) (chad-preserves-≃Γ (Etup-to-val a) evIn ctgL l (~τ .fst) ~Γ) (∃dsyn (dsyn .snd))
--         ihl = chad-equiv-DSemᵀ a evIn ctgL l (~τ .fst) ~Γ (∃dsyn (dsyn .fst))
--   in begin
--   LEtup2EV (LACMexec (LACMsequence m1 m2) evIn)
--     ≡⟨ gnoc (LACMexec-sequence m1 m2 evIn) LEtup2EV ⟩
--   LEtup2EV (LACMexec m2 (LACMexec m1 evIn))
--     ≡⟨ trans ihr (trans (ev+congR ihl) (trans (sym (ev+assoc _ _ _)) (ev+congL (ev+comm _ _)))) ⟩
--   (Etup2EV (to-witness dl (sparse2dense $ fst ctg )) ev+ Etup2EV (to-witness dr (sparse2dense $ snd ctg))) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (DSemᵀ-ev-lemma-pair (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) a (sparse2dense $ fst ctg) (sparse2dense $ snd ctg) dl dr dt) ⟩
--   (Etup2EV (to-witness dt (sparse2dense {D2τ' σ :*! D2τ' τ} (just ctg))) ev+ LEtup2EV evIn)
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (fst' {σ = σ} {τ = τ} t) ~τ ~Γ (∃dsyn dsyn)
--   = let ctg' = (just (ctg , zerov (D2τ' τ) .fst))
--         d-fst = ∃DSyn→∃DSem a (fst' t) dsyn
--         d-t = ∃DSyn→∃DSem a t dsyn 
--         d-snd = DSemᵀ-exists-lemma-pair₁ _ _ a d-t .snd
--   in begin
--   LEtup2EV (LACMexec (interp (chad (fst' t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ gnoc (simplify-exec-chad-fst (Etup-to-val a) evIn ctg t) LEtup2EV ⟩
--   LEtup2EV (LACMexec (interp (chad t) (primalVal (Etup-to-val a)) .snd ctg'  .fst) evIn)
--     ≡⟨ chad-equiv-DSemᵀ a evIn ctg' t (~τ , ≃τ-zerov' τ) ~Γ (∃dsyn dsyn) ⟩
--   Etup2EV (to-witness d-t (sparse2dense ctg , sparse2dense (zerov (D2τ' τ) .fst))) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-pair-zeroR (interp (fst' t) ∘ Etup-to-val) _ a d-t d-fst d-snd (sparse2dense ctg)) Etup2EV) ⟩
--   Etup2EV (to-witness d-fst $ sparse2dense ctg) ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (snd' {σ = σ} {τ = τ} t) ~τ ~Γ (∃dsyn dsyn)
--   = let ctg' = (just (zerov (D2τ' σ) .fst , ctg))
--         d-t = ∃DSyn→∃DSem a t dsyn 
--         d-snd = ∃DSyn→∃DSem a (snd' t) dsyn
--         d-fst = DSemᵀ-exists-lemma-pair₁ _ _ a d-t .fst
--   in begin
--   LEtup2EV (LACMexec (interp (chad (snd' t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ gnoc (simplify-exec-chad-snd (Etup-to-val a) evIn ctg t) LEtup2EV ⟩
--   LEtup2EV (LACMexec (interp (chad t) (primalVal (Etup-to-val a)) .snd ctg'  .fst) evIn)
--     ≡⟨ chad-equiv-DSemᵀ a evIn ctg' t (≃τ-zerov' σ , ~τ) ~Γ (∃dsyn dsyn) ⟩
--   Etup2EV (to-witness d-t (sparse2dense (zerov (D2τ' σ) .fst), sparse2dense ctg )) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-pair-zeroL _ (interp (snd' t) ∘ Etup-to-val) a d-t d-fst d-snd (sparse2dense ctg)) Etup2EV) ⟩
--   Etup2EV (to-witness d-snd $ sparse2dense ctg) ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (let' {σ = σ} {τ = τ} rhs body) ~τ ~Γ (∃dsyn dsyn) =
--   let -- DSems of subterms are defined
--       dt = ∃DSyn→∃DSem a (let' rhs body) dsyn
--       d-rhs = ∃DSyn→∃DSem a rhs (dsyn .fst) 
--       d-body = ∃DSyn→∃DSem (interp rhs (Etup-to-val a) , a) body (dsyn .snd)
--       -- Helpful shorthands
--       a' = (interp rhs (Etup-to-val a)) , a
--       ctg-body = to-witness d-body (sparse2dense ctg)
--       ev-body = LACMexec (interp (chad body) (Etup-to-val-primal a') .snd ctg .fst) (zerov (D2τ' σ) .fst , evIn)
--       -- Induction hypothesis
--       preserves-≃Γ = chad-preserves-≃Γ (Etup-to-val a') (zerov (D2τ' σ) .fst , evIn) ctg body ~τ (≃Γ-intro-zero' σ evIn ~Γ)
--       ih-body = trans (chad-equiv-DSemᵀ a' (zerov (D2τ' σ) .fst , evIn) ctg body ~τ (≃Γ-intro-zero' σ evIn ~Γ) (∃dsyn (dsyn .snd)))
--                       (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' σ) }}) refl)
--       ih-rhs = chad-equiv-DSemᵀ a (ev-body .snd) (ev-body .fst) rhs (fst preserves-≃Γ) (snd preserves-≃Γ) (∃dsyn (dsyn .fst))
--       ih = trans ih-rhs (trans (ev+congR (cong snd ih-body)) (ev+congL (gnoc (gnoc (cong fst ih-body) (to-witness d-rhs)) Etup2EV)))
--   in begin
--   LEtup2EV (LACMexec (interp (chad (let' rhs body)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ gnoc (simplify-exec-chad-let a Etup-to-val evIn ctg rhs body) LEtup2EV ⟩
--   LEtup2EV (LACMexec (interp (chad rhs) (Etup-to-val-primal a) .snd (ev-body .fst) .fst) (ev-body .snd))
--     ≡⟨ trans ih (sym $ ev+assoc _ _ _) ⟩
--   (Etup2EV (to-witness d-rhs (fst ctg-body)) ev+ Etup2EV (snd ctg-body)) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (DSemᵀ-lemma-interp-let a (sparse2dense ctg) rhs body dt d-rhs d-body) ⟩
--   Etup2EV (to-witness dt (sparse2dense ctg)) ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (prim {σ = σ} {τ = τ} op t) ~τ ~Γ (∃dsyn dsyn) =
--   let d-chad-op = interp (dprim' op) (Etup-to-val (ctg , (primal σ (interp t (Etup-to-val a)), tt))) 
--       d-prim = ∃DSyn→∃DSem a (prim op t) dsyn
--       d-t = ∃DSyn→∃DSem a t (dsyn .snd) 
--       d-op = dsyn .fst
--   in begin
--   LEtup2EV (LACMexec (interp (chad (prim op t)) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ gnoc (simplify-exec-chad-primop (Etup-to-val a) evIn ctg t op) LEtup2EV ⟩
--   LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd d-chad-op .fst) evIn)
--     ≡⟨ chad-equiv-DSemᵀ a evIn d-chad-op t (dprim'-preserves-≃τ (Etup-to-val a) ctg op t ~τ) ~Γ (∃dsyn (dsyn .snd)) ⟩
--   Etup2EV (to-witness d-t $ sparse2dense d-chad-op) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (gnoc (evalprim-equiv-DSem (interp t (Etup-to-val a)) ctg op d-op) (to-witness d-t)) Etup2EV) ⟩
--   Etup2EV (to-witness d-t (to-witness d-op $ sparse2dense ctg)) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (sym (DSemᵀ-lemma-chain (evalprim op) (interp t ∘ Etup-to-val) a d-op d-t d-prim (sparse2dense ctg))) Etup2EV) ⟩
--   Etup2EV (to-witness d-prim $ sparse2dense ctg) ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn (just (inj₁ ctg)) (inl {σ = σ} {τ = τ} t) ~τ ~Γ (∃dsyn dsyn) =
--   let ctg' = sparse2dense {D2τ' σ :+! D2τ' τ} (just (inj₁ ctg))
--       d-inl = ∃DSyn→∃DSem a (inl t) dsyn
--       dt = ∃DSyn→∃DSem a t dsyn
--   in begin
--   LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ chad-equiv-DSemᵀ a evIn ctg t ~τ ~Γ (∃dsyn dsyn) ⟩
--   Etup2EV (to-witness dt (sparse2dense ctg)) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-inj₁ _ a dt d-inl _ _) Etup2EV) ⟩
--   Etup2EV (to-witness d-inl ctg') ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn (just (inj₂ ctg)) (inr {σ = σ} {τ = τ} t) ~τ ~Γ (∃dsyn dsyn) =
--   let ctg' = sparse2dense {D2τ' σ :+! D2τ' τ} (just (inj₂ ctg))
--       d-inr = ∃DSyn→∃DSem a (inr t) dsyn
--       dt = ∃DSyn→∃DSem a t dsyn
--   in begin
--   LEtup2EV (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst) evIn)
--     ≡⟨ chad-equiv-DSemᵀ a evIn ctg t ~τ ~Γ (∃dsyn dsyn) ⟩
--   Etup2EV (to-witness dt (sparse2dense ctg)) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (gnoc (DSemᵀ-lemma-inj₂ _ a dt d-inr _ _) Etup2EV) ⟩
--   Etup2EV (to-witness d-inr ctg') ev+ LEtup2EV evIn
--   ∎
-- chad-equiv-DSemᵀ {Γ} a evIn ctg (case' {σ = σ} {τ = τ} {ρ = ρ} e l r) ~τ ~Γ dsyn
--   rewrite chad-preserves-primal (Etup-to-val a) e
--   with interp e (Etup-to-val a) in interp-e-val≡inj-x | dsyn
-- ... | inj₁ x | ∃dsyn dsyn
--   rewrite simplify-exec-chad-case (Etup-to-val a) evIn ctg e l x inj₁
--     = begin
--     LEtup2EV (LACMexec (interp (chad e) (Etup-to-val-primal a) .snd (just (inj₁ (body .fst))) .fst) (body .snd))
--     ≡⟨ trans ih (sym $ ev+assoc _ _ _) ⟩
--     (Etup2EV (to-witness de (ctg-l .fst , zerovDense (D2τ' τ))) ev+ Etup2EV (ctg-l .snd)) ev+ LEtup2EV evIn
--     ≡⟨ ev+congL (DSemᵀ-lemma-cong-interp-case a e l r de (∃dsyn dsyn) (sparse2dense ctg) (inj₁ x) interp-e-val≡inj-x dl)  ⟩
--     Etup2EV (to-witness d-case (sparse2dense ctg)) ev+ LEtup2EV evIn
--     ∎
--     where -- DSemᵀ of subterms is defined
--           d-case : Is-just (DSemᵀ {Etup Pr Γ} {ρ} (interp (case' e l r) ∘ Etup-to-val) a)
--           d-case = ∃DSyn→∃DSem a (case' e l r) dsyn
--           apply-eq-to-dsyn : [ (λ v' → DSyn-ExistsP (push v' (Etup-to-val a)) l) , (λ v' → DSyn-ExistsP (push v' (Etup-to-val a)) r) ] (interp e $ Etup-to-val a) ≡ DSyn-ExistsP (push x (Etup-to-val a)) l
--           apply-eq-to-dsyn rewrite interp-e-val≡inj-x = refl
--           dsyn' : DSyn-ExistsP (push x (Etup-to-val a)) l
--           dsyn' rewrite (sym apply-eq-to-dsyn) = dsyn .snd
--           dl : Is-just (DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a))
--           dl = ∃DSyn→∃DSem (x , a) l dsyn'
--           de : Is-just (DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a )
--           de = ∃DSyn→∃DSem a e (dsyn .fst)
--           -- useful names
--           ev'  = (zerov (D2τ' σ) .fst , evIn)
--           body = LACMexec (interp (chad l) (Etup-to-val-primal (x , a)) .snd ctg .fst) ev'
--           ctg-l = to-witness dl (sparse2dense ctg)
--           -- Compatibility is preserved
--           ev'≃ev = (≃Γ-intro-zero' σ evIn ~Γ)
--           body-preserves≃Γ = chad-preserves-≃Γ (Etup-to-val (x , a)) ev' ctg l ~τ ev'≃ev
--           body-preserves≃τ = ≃τ-congR (σ :+ τ) (just (inj₁ (body .fst))) (inj₁ x) (interp e (Etup-to-val a)) (sym interp-e-val≡inj-x) (fst body-preserves≃Γ)
--           -- Induction hypothesis
--           ih-e = chad-equiv-DSemᵀ a (body .snd) (just ∘ inj₁ $ body .fst) e body-preserves≃τ (snd body-preserves≃Γ) (∃dsyn (dsyn .fst))
--           ih-l = trans (chad-equiv-DSemᵀ (x , a) ev' ctg l ~τ ev'≃ev (∃dsyn dsyn')) 
--                        (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' σ)}}) refl)
--           ih = trans ih-e (cong₂ _ev+_ (gnoc (cong fst ih-l) λ q → Etup2EV (to-witness de (q , zerovDense (D2τ' τ)))) (cong snd ih-l))
-- ... | inj₂ x | ∃dsyn dsyn 
--   rewrite simplify-exec-chad-case (Etup-to-val a) evIn ctg e r x inj₂
--   = begin
--   LEtup2EV (LACMexec (interp (chad e) (Etup-to-val-primal a) .snd (just (inj₂ (body .fst))) .fst) (body .snd))
--   ≡⟨ trans ih (sym $ ev+assoc _ _ _) ⟩
--   (Etup2EV (to-witness de ( zerovDense (D2τ' σ) , ctg-r .fst )) ev+ Etup2EV (ctg-r .snd)) ev+ LEtup2EV evIn
--   ≡⟨ ev+congL (DSemᵀ-lemma-cong-interp-case a e l r de (∃dsyn dsyn) (sparse2dense ctg) (inj₂ x) interp-e-val≡inj-x dr)  ⟩
--   Etup2EV (to-witness d-case (sparse2dense ctg)) ev+ LEtup2EV evIn
--   ∎
--   where -- DSemᵀ of subterms is defined
--         d-case : Is-just (DSemᵀ {Etup Pr Γ} {ρ} (interp (case' e l r) ∘ Etup-to-val) a)
--         d-case = ∃DSyn→∃DSem a (case' e l r) dsyn
--         apply-eq-to-dsyn : [ (λ v' → DSyn-ExistsP (push v' (Etup-to-val a)) l) , (λ v' → DSyn-ExistsP (push v' (Etup-to-val a)) r) ] (interp e $ Etup-to-val a) ≡ DSyn-ExistsP (push x (Etup-to-val a)) r
--         apply-eq-to-dsyn rewrite interp-e-val≡inj-x = refl
--         dsyn' : DSyn-ExistsP (push x (Etup-to-val a)) r
--         dsyn' rewrite (sym apply-eq-to-dsyn) = dsyn .snd
--         dr : Is-just (DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a))
--         dr = ∃DSyn→∃DSem (x , a) r dsyn'
--         de : Is-just (DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a )
--         de = ∃DSyn→∃DSem a e (dsyn .fst)
--         -- useful names
--         ev'  = (zerov (D2τ' τ) .fst , evIn)
--         body = LACMexec (interp (chad r) (Etup-to-val-primal (x , a)) .snd ctg .fst) ev'
--         ctg-r = to-witness dr (sparse2dense ctg)
--         -- Compatibility is preserved
--         ev'≃ev = (≃Γ-intro-zero' τ evIn ~Γ)
--         body-preserves≃Γ = chad-preserves-≃Γ (Etup-to-val (x , a)) ev' ctg r ~τ ev'≃ev
--         body-preserves≃τ = ≃τ-congR (σ :+ τ) (just (inj₂ (body .fst))) (inj₂ x) (interp e (Etup-to-val a)) (sym interp-e-val≡inj-x) (fst body-preserves≃Γ)
--         -- Induction hypothesis
--         ih-e = chad-equiv-DSemᵀ a (body .snd) (just ∘ inj₂ $ body .fst) e body-preserves≃τ (snd body-preserves≃Γ) (∃dsyn (dsyn .fst))
--         ih-l = trans (chad-equiv-DSemᵀ (x , a) ev' ctg r ~τ ev'≃ev (∃dsyn dsyn')) 
--                       (cong₂ _,_ (plusvDense-zeroR' {{zerov-equiv-zerovDense (D2τ' τ)}}) refl)
--         ih = trans ih-e (cong₂ _ev+_ (gnoc (cong fst ih-l) λ q → Etup2EV (to-witness de (zerovDense (D2τ' σ) , q))) (cong snd ih-l))