{-# OPTIONS --allow-unsolved-metas #-}
module correctness.lemmas.dsem-lemmas where 

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function.Base using (_$_; _∘_; id; case_of_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; inspect)
import Relation.Binary.PropositionalEquality as Equality
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import correctness.lemmas.environment-vector-lemmas

open import spec
open import correctness.spec
open import correctness.dsem
import spec.LACM as LACM


onehot-equiv-addLEτ-lemma : {Γ : Env Pr} {τ : Typ Pr}
    → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
    in (ctg : LinRep (D2τ' τ))
    → (evIn : LEtup (map D2τ' Γ) )
    → Compatible-idx-LEtup (idx , ctg) evIn
    → LEtup2EV (addLEτ idx' ctg evIn)
      ≡ (Etup2EV (onehot idx (sparse2dense ctg)) ev+ LEtup2EV evIn)
onehot-equiv-addLEτ-lemma {τ ∷ Γ}  Z      ctg (x , xs) w = cong₂ _,_ (plusv-equiv-plusvDense ctg x w) (sym (ev+zeroL' Etup-zerovDense-equiv-zero-EV))
onehot-equiv-addLEτ-lemma {τ ∷ Γ} (S idx) ctg (x , xs) w = cong₂ _,_ (sym plusvDense-zeroL') (onehot-equiv-addLEτ-lemma idx ctg xs w)

DSemᵀ-lemma-ctg-zero' : {σ τ : Typ Pr} { f : Rep σ  →  Rep τ } { a : Rep σ }
                { ctg : LinRepDense (D2τ' τ) }
                → {{ ctg ≡ zerovDense (D2τ' τ) }}
        → DSemᵀ {σ} {τ} f a ctg ≡ zerovDense (D2τ' σ)
DSemᵀ-lemma-ctg-zero' {f = f} {a = a} {{ refl }} = DSemᵀ-ctg-zero f a

DSemᵀ-lemma-ctg-zeroLEnv : {Γ : Env Pr} {τ : Typ Pr}
                → let σ = Etup Pr Γ in
                ( f : Rep σ  →  Rep τ ) 
                ( a : Rep σ ) 
                ( ctg : LinRepDense (D2τ' τ) )
                → ( ctg ≡ zerovDense (D2τ' τ))
                → Etup2EV (DSemᵀ {σ} {τ} f a ctg) ≡ zero-EV (map D2τ' Γ)
DSemᵀ-lemma-ctg-zeroLEnv {σ} {τ} f a ctg w = trans (cong (Etup2EV ∘ (DSemᵀ f a)) w)
                                                (trans (cong Etup2EV DSemᵀ-lemma-ctg-zero') 
                                                      Etup-zerovDense-equiv-zero-EV) 

DSemᵀ-lemma-ctg-zeroLEnv' : {Γ : Env Pr} {τ : Typ Pr}
                → let σ = Etup Pr Γ
                in { f : Rep σ  →  Rep τ } 
                    { a : Rep σ } 
                    { ctg : LinRepDense (D2τ' τ) }
                →  {{ ctg ≡ zerovDense (D2τ' τ) }}
                → Etup2EV (DSemᵀ {σ} {τ} f a ctg) ≡ zero-EV (map D2τ' Γ) 
DSemᵀ-lemma-ctg-zeroLEnv' {σ} {τ} {f} {a} {ctg} {{w}} = DSemᵀ-lemma-ctg-zeroLEnv f a ctg w

DSemᵀ-lemma-pair : {Γ : Env Pr} {τ1 τ2 : Typ Pr}
        → let σ  = Etup Pr Γ 
        in (f : Rep σ →  Rep τ1) 
        → (g : Rep σ →  Rep τ2) 
        → (a : Rep σ)
        → (ctg-f : LinRepDense (D2τ' τ1))
        → (ctg-g : LinRepDense (D2τ' τ2))
        → let dsem-f = DSemᵀ {σ} {τ1} f a ctg-f
              dsem-g = DSemᵀ {σ} {τ2} g a ctg-g
              h : Rep σ → Rep (τ1 :* τ2)
              h e = (f e , g e)
              ctg : LinRepDense (D2τ' (τ1 :* τ2))
              ctg = (ctg-f , ctg-g)
          in Etup2EV dsem-f ev+ Etup2EV dsem-g
              ≡ Etup2EV (DSemᵀ {σ} {τ1 :* τ2} h a ctg)
DSemᵀ-lemma-pair f g a ctg-f ctg-g = sym $ trans (cong Etup2EV (DSemᵀ-pair f g a ctg-f ctg-g))
                                            (plusvDense-equiv-ev+ (DSemᵀ f a ctg-f) (DSemᵀ g a ctg-g))

-- TODO: Betere naam verzinnen, dit zou de naam moeten zijn van een Lemma die zegt dat fst linear is
DSemᵀ-lemma-fst : {Γ : Env Pr} {τ1 τ2 : Typ Pr}
        → let σ  = Etup Pr Γ 
        in (f : Rep σ →  Rep τ1) 
        → (g : Rep σ →  Rep τ2) 
        → (a : Rep σ)
        → (ctg-f : LinRepDense (D2τ' τ1))
        → let ctg-g = sparse2dense (zerov (D2τ' τ2) .fst)
              ctg : LinRepDense (D2τ' (τ1 :* τ2))
              ctg = (ctg-f , ctg-g)
              h : Rep σ → Rep (τ1 :* τ2)
              h e = (f e , g e)
          in DSemᵀ {σ} {τ1 :* τ2} h a ctg 
              ≡ DSemᵀ {σ} {τ1} f a ctg-f
DSemᵀ-lemma-fst {Γ} {τ1} {τ2} f g a ctg-f =
  let ctg-g = (sparse2dense (zerov (D2τ' τ2) .fst))
  in trans (DSemᵀ-pair f g a ctg-f ctg-g) (plusvDense-zeroR' {{DSemᵀ-lemma-ctg-zero' {{zerov-equiv-zerovDense (D2τ' τ2)}}}})

DSemᵀ-lemma-snd : {Γ : Env Pr} {τ1 τ2 : Typ Pr}
        → let σ  = Etup Pr Γ 
        in (f : Rep σ →  Rep τ1) 
        → (g : Rep σ →  Rep τ2) 
        → (a : Rep σ)
        → (ctg-g : LinRepDense (D2τ' τ2))
        → let ctg-f = sparse2dense (zerov (D2τ' τ1) .fst)
              ctg : LinRepDense (D2τ' (τ1 :* τ2))
              ctg = (ctg-f , ctg-g)
              h : Rep σ → Rep (τ1 :* τ2)
              h e = (f e , g e)
          in DSemᵀ {σ} {τ1 :* τ2} h a ctg 
              ≡ DSemᵀ {σ} {τ2} g a ctg-g
DSemᵀ-lemma-snd {Γ} {τ1} {τ2} f g a ctg-g = 
  let ctg-f = (sparse2dense (zerov (D2τ' τ1) .fst))
  in trans (DSemᵀ-pair f g a ctg-f ctg-g) (plusvDense-zeroL' {{DSemᵀ-lemma-ctg-zero' {{zerov-equiv-zerovDense (D2τ' τ1)}}}}) 


DSemᵀ-lemma-interp-let : {Γ : Env Pr} {σ τ : Typ Pr}
  → (a : Rep (Etup Pr Γ))
  → (ctg : LinRepDense (D2τ' τ))
  → (rhs : Term Pr Γ σ)
  → (body : Term Pr (σ ∷ Γ) τ)
  → let a' = (interp rhs (Etup-to-val a)) , a
        dsem-body = DSemᵀ {σ = σ :* (Etup Pr Γ)} {τ = τ} (interp body ∘ Etup-to-val) a' ctg
        dsem-rhs = DSemᵀ {σ = Etup Pr Γ } {τ = σ} (interp rhs ∘ Etup-to-val) a (Etup2EV dsem-body .fst)
    in (Etup2EV dsem-rhs ev+ Etup2EV dsem-body .snd)
        ≡ Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = τ} (interp (let' rhs body) ∘ Etup-to-val) a ctg)
DSemᵀ-lemma-interp-let {Γ} {σ} {τ} a ctg rhs body =
  let -- Expressions used for applying the chain rule
      f : (env : Rep (Etup Pr (σ ∷ Γ))) → Rep τ
      f = interp body ∘ Etup-to-val
      g : (env : Rep (Etup Pr Γ)) → Rep σ × Rep (Etup Pr Γ) -- Note that g constructs a pair, thus we can use the pair rule of DSem on it
      g = (λ env → (interp rhs (Etup-to-val env) , env))

      dsem-body = DSemᵀ {σ = σ :* (Etup Pr Γ)} {τ = τ} f (g a) ctg
      dsem-rhs = DSemᵀ {σ = Etup Pr Γ } {τ = σ} (fst ∘ g) a (Etup2EV dsem-body .fst)
  in begin
  Etup2EV dsem-rhs ev+ Etup2EV dsem-body .snd
    ≡⟨ ev+congR (sym (cong Etup2EV (DSemᵀ-identity a (dsem-body .snd)))) ⟩
  Etup2EV dsem-rhs ev+ Etup2EV (DSemᵀ id a (dsem-body .snd))
    ≡⟨ DSemᵀ-lemma-pair (interp rhs ∘ Etup-to-val) id a (dsem-body .fst) (dsem-body .snd) ⟩
  Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = σ :* Etup Pr Γ} g a (DSemᵀ {σ = σ :* Etup Pr Γ} {τ = τ} f (g a) ctg))
    ≡⟨ cong Etup2EV (sym (DSemᵀ-chain f g a ctg)) ⟩
  Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = τ} (f ∘ g) a ctg)
    ≡⟨⟩
  Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = τ} (interp (let' rhs body) ∘ Etup-to-val) a ctg)
  ∎

DSemᵀ-lemma-inj₁ : {σ τ ρ : Typ Pr}
        → (f : Rep σ →  Rep τ) → (a : Rep σ)
        → (ctgL : LinRepDense (D2τ' τ)) → (ctgR : LinRepDense (D2τ' ρ))
        → DSemᵀ {σ} {τ} f a ctgL
          ≡ DSemᵀ {σ} {τ :+ ρ} (inj₁ ∘ f) a ( ctgL , ctgR ) 
DSemᵀ-lemma-inj₁ {σ} {τ} {ρ} f a ctgL ctgR =
  begin
  DSemᵀ f a ctgL
    ≡⟨ cong (DSemᵀ f a) (sym (DSemᵀ-inj₁ (f a) (ctgL , ctgR))) ⟩
  DSemᵀ f a (DSemᵀ inj₁ (f a) (ctgL , ctgR))
    ≡⟨ sym (DSemᵀ-chain inj₁ f a (ctgL , ctgR)) ⟩
  DSemᵀ {σ} {τ :+ ρ} (inj₁ ∘ f) a (ctgL , ctgR)
  ∎

DSemᵀ-lemma-inj₂ : {σ τ ρ : Typ Pr}
        → (f : Rep σ →  Rep τ) → (a : Rep σ)
        → (ctgL : LinRepDense (D2τ' ρ)) → (ctgR : LinRepDense (D2τ' τ))
        → DSemᵀ {σ} {τ} f a ctgR
          ≡ DSemᵀ {σ} {ρ :+ τ} (inj₂ ∘ f) a ( ctgL , ctgR ) 
DSemᵀ-lemma-inj₂ {σ} {τ} {ρ} f a ctgL ctgR =
  begin
  DSemᵀ f a ctgR
    ≡⟨ cong (DSemᵀ f a) (sym (DSemᵀ-inj₂ (f a) (ctgL , ctgR))) ⟩
  DSemᵀ f a (DSemᵀ inj₂ (f a) (ctgL , ctgR))
    ≡⟨ sym (DSemᵀ-chain inj₂ f a (ctgL , ctgR)) ⟩
  DSemᵀ {σ} {ρ :+ τ} (inj₂ ∘ f) a (ctgL , ctgR)
  ∎

fst-case : {A B : Set} {σ τ : Typ Pr}
        → (x : Rep (σ :+ τ))
        → (a₁ : Rep σ → A) (a₂ : Rep τ → A)
        → (b₁ : Rep σ → B) (b₂ : Rep τ → B)
        → let f : (Rep (σ :+ τ)) → A × B
              f = λ where (inj₁ z) → (a₁ z , b₁ z)
                          (inj₂ z) → (a₂ z , b₂ z)
                  
              g : (Rep (σ :+ τ)) → A
              g = λ where (inj₁ z) → a₁ z
                          (inj₂ z) → a₂ z
          in fst (f x) ≡ g x
fst-case (inj₁ x) a₁ a₂ b₁ b₂ = refl
fst-case (inj₂ y) a₁ a₂ b₁ b₂ = refl

DSemᵀ-lemma-interp-case : {Γ : Env Pr} {σ τ ρ : Typ Pr}
  → (a : Rep (Etup Pr Γ))
  → (ctg : LinRepDense (D2τ' ρ))
  → (e : Term Pr Γ (σ :+ τ))
  → (l : Term Pr (σ ∷ Γ) ρ)
  → (r : Term Pr (τ ∷ Γ) ρ)
  → case interp e (Etup-to-val a) of
      λ where
      (inj₁ x) → let dsem-l = DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a) ctg
                     dsem-e = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (dsem-l .fst , zerovDense (D2τ' τ))
                 in Etup2EV dsem-e ev+ Etup2EV (dsem-l .snd)
                 ≡ Etup2EV (DSemᵀ (interp (case' e l r) ∘ Etup-to-val) a ctg)
      (inj₂ x) → let dsem-r = DSemᵀ {τ :* Etup Pr Γ} {ρ} (interp r ∘ Etup-to-val) (x , a) ctg
                     dsem-e = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (zerovDense (D2τ' σ),  dsem-r .fst)
                 in Etup2EV dsem-e ev+ Etup2EV (dsem-r .snd)
                 ≡ Etup2EV (DSemᵀ (interp (case' e l r) ∘ Etup-to-val) a ctg)
DSemᵀ-lemma-interp-case {Γ} {σ} {τ} {ρ} a ctg e l r
  using f ← λ (zs , a) → [ (λ z → interp l (Etup-to-val (z , a))) 
                          ,(λ z → interp r (Etup-to-val (z , a)))
                         ] zs
  using g ← λ a → ( interp e (Etup-to-val a) , a)
  with interp e (Etup-to-val a) | inspect (interp e) (Etup-to-val a)
... | (inj₁ x) | Equality.[_] interp-e-val≡inj₁-x =
  let dsem-l = DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a) ctg
      dsem-e = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (dsem-l .fst , zerovDense (D2τ' τ))
      dsem-f = DSemᵀ {(σ :+ τ) :* (Etup Pr Γ)} {ρ} f (inj₁ x , a) ctg
      dsem-g = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (dsem-f .fst)

      case-lemma : ( (dsem-l .fst , zerovDense (D2τ' τ)) , dsem-l .snd) ≡ dsem-f
      case-lemma = sym (DSemᵀ-case8 {σ} {τ} {Etup Pr Γ} {ρ} (inj₁ x , a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) ctg)

  in begin
  Etup2EV dsem-e ev+ Etup2EV (dsem-l .snd)
  ≡⟨ cong₂ _ev+_ (cong Etup2EV (cong (DSemᵀ (interp e ∘ Etup-to-val) a) (cong fst case-lemma))) (cong Etup2EV (cong snd case-lemma)) ⟩
  Etup2EV dsem-g ev+ Etup2EV (dsem-f .snd)
  ≡⟨ ev+congR (cong Etup2EV (sym (DSemᵀ-identity a (dsem-f .snd)))) ⟩
  Etup2EV dsem-g ev+ Etup2EV (DSemᵀ {Etup Pr Γ} {Etup Pr Γ} id a (dsem-f .snd))
  ≡⟨ DSemᵀ-lemma-pair (interp e ∘ Etup-to-val) id a (dsem-f .fst) (dsem-f .snd) ⟩
  Etup2EV (DSemᵀ {Etup Pr Γ} {(σ :+ τ) :* (Etup Pr Γ)} g a dsem-f)
  ≡⟨ cong Etup2EV (cong (DSemᵀ g a) (cong (λ q → DSemᵀ {(σ :+ τ) :* (Etup Pr Γ)} {ρ} f q ctg) (cong₂ (_,_) (sym interp-e-val≡inj₁-x) refl))) ⟩
  Etup2EV (DSemᵀ {Etup Pr Γ} {(σ :+ τ) :* (Etup Pr Γ)} g a (DSemᵀ {(σ :+ τ) :* (Etup Pr Γ)} {ρ} f (g a) ctg))
  ≡⟨ cong Etup2EV (sym (DSemᵀ-chain f g a ctg)) ⟩
  Etup2EV (DSemᵀ (f ∘ g) a ctg)
  ≡⟨ cong Etup2EV (DSemᵀ-extensionality {Etup Pr Γ} {ρ} (f ∘ g) (interp (case' e l r) ∘ Etup-to-val) a ctg w) ⟩
  Etup2EV (DSemᵀ (λ a' → interp (case' e l r) (Etup-to-val a')) a ctg)
  ≡⟨⟩
  Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = ρ} (interp (case' e l r) ∘ Etup-to-val) a ctg)
  ∎
  where -- f : Rep ((σ :+ τ) :* (Etup Pr Γ)) → Rep ρ
        -- f = λ (zs , a) → [ (λ z → interp l (Etup-to-val (z , a))) 
        --                   ,(λ z → interp r (Etup-to-val (z , a)))
        --                  ] zs
        -- g : Rep (Etup Pr Γ) → Rep ((σ :+ τ) :* (Etup Pr Γ)) 
        -- g = λ a → ( interp e (Etup-to-val a) , a)
        w : (y : Rep (Etup Pr Γ)) → (f ∘ g) y ≡ interp (case' e l r) (Etup-to-val y) -- TODO: extract this lemma
        w y with interp e (Etup-to-val y)
        ... | inj₁ _ = refl
        ... | inj₂ _ = refl
... | (inj₂ x) | _ = {!   !}
  -- Etup2EV (DSemᵀ (λ a' → [  (λ y → interp l (Etup-to-val (y , a')))
  --                         , (λ y → interp r (Etup-to-val (y , a')))
  --                        ] (interp e (Etup-to-val a'))
  --                )
  --                 a ctg)
  -- ?
  -- -- Etup2EV (DSemᵀ {Etup Pr Γ} {(σ :+ τ) :* (Etup Pr Γ)} g a
  -- --           (match-inj ((σ :+ τ) :* (Etup Pr Γ)) ρ 
  -- --               ?
  -- --               ?
  -- --               (g a)
  -- --           ))
  -- ≡⟨ cong Etup2EV {!   !} ⟩
  -- Etup2EV (DSemᵀ {Etup Pr Γ} {(σ :+ τ) :* (Etup Pr Γ)} g a (DSemᵀ {(σ :+ τ) :* (Etup Pr Γ)} {ρ} f (g a) ctg))
  -- ≡⟨ cong Etup2EV (sym (DSemᵀ-lemma-chain-app f g a ctg)) ⟩
  -- Etup2EV (DSemᵀ (f ∘ g) a ctg)
  -- ≡⟨ cong Etup2EV (DSemᵀ-extensionality {Etup Pr Γ} {ρ} (f ∘ g) (interp (case' e l r) ∘ Etup-to-val) a ctg w) ⟩