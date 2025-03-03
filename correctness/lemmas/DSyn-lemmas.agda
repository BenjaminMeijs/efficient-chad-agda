module correctness.lemmas.DSyn-lemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (primFloatLess)

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; isInj₁; isInj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; _>>=_)
open import Data.Product using (_×_; Σ)
open import Data.List using ([]; _∷_)
open import Function.Base using (_∘_; _$_; case_of_; id)
open import Relation.Binary.PropositionalEquality using (sym; _≗_)
import Data.Maybe.Relation.Unary.Any as Any

open import spec
open import correctness.spec
open import correctness.dsem
open import correctness.lemmas.dsem-lemmas



-- TODO: move this to simplify interp-exec-chad? 
-- It is also used in dsem-lemmas 
private module case-helper {Γ : Env Pr} {σ τ ρ : Typ Pr} (a : Rep (Etup Pr Γ)) (e : Term Pr Γ (σ :+ τ)) (l : Term Pr (σ ∷ Γ) ρ) (r : Term Pr (τ ∷ Γ) ρ) where
    f : (Rep $ (σ :+ τ) :* Etup Pr Γ) → Rep ρ
    f = λ (cond , a') → [ (λ v → interp l $ Etup-to-val (v , a'))
                        , (λ v → interp r $ Etup-to-val (v , a'))
                        ] cond
    g : (a' : Rep (Etup Pr Γ)) → Rep ((σ :+ τ) :* Etup Pr Γ)
    g = λ a' → interp e (Etup-to-val a') , a'

    case-simp-ext : (f ∘ g) ≗ interp (case' e l r) ∘ Etup-to-val
    case-simp-ext a' with (interp e (Etup-to-val a'))
    ... | inj₁ _ = refl
    ... | inj₂ _ = refl

private
    unpack-isInj₁ : {A B : Set} (x : A) (y : A ⊎ B)
          → (y ≡ inj₁ x)
          → (w : Is-just (isInj₁ y)) 
          → (x ≡ to-witness w)
    unpack-isInj₁ _ _ refl (Any.just _) = refl

    unpack-isInj₂ : {A B : Set} (x : B) (y : A ⊎ B)
          → (y ≡ inj₂ x)
          → (w : Is-just (isInj₂ y)) 
          → (x ≡ to-witness w)
    unpack-isInj₂ _ _ refl (Any.just _) = refl

    -- d-case-simp : Is-just (DSemᵀ {Etup Pr Γ} {ρ} (f ∘ g) a)
    -- d-case-simp = DSemᵀ-exists-extensionality (interp (case' e l r) ∘ Etup-to-val) (f ∘ g) case-simp-ext a d-case 

-- Question: How to handle ∃DSyn→∃DSem ?
-- Question: How to name this? 
DSyn→DSem : {Γ : Env Pr} {τ : Typ Pr}  ( a : Rep (Etup Pr Γ) ) → ( t : Term Pr Γ τ ) → DSyn-ExistsP (Etup-to-val a) t → (Is-just (DSemᵀ {Etup Pr Γ} {τ} (interp t ∘ Etup-to-val) a))
DSyn→DSem {Γ} {τ} a ( unit ) w = DSemᵀ-exists-unit a
DSyn→DSem {Γ} {τ} a ( var idx ) w = DSemᵀ-var a idx (zerovDense (D2τ' τ)) .fst
DSyn→DSem {Γ} {τ} a ( pair l r ) w = Pair.DSemᵀ-exists-lemma-pair₂ (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) a (DSyn→DSem a l (w .fst) , DSyn→DSem a r (w .snd))
DSyn→DSem {Γ} {τ} a ( fst' t ) w = DSemᵀ-exists-lemma-chain fst (interp t ∘ Etup-to-val) a (DSemᵀ-fst (interp t $ Etup-to-val a) (zerovDense (D2τ' τ))  .fst) (DSyn→DSem a t w)
DSyn→DSem {Γ} {τ} a ( snd' t ) w = DSemᵀ-exists-lemma-chain snd (interp t ∘ Etup-to-val) a (DSemᵀ-snd (interp t $ Etup-to-val a) (zerovDense (D2τ' τ))  .fst) (DSyn→DSem a t w)
DSyn→DSem {Γ} {τ} a ( let' {σ = σ} rhs body ) w =
  let ih-rhs = Pair.DSemᵀ-exists-lemma-pair₂ (interp rhs ∘ Etup-to-val) id a (DSyn→DSem a rhs (fst w) , DSemᵀ-identity a (zerovDense (D2τ' (Etup Pr Γ))) .fst) 
      ih-body = DSyn→DSem (interp rhs (Etup-to-val a) , a) body (snd w)
  in DSemᵀ-exists-lemma-chain {Etup Pr Γ} {σ :* Etup Pr Γ} {τ} (interp body ∘ Etup-to-val) (λ z → interp rhs (Etup-to-val z) , z) a ih-body ih-rhs
DSyn→DSem {Γ} {τ} a ( prim {σ = σ} op t ) w = DSemᵀ-exists-lemma-chain {τ2 = σ} (evalprim op) (interp t ∘ Etup-to-val) a (w .fst) (DSyn→DSem a t (w .snd))
DSyn→DSem {Γ} {τ} a ( inl t ) w = DSemᵀ-exists-lemma-chain inj₁ (interp t ∘ Etup-to-val) a (DSemᵀ-inj₁ (interp t $ Etup-to-val a) (zerovDense (D2τ' _ :*! D2τ' _)) .fst) (DSyn→DSem a t w) 
DSyn→DSem {Γ} {τ} a ( inr t ) w = DSemᵀ-exists-lemma-chain inj₂ (interp t ∘ Etup-to-val) a (DSemᵀ-inj₂ (interp t $ Etup-to-val a) (zerovDense (D2τ' _ :*! D2τ' _)) .fst) (DSyn→DSem a t w) 
DSyn→DSem {Γ} {τ} a ( case' e l r ) w
  using f ← case-helper.f a e l r
  using g ← case-helper.g a e l r
  using ext ← case-helper.case-simp-ext a e l r
  using de ← DSyn→DSem a e (fst w)
  using dg ← Pair.DSemᵀ-exists-lemma-pair₂ (interp e ∘ Etup-to-val) id a (de , DSemᵀ-exists-lemma-identity a)
  with interp e (Etup-to-val a) in eq1
DSyn→DSem {Γ} a (case' {σ = σ} {τ = τ} e l r) (we , wl) | inj₁ x
  = DSemᵀ-exists-extensionality (f ∘ g) _ ext a df∘g
  where v : Is-just (isInj₁ (interp e (Etup-to-val a)))
        v rewrite eq1 = Any.just tt
        wl' : DSyn-ExistsP (push (to-witness v) (Etup-to-val a)) l
        wl' rewrite sym (unpack-isInj₁ x (interp e (Etup-to-val a)) eq1 v) = wl
        dl : Is-just $ DSemᵀ (interp l ∘ Etup-to-val) (to-witness v , a)
        dl = DSyn→DSem (to-witness v , a) l wl'
        df = DSemᵀ-exists-case-inj₁ (g a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) v dl 
        df∘g = DSemᵀ-exists-lemma-chain {τ2 = (σ :+ τ) :* Etup Pr Γ} f g a df dg
DSyn→DSem {Γ} a (case' {σ = σ} {τ = τ} e l r) (we , wr) | inj₂ x
  = DSemᵀ-exists-extensionality (f ∘ g) _ ext a df∘g
  where v : Is-just (isInj₂ (interp e (Etup-to-val a)))
        v rewrite eq1 = Any.just tt
        wr' : DSyn-ExistsP (push (to-witness v) (Etup-to-val a)) r
        wr' rewrite sym (unpack-isInj₂ x (interp e (Etup-to-val a)) eq1 v) = wr
        dr : Is-just $ DSemᵀ (interp r ∘ Etup-to-val) (to-witness v , a)
        dr = DSyn→DSem (to-witness v , a) r wr'
        df = DSemᵀ-exists-case-inj₂ (g a) (interp l ∘ Etup-to-val) (interp r ∘ Etup-to-val) v dr 
        df∘g = DSemᵀ-exists-lemma-chain {τ2 = (σ :+ τ) :* Etup Pr Γ} f g a df dg

DSyn-Exists→DSem-Exists : {Γ : Env Pr} {τ : Typ Pr}  ( a : Rep (Etup Pr Γ) ) → ( t : Term Pr Γ τ ) → DSyn-Exists (Etup-to-val a) t → (Is-just (DSemᵀ {Etup Pr Γ} {τ} (interp t ∘ Etup-to-val) a))
DSyn-Exists→DSem-Exists a t (∃dsyn x) = DSyn→DSem a t x

-- TODO: Delete this old stuff

-- _>>_ : {A B : Set} → Maybe A → Maybe B → Maybe B
-- _>>_ x y = x >>= λ _ → y

-- DSyn-ExistsP-Prim' : {σ τ : Typ Pr} → Primop Pr σ τ → Rep σ → Maybe ⊤
-- DSyn-ExistsP-Prim' SIGN x =
--   case primFloatLess x 0.0 of
--     λ where true → just tt -- x < 0 , thus the derivative exists
--             false → case primFloatLess 0.0 x of
--                       λ where true → just tt -- x > 0 , thus the derivative exists
--                               false → nothing -- x is zero or NaN, thsu the derivative does not exists.
-- DSyn-ExistsP-Prim' op x = just tt

-- -- Evaluator die bepaalt of het differentieerbaar is
-- DSyn-ExistsP' : {Γ : Env Pr} {τ : Typ Pr} → Val Pr Γ → Term Pr Γ τ → Maybe (Rep τ)
-- DSyn-ExistsP' {Γ} {τ} val term
--   using v ← interp term val
--   with term
-- ... | unit = just v
-- ... | var idx = just v
-- ... | pair l r = do DSyn-ExistsP' val l
--                     DSyn-ExistsP' val r
--                     just v
-- ... | fst' t = do DSyn-ExistsP' val t
--                   just v
-- ... | snd' t = do DSyn-ExistsP' val t
--                   just v
-- ... | let' rhs body = do v' ← DSyn-ExistsP' val rhs
--                          DSyn-ExistsP' (push v' val) body
--                          just v
-- ... | prim op t = do v' ← DSyn-ExistsP' val t
--                      DSyn-ExistsP-Prim' op v'
--                      just v
-- ... | inl t = DSyn-ExistsP' val t >> just v
-- ... | inr t = DSyn-ExistsP' val t >> just v
-- ... | case' e l r = case interp e val of
--                       [ (λ v' → DSyn-ExistsP' (push v' val) l >> just v) 
--                       , (λ v' → DSyn-ExistsP' (push v' val) r >> just v) ]
