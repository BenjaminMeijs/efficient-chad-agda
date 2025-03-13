module correctness.chad-numerical-precision where

open import Data.Nat
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.List using (_∷_; map; [])
open import Data.Product using (_×_)

open import spec
import spec.LACM as LACM
open import correctness.spec

relu : Term Pr (R ∷ []) R
relu = case' (prim SIGN (var Z)) 
        (case' (var Z) (prim (LIT 0.0) unit) -- negative, y = 0
                       (var (S (S Z)))) -- positive , y = x
        (prim (LIT 0.0) unit) -- Zero or NaN , y = 0

relu' : Term Du (D1Γ (R ∷ [])) (D2Γ (R ∷ []))
relu' = app (snd' (chad relu)) {! prim (LIT 1.0) unit  !}

ill-conditioned-example : Term Pr (R ∷ []) R
ill-conditioned-example = {! case'  !}

-- Epsilon : ∀ {tag} ( τ : Typ tag ) → Set
-- Epsilon Un = ⊤
-- Epsilon Inte = ⊤
-- Epsilon R = ℕ
-- Epsilon (σ :* τ) = Epsilon σ × Epsilon τ
-- Epsilon (σ :+ τ) = Epsilon σ × Epsilon τ
-- Epsilon (σ :-> τ) = Epsilon σ → Epsilon τ
-- Epsilon (EVM x τ) = Epsilon τ → {!    !}
-- Epsilon (Lin LUn) = ⊤
-- Epsilon (Lin LR) = ℕ
-- Epsilon (Lin (σ :*! τ)) = Epsilon (Lin σ) × Epsilon (Lin τ)
-- Epsilon (Lin (σ :+! τ)) = Epsilon (Lin σ) × Epsilon (Lin τ)

-- ε-zero : ( τ : Typ Pr ) → Epsilon τ
-- ε-zero Un = tt
-- ε-zero Inte = 0
-- ε-zero R = 0
-- ε-zero (σ :* τ) = (ε-zero σ) , (ε-zero τ)
-- ε-zero (σ :+ τ) = (ε-zero σ) , (ε-zero τ) 

-- ε-plus : {τ : Typ Pr} → Epsilon τ → Epsilon τ → Epsilon τ
-- ε-plus {Un} x y = tt
-- ε-plus {Inte} x y = x + y
-- ε-plus {R} x y = x + y
-- ε-plus {σ :* τ} (x1 , x2) (y1 , y2) = ε-plus x1 y1 , ε-plus x2 y2
-- ε-plus {σ :+ τ} (x1 , x2) (y1 , y2) = ε-plus x1 y1 , ε-plus x2 y2

-- ε-max : {τ : Typ Pr} → Epsilon τ → Epsilon τ → Epsilon τ
-- ε-max {Un} x y = tt
-- ε-max {Inte} x y = x ⊔′ y
-- ε-max {R} x y = x ⊔′ y
-- ε-max {σ :* τ} (x1 , x2) (y1 , y2) = ε-max x1 y1 , ε-max x2 y2
-- ε-max {σ :+ τ} (x1 , x2) (y1 , y2) = ε-max x1 y1 , ε-max x2 y2

-- primop-max-ε-factor : {σ τ : Typ Pr} 
--                     → (op : Primop Pr σ τ)
--                     → Epsilon σ
--                     → Epsilon τ
-- primop-max-ε-factor {Un} {R}        (LIT x) tt = 0
-- primop-max-ε-factor {Inte} {Inte}   INEG ε = ε
-- primop-max-ε-factor {R} {R}         NEG ε = ε
-- primop-max-ε-factor {R} {σ :+ τ}    SIGN ε = (tt , tt) , tt
-- primop-max-ε-factor {σ :* τ} {Inte} IADD (ε1 , ε2) = 1 + ε1 ⊔′ ε2
-- primop-max-ε-factor {σ :* τ} {Inte} IMUL (ε1 , ε2) = 1 + ε1 ⊔′ ε2
-- primop-max-ε-factor {σ :* τ} {R}    ADD (ε1 , ε2) = 1 + ε1 ⊔′ ε2
-- primop-max-ε-factor {σ :* τ} {R}    MUL (ε1 , ε2) = 1 + ε1 ⊔′ ε2

-- term-max-ε-factor : {Γ : Env Pr} {τ : Typ Pr} 
--                     → (t : Term Pr Γ τ)
--                     → Epsilon τ
-- term-max-ε-factor {Γ} {τ} unit = tt
-- term-max-ε-factor {Γ} {τ} (var idx) = ε-zero τ
-- term-max-ε-factor {Γ} {τ} (pair l r) = term-max-ε-factor l , term-max-ε-factor r 
-- term-max-ε-factor {Γ} {τ} (fst' t) = term-max-ε-factor t .fst
-- term-max-ε-factor {Γ} {τ} (snd' t) = term-max-ε-factor t .snd
-- term-max-ε-factor {Γ} {τ} (let' rhs body) = {! app (snd' (chad body)) ?  !}
-- term-max-ε-factor {Γ} {τ} (prim op t) = primop-max-ε-factor op (term-max-ε-factor t)
-- term-max-ε-factor {Γ} {τ} (inl t) = {!   !} -- term-max-ε-factor t , ε-zero _
-- term-max-ε-factor {Γ} {τ} (inr t) = {!   !} -- ε-zero _ , term-max-ε-factor t
-- term-max-ε-factor {Γ} {τ} (case' e l r) = {!   !} -- ε-max (term-max-ε-factor l) (term-max-ε-factor r)


-- -- chad-equiv-DSemᵀ : {Γ : Env Pr} {τ : Typ Pr} 
-- --                   → let σ  = Etup Pr Γ 
-- --                         LΓ = map D2τ' Γ in
-- --                   (a : Rep σ)
-- --                   (evIn : LEtup LΓ )
-- --                   (ctg : LinRep (D2τ' τ))
-- --                   (t : Term Pr Γ τ)
-- --                 → ctg  ≃τ (interp t (Etup-to-val a))
-- --                 → evIn ≃Γ Etup-to-val a  
-- --                 → (∃-dsyn : DSyn-Exists (Etup-to-val a) t)
-- --                 → let dsem = DSyn-Exists→DSem-Exists a t ∃-dsyn
-- --                 in (LEtup2EV {LΓ} (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst ) evIn)
-- --                   ≡ Etup2EV {Γ} ( to-witness dsem (sparse2dense ctg)) ev+ LEtup2EV {LΓ} evIn)

