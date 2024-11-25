open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘_; _$_; case_of_; flip)
open import Data.Fin as Fin
open import Data.Empty
open import Data.Integer using (ℤ)
open import Data.Product using (_×_)
open import Level using (Level)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import spec hiding (eval)
import spec as S
import spec.LACM as LACM
open LACM using (LACM)

interp : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> Val tag Γ -> Term tag Γ τ -> Rep τ
interp env e = fst (S.eval env e)

LACMrun : ∀ {Γ : LEnv} {a : Set} -> LACM Γ a -> LEtup Γ -> LEtup Γ
LACMrun {Γ} f e = let _ , e' , _ = LACM.run f e in e'

LACMrun-pure : ∀ {Γ : LEnv} {a : Set} → (x : a)
               → (env : LEtup Γ)
               → LACMrun {Γ} (LACM.pure x) env ≡ env
LACMrun-pure {Γ = Γ} x env = fst $ LACM.run-pure x env

zero-LEnv : (Γ : Env Pr) -> LEtup (map D2τ' Γ)
zero-LEnv [] = tt
zero-LEnv (x ∷ env) = fst ( zerov $ D2τ' x) , zero-LEnv env

postulate
    DSem : {Γ : Env Pr} {τ : Typ Pr} 
            → (Val Pr Γ →  Rep τ)                          -- f(x)
            → (Val Du (D1Γ Γ) → Rep (D2τ τ) → LEtup (map D2τ' Γ)) -- f'(x)
    
    -- The derivative of any term producing a unit is zero for all input variables
    DSem-unit : {Γ : Env Pr}
            → (f : Val Pr Γ →  Rep (Un {Pr}))
            → (env : Val Du (D1Γ Γ)) → (ctg : Rep (D2τ Un))
            → DSem {Γ} {Un} f env ctg ≡ zero-LEnv Γ


-- current Goal proposal
chad-ctg-snd-equiv-DSem : {Γ : Env Pr} {τ : Typ Pr} 
                → (env : Val Du (D1Γ Γ))       -- the typing environment
                  (ctg : Rep (D2τ τ))            -- ctg, some arbitrary (gradient) input
                  (t : Term Pr Γ τ)            -- f(ctg), the original program
                → LACMrun (fst ((interp env (snd' $ chad t)) ctg)) (zero-LEnv Γ) -- f'(ctg) according to CHAD
                  ≡ ((DSem (flip interp t) env) ctg) -- f'(ctg) according to DSem
chad-ctg-snd-equiv-DSem {Γ = Γ} env ctg unit =
        begin
        LACMrun (fst (interp env (snd' $ chad unit) ctg)) (zero-LEnv Γ)
        ≡⟨ LACMrun-pure _ (zero-LEnv Γ) ⟩
        zero-LEnv Γ
        ≡⟨ (sym $ DSem-unit {Γ} (flip interp unit) env ctg) ⟩
        DSem {Γ} (flip interp unit) env ctg
        ∎
chad-ctg-snd-equiv-DSem env ctg (t) = {!   !}
-- chad-ctg-snd-equiv-DSem {Γ = Γ} {τ = τ} env ⊤ unit =
--         begin
--         (interp env (snd' $ chad unit)) ⊤
--         ≡⟨ refl ⟩
--         interp env (snd' (pair unit (lamwith {Un} {D1Γ Γ} {EVM (Data.List.map D2τ' Γ) Un} [] (pureevm unit)))) ⊤
--         ≡⟨ refl ⟩
--         interp env (lamwith {Un} {D1Γ Γ} {EVM (Data.List.map D2τ' Γ) Un} [] (pureevm unit)) ⊤
--         ≡⟨ refl ⟩
--         (interp env (lam {D1Γ Γ} {EVM (Data.List.map D2τ' Γ) Un} {Un} [] (λ ()) (pureevm unit))) ⊤
--         ≡⟨ refl ⟩
--         -- Somehow, this doesn't type.
--         -- But it the literal definition of (eval env (lam ...)) !!!
--         -- How could I get this to typecheck / work? 
--         -- {! (\v -> (eval (push v (buildValFromInj (λ ()) env)) (pureevm unit))) ⊤ !}
--         -- ≡⟨ {!   !} ⟩
--         {!  (interp (push ⊤ (buildValFromInj (λ ()) env)) (pureevm unit))  !}
--         ≡⟨ {!   !} ⟩
--         {! LACM.pure (interp (push ⊤ env) unit)  !}
--         ≡⟨ {!   !} ⟩
--         {! LACM.pure tt  !}
--         ≡⟨ {!   !} ⟩
--         DSem (flip interp unit) env ⊤
--         ∎

-- ==========================================
-- Random functions to understand the problem
-- ==========================================
-- appRep : {Γ : Env Pr} {τ : Typ Pr} 
--             → (f : Rep (D2τ τ :-> D2Γ Γ)) 
--             → (x : Rep (D2τ τ)) 
--             → Rep (D2Γ Γ) × ℤ
-- appRep f x = f x


-- _compose_ : {Γ : Env Du} {a b c : Typ Du}
--         -> Term Du Γ (b :-> c) -> Term Du Γ (a :-> b) -> Term Du Γ (a :-> c)
-- f compose g = {!   !} 

-- runChad : {Γ : Env Pr} {τ : Typ Pr}
--            -> Val Pr Γ -- x
--            -> Term Pr Γ τ -- f(x)
--            -> Rep (D2τ τ :-> D2Γ Γ) -- f'(x)
-- runChad env t = interp (primalVal env) (snd' $ chad t)

-- -- ==========================================
-- -- By now, I see that these are not correct
-- -- ==========================================
-- -- Goal option 
-- -- This doesn't work because we need to apply the a value to the functions to proof that they are equal
-- -- As we cannot directly proof that functions are equal
-- chad-snd-equiv-DSem : {Γ : Env Pr} {τ : Typ Pr} 
--                 → (env : Val Du (D1Γ Γ)) (t : Term Pr Γ τ)
--                 → interp env (snd' $ chad t)
--                   ≡ DSem (flip interp t) env
-- chad-snd-equiv-DSem env unit = 
--                 begin
--                 interp env (snd' $ chad unit)
--                 ≡⟨⟩
--                 interp env (snd' $ pair unit (lamwith [] (pureevm unit)))
--                 ≡⟨ refl ⟩
--                 interp env ((lamwith [] (pureevm unit)))
--                 ≡⟨ refl ⟩
--                 interp env ((lamwith [] (pureevm unit)))
--                 ≡⟨ {!   !} ⟩
--                 DSem (flip interp unit) env
--                 ∎
-- chad-snd-equiv-DSem env t = {!   !}

-- postulate
--     DSem-t : {Γ : Env Pr} {τ : Typ Pr} 
--             → (Val Pr Γ →  Rep τ)
--             → (Val Du (D1Γ Γ) → Rep (D2τ τ) → Rep (D2Γ Γ))
    
--     DSem-t-unit : {Γ : Env Pr}
--                 {x : (Rep (Un {Pr}))}
--                 (f : Val Pr Γ →  Rep (Un {Pr}))
--                 (env : Val Du (D1Γ Γ))
--                 → DSem f env x ≡ {! LACM.pure tt   !}

-- -- Goal option
-- -- This doesn't work because the definition of DSem doesn't include the additional ℤ value
-- chad-snd-equiv-DSem-term : {Γ : Env Pr} {τ : Typ Pr} 
--                 → (env : Val Du (D1Γ Γ)) (x : Term Du (D1Γ Γ) (D2τ τ) ) (t : Term Pr Γ τ)
--                 → ( interp env (app (snd' $ chad t) x ))
--                   ≡ (DSem-t (flip interp t) env ((interp env x)) )
-- chad-snd-equiv-DSem-term env x unit = begin
--                                         interp env (app (snd' $ chad unit) x)
--                                        ≡⟨ refl ⟩
--                                         interp env (app (snd' $ (pair unit (lamwith [] (pureevm unit)))) x)
--                                        ≡⟨ refl ⟩
--                                         interp env (pureevm unit)
--                                        ≡⟨ refl ⟩
--                                         LACM.pure tt
--                                        ≡⟨ {!   !} ⟩
--                                        DSem-t (flip interp unit) env (interp env x)
--                                        ∎
-- chad-snd-equiv-DSem-term env x (fst' t) = {!   !}
-- chad-snd-equiv-DSem-term env x (snd' t) = {!   !}
-- chad-snd-equiv-DSem-term env x (inl t) = {!   !}
-- chad-snd-equiv-DSem-term env x (inr t) = {!   !}
-- chad-snd-equiv-DSem-term env x (pair l r) = {!   !}
-- chad-snd-equiv-DSem-term env x (prim op t) = {!   !}
-- chad-snd-equiv-DSem-term env x (var v) = {!   !}
-- chad-snd-equiv-DSem-term env x (let' e t) = {!   !}
-- chad-snd-equiv-DSem-term env x (case' e l r) = {!   !}
 
 