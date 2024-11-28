open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Maybe
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

-- ==========================================
-- Convenience functions
-- ==========================================
-- QUESTION: are all functions named appropriately?

-- eval from 'Spec', ignoring the complexity cost
interp : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> Val tag Γ -> Term tag Γ τ -> Rep τ
interp env e = fst (S.eval env e)

-- LACM.run, only returning the environment
-- Folowing the naming of the haskell state monad
LACMexec : ∀ {Γ : LEnv} {a : Set} -> LACM Γ a -> LEtup Γ -> LEtup Γ
LACMexec {Γ} f e = let _ , e' , _ = LACM.run f e in e'

-- executing a pure computation doesn't change the environment, exec (pure x) env ≡ env
LACMexec-pure : ∀ {Γ : LEnv} {a : Set} → (x : a)
               → (env : LEtup Γ)
               → LACMexec {Γ} (LACM.pure x) env ≡ env
LACMexec-pure {Γ = Γ} x env = fst $ LACM.run-pure x env

LACMexec-bind : ∀ {Γ : LEnv} {a b : Set} -> (m1 : LACM Γ a) -> (k : a -> LACM Γ b × ℤ)
                -> (env : LEtup Γ)
                -> let _  , env' , _ = LACM.run (LACM.bind m1 k) env
                       r1 , env1 , _ = LACM.run m1 env
                       m2 , _        = k r1
                       _  , env2 , _ = LACM.run m2 env1
                   in (env' ≡ env2) 
LACMexec-bind {Γ} m1 k env = fst $ LACM.run-bind m1 k env

-- Produces "a large tuple of zeros" for all variables in the environment
zero-LEnv : (Γ : Env Pr) -> LEtup (map D2τ' Γ)
zero-LEnv [] = tt
zero-LEnv (x ∷ env) = fst ( zerov $ D2τ' x) , zero-LEnv env

postulate
    DSem : {Γ : Env Pr} {τ : Typ Pr} 
            → (Val Pr Γ →  Rep τ)                          -- f(x)
            → (Val Du (D1Γ Γ) → Rep (D2τ τ) → LEtup (map D2τ' Γ)) -- f'(x)
    
    -- The derivative of any term producing a unit is zero for all input variables
    -- TODO dit kan je generaliseren. Als ctg de zero is voor type tau, dan is DSEM zero-LEnv 
    DSem-unit : {Γ : Env Pr}
            → (f : Val Pr Γ →  Rep (Un {Pr})) 
            → (env : Val Du (D1Γ Γ)) → (ctg : Rep (D2τ Un))
            → DSem {Γ} {Un} f env ctg ≡ zero-LEnv Γ


chad-equiv-DSem : {Γ : Env Pr} {τ : Typ Pr} 
                  (env : Val Du (D1Γ Γ))       -- the typing environment
                  (ctg : Rep (D2τ τ))            -- ctg, some arbitrary (gradient) input
                  (t : Term Pr Γ τ)            -- f(ctg), the original program
                → LACMexec (fst ((interp env (snd' $ chad t)) ctg)) (zero-LEnv Γ) -- f'(ctg) according to CHAD
                  ≡ ((DSem (flip interp t) env) ctg) -- f'(ctg) according to DSem
chad-equiv-DSem {Γ = Γ} env ctg unit =
        begin
        LACMexec (fst (interp env (snd' $ chad unit) ctg)) (zero-LEnv Γ)
        ≡⟨ LACMexec-pure _ (zero-LEnv Γ) ⟩
        zero-LEnv Γ
        ≡⟨ (sym $ DSem-unit {Γ} (flip interp unit) env ctg) ⟩
        DSem {Γ} (flip interp unit) env ctg
        ∎
-- chad-equiv-DSem {Γ = Γ} env nothing (pair l r) = {!   !}
-- chad-equiv-DSem {Γ = Γ} env ctg@(just (ctgL , ctgR)) (pair l r) = {!  !}
chad-equiv-DSem {Γ = Γ} env ctg (pair l r) = 
        let ihl = {! lfst' ctg  !}
        in begin
        LACMexec (fst (interp env (snd' $ chad (pair l r)) ctg)) (zero-LEnv Γ)
        ≡⟨⟩
        LACMexec (fst (interp env (( 
                        let' (pair (chad l) (chad r)) $
                                (lamwith (zero ∷ []) $
                                  thenevm (app (snd' (fst' (var (S Z)))) (lfst' (var Z)))
                                          (app (snd' (snd' (var (S Z)))) (lsnd' (var Z))))
                 )) ctg)) (zero-LEnv Γ)
        ≡⟨ {! zero  !} ⟩
        -- LACMexec (fst (interp env (( 
                        -- let' (pair (chad l) (chad r)) $
                                -- (lamwith (zero ∷ []) $
                                --   thenevm (app (snd' (chad l)) (lfst' (ctg)))
                                        --   (app (snd' (chad r)) (lsnd' (ctg))))
                --  )) ctg)) (zero-LEnv Γ)
        DSem (flip interp (pair l r)) env ctg
        ∎
chad-equiv-DSem {Γ = Γ} env ctg (fst' t) = {!   !}
chad-equiv-DSem {Γ = Γ} env ctg (snd' t) = {!   !}
chad-equiv-DSem {Γ = Γ} env ctg (var x) = {!   !}
chad-equiv-DSem {Γ = Γ} env ctg (let' e t) = {!   !}
chad-equiv-DSem {Γ = Γ} env ctg (prim op t) = {!   !}
chad-equiv-DSem {Γ = Γ} env ctg (inl t) = {!   !}
chad-equiv-DSem {Γ = Γ} env ctg (inr t) = {!   !}
chad-equiv-DSem {Γ = Γ} env ctg (case' c l r) = {!   !}
