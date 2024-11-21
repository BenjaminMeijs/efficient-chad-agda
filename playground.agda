open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
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

eval : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> Val tag Γ -> Term tag Γ τ -> Rep τ
eval env e = fst (S.eval env e)

postulate
    DSem : {Γ : Env Pr} {τ : Typ Pr} 
            → (Val Pr Γ →  Rep τ)
            → (Val Du (D1Γ Γ) → Rep (D2τ τ :-> D2Γ Γ))


-- Goal option 2, specifying over the input
chad-x-snd-equiv-DSem : {Γ : Env Pr} {τ : Typ Pr} 
                → (env : Val Du (D1Γ Γ))       -- the typing environment
                  (x : Rep (D2τ τ))            -- x, some arbitrary (gradient) input
                  (t : Term Pr Γ τ)            -- f(x), the original program
                → (eval env (snd' $ chad t)) x -- f'(x) according to CHAD
                  ≡ (DSem (flip eval t) env) x -- f'(x) according to DSem
chad-x-snd-equiv-DSem {Γ = Γ} {τ = τ} env ⊤ unit =
        begin
        (eval env (snd' $ chad unit)) ⊤
        ≡⟨ refl ⟩
        eval env (snd' (pair unit (lamwith {Un} {D1Γ Γ} {EVM (Data.List.map D2τ' Γ) Un} [] (pureevm unit)))) ⊤
        ≡⟨ refl ⟩
        eval env (lamwith {Un} {D1Γ Γ} {EVM (Data.List.map D2τ' Γ) Un} [] (pureevm unit)) ⊤
        ≡⟨ refl ⟩
        (eval env (lam {D1Γ Γ} {EVM (Data.List.map D2τ' Γ) Un} {Un} [] (λ ()) (pureevm unit))) ⊤
        ≡⟨ {!   !} ⟩
        -- Somehow, this doesn't type.
        -- But it the literal definition of (eval env (lam ...)) !!!
        -- How could I get this to typecheck / work? 
        {! (\v -> (eval (push v (buildValFromInj (λ ()) env)) (pureevm unit))) ⊤ !}
        ≡⟨ {!   !} ⟩
        {! (eval (push ⊤ env) (pureevm unit))  !}
        ≡⟨ {!   !} ⟩
        {! LACM.pure (eval (push ⊤ env) unit)  !}
        ≡⟨ {!   !} ⟩
        {! LACM.pure tt  !}
        ≡⟨ {!   !} ⟩
        DSem (flip eval unit) env ⊤
        ∎

chad-x-snd-equiv-DSem env x (t) = {!   !}

-- ==========================================
-- Random functions to understand the problem
-- ==========================================
appRep : {Γ : Env Pr} {τ : Typ Pr} 
            → (f : Rep (D2τ τ :-> D2Γ Γ)) 
            → (x : Rep (D2τ τ)) 
            → Rep (D2Γ Γ) × ℤ
appRep f x = f x


_compose_ : {Γ : Env Du} {a b c : Typ Du}
        -> Term Du Γ (b :-> c) -> Term Du Γ (a :-> b) -> Term Du Γ (a :-> c)
f compose g = {!   !} 

runChad : {Γ : Env Pr} {τ : Typ Pr}
           -> Val Pr Γ -- x
           -> Term Pr Γ τ -- f(x)
           -> Rep (D2τ τ :-> D2Γ Γ) -- f'(x)
runChad env t = eval (primalVal env) (snd' $ chad t)

-- ==========================================
-- By now, I see that these are not correct
-- ==========================================
-- Goal option 
-- This doesn't work because we need to apply the a value to the functions to proof that they are equal
-- As we cannot directly proof that functions are equal
chad-snd-equiv-DSem : {Γ : Env Pr} {τ : Typ Pr} 
                → (env : Val Du (D1Γ Γ)) (t : Term Pr Γ τ)
                → eval env (snd' $ chad t)
                  ≡ DSem (flip eval t) env
chad-snd-equiv-DSem env unit = 
                begin
                eval env (snd' $ chad unit)
                ≡⟨⟩
                eval env (snd' $ pair unit (lamwith [] (pureevm unit)))
                ≡⟨ refl ⟩
                eval env ((lamwith [] (pureevm unit)))
                ≡⟨ refl ⟩
                eval env ((lamwith [] (pureevm unit)))
                ≡⟨ {!   !} ⟩
                DSem (flip eval unit) env
                ∎
chad-snd-equiv-DSem env t = {!   !}

postulate
    DSem-t : {Γ : Env Pr} {τ : Typ Pr} 
            → (Val Pr Γ →  Rep τ)
            → (Val Du (D1Γ Γ) → Rep (D2τ τ) → Rep (D2Γ Γ))
    
    DSem-t-unit : {Γ : Env Pr}
                {x : (Rep (Un {Pr}))}
                (f : Val Pr Γ →  Rep (Un {Pr}))
                (env : Val Du (D1Γ Γ))
                → DSem f env x ≡ {! LACM.pure tt   !}

-- Goal option
-- This doesn't work because the definition of DSem doesn't include the additional ℤ value
chad-snd-equiv-DSem-term : {Γ : Env Pr} {τ : Typ Pr} 
                → (env : Val Du (D1Γ Γ)) (x : Term Du (D1Γ Γ) (D2τ τ) ) (t : Term Pr Γ τ)
                → ( eval env (app (snd' $ chad t) x ))
                  ≡ (DSem-t (flip eval t) env ((eval env x)) )
chad-snd-equiv-DSem-term env x unit = begin
                                        eval env (app (snd' $ chad unit) x)
                                       ≡⟨ refl ⟩
                                        eval env (app (snd' $ (pair unit (lamwith [] (pureevm unit)))) x)
                                       ≡⟨ refl ⟩
                                        eval env (pureevm unit)
                                       ≡⟨ refl ⟩
                                        LACM.pure tt
                                       ≡⟨ {!   !} ⟩
                                       DSem-t (flip eval unit) env (eval env x)
                                       ∎
chad-snd-equiv-DSem-term env x (fst' t) = {!   !}
chad-snd-equiv-DSem-term env x (snd' t) = {!   !}
chad-snd-equiv-DSem-term env x (inl t) = {!   !}
chad-snd-equiv-DSem-term env x (inr t) = {!   !}
chad-snd-equiv-DSem-term env x (pair l r) = {!   !}
chad-snd-equiv-DSem-term env x (prim op t) = {!   !}
chad-snd-equiv-DSem-term env x (var v) = {!   !}
chad-snd-equiv-DSem-term env x (let' e t) = {!   !}
chad-snd-equiv-DSem-term env x (case' e l r) = {!   !}

 