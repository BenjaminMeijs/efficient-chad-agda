open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘_; _$_; case_of_)
open import Data.Fin as Fin
open import Data.Empty
open import Level using (Level)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import eval-sink-commute
open import spec hiding (eval)
import spec as S

eval : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> Val tag Γ -> Term tag Γ τ -> Rep τ
eval env e = fst (S.eval env e)

D1Term : {Γ : Env Pr} {τ : Typ Pr}
        -> Term Pr Γ τ -> Term Du (D1Γ Γ) (D1τ τ)
D1Term unit = unit
D1Term (let' term body) = let' (D1Term term) (D1Term body)
D1Term (pair l r) = pair (D1Term l) (D1Term r)
D1Term (fst' prog) = fst' (D1Term prog)
D1Term (snd' prog) = snd' (D1Term prog)
D1Term (inl prog) = inl (D1Term prog)
D1Term (inr prog) = inr (D1Term prog)
D1Term (prim x prog) = prim (d1Prim x) (D1Term prog)
D1Term (case' c l r) = case' (D1Term c) (D1Term l) (D1Term r)
D1Term (var x) = var (convIdx D1τ x)

-- Giga: Guaranteeing Invariance of non-Gradient part of Automatic differentiation
giga-chad : {Γ : Env Pr} {τ : Typ Pr}
                   -> (env : Val Du (D1Γ Γ))
                   -> (prog : Term Pr Γ τ)
                   -> eval env (fst' (chad prog)) ≡ eval env (D1Term prog)
giga-chad env unit = refl
giga-chad env (var x) = refl
giga-chad env (fst' term) rewrite giga-chad env term = refl
giga-chad env (snd' term) rewrite giga-chad env term = refl
giga-chad env (inl term) rewrite giga-chad env term = refl
giga-chad env (inr term) rewrite giga-chad env term = refl
giga-chad env (pair l r)
    rewrite giga-chad env l 
    rewrite giga-chad env r = refl 
giga-chad env (prim op t) = cong (evalprim (d1Prim op) ) (giga-chad env t)
giga-chad env (case' e l r) = {!   !}
giga-chad env (let' {σ = σ} {τ = τ} rhs t)
    rewrite giga-chad env rhs =
      let eval-rhs-giga = eval env (D1Term rhs)
          eval-rhs-chad = eval env (chad rhs)
          eval-t-giga   = eval (push eval-rhs-giga env) (D1Term t)
          eval-t-chad  = eval (push ((eval-rhs-giga)) ((push eval-rhs-chad (env))))
                               (sink (WCopy (WSkip WEnd)) (chad t))
      in {!   !}
        -- begin
        -- eval env (fst' (chad (let' rhs t)))
      -- ≡⟨ {!   !} ⟩ 
        -- eval env (D1Term (let' rhs t))
        -- ∎

push-is-let : {Γ : Env Pr} {τ σ : Typ Pr}
                   -> (env : Val Du (D1Γ Γ))
                   -> (rhs : Term Pr Γ σ)
                --    -> {eRhs : eval env (fst' (chad rhs))}
                   -> (t : Term Pr (σ ∷ Γ) τ)
                   -> eval env (fst' (chad (let' rhs t))) 
                      ≡ eval (push (eval env (fst' (chad rhs))) env) (fst' (chad t))
push-is-let env rhs t = let eRhs  = eval env (fst' (chad rhs)) in
                      begin 
                      fst (eval env ((chad (let' rhs t))))
                      ≡⟨⟩ 
                        (eval env ( 
                        let' (chad rhs) $
                        let' (fst' (var Z)) $
                        let' (sink (WCopy (WSkip WEnd)) (chad t)) $
                        (fst' (var Z))
                        ))
                      ≡⟨ {! eval-sink-commute ? ? ? ? ?  !} ⟩ 
                        (eval env ( 
                        let' (chad rhs) $
                        let' (fst' (var Z)) $
                        let' (sink (WCopy (WSkip WEnd)) (chad t)) $
                        (fst' (var Z))
                        ))
                      ≡⟨ {!   !} ⟩
                      fst (eval (push eRhs env) (chad t))
                      ≡⟨ {!   !} ⟩
                      fst (eval (push eRhs env) (chad t))
                      ∎
                      

foobar : {Γ : Env Pr} {τ σ : Typ Pr}
                   -> (env : Val Du (D1Γ Γ))
                   -> (rhs : Term Pr Γ σ)
                   -> (t : Term Pr (σ ∷ Γ) τ)
                   -> eval env (D1Term (let' rhs t)) ≡ eval env (fst' (chad (let' rhs t )))  
foobar env rhs t = let eRhs  = eval env (D1Term rhs)
                       eT a  = eval (push a env) (D1Term t)
                       eRhs' = eval env (fst' (chad rhs))
                       eT' a = eval (push a env) (fst' (chad t))
                       eRhs≡eRhs' = giga-chad env rhs
                       eT≡eT' = giga-chad (push eRhs' env) t
                   in begin 
                        eT eRhs
                        ≡⟨ sym (cong eT eRhs≡eRhs') ⟩ 
                        eT eRhs'
                        ≡⟨ sym eT≡eT' ⟩ 
                        eT' eRhs'
                        ≡⟨⟩ 
                        eval (push eRhs' env) (fst' (chad t))
                        ≡⟨ sym (push-is-let env rhs t) ⟩ 
                        eval env (fst' (chad (let' rhs t))) 
                      ∎