module giga-chad where
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

interp : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> Val tag Γ -> Term tag Γ τ -> Rep τ
interp env e = fst (S.eval env e)

interp-sink-commute : ∀ {tag} {Γ Γ' : Env tag} {τ : Typ tag}
                 -> (env : Val tag Γ) (env2 : Val tag Γ')
                 -> (w : Weakening Γ Γ')
                 -> sinks-to w env env2
                 -> (e : Term tag Γ τ)
                 -> interp env e ≡ interp env2 (sink w e)
interp-sink-commute env env2 w s e = cong fst (eval-sink-commute env env2 w s e)

-- Lemma using interp-sink-commute on a weakening of Copy-Skip-End
-- This ends up being used for the let' and case' constructors.
interp-sink-commute-Copy-Skip-End : ∀ {tag} {Γ : Env tag} {σ τ ρ : Typ tag} {y : Rep ρ}
                            → (x : Rep σ)
                            → (env : Val tag Γ)
                            → (e : Term tag (σ ∷ Γ) τ )
                            → let env1 : Val tag (σ ∷ Γ)
                                  env1 = push x env
                                  env2 : Val tag (σ ∷ ρ ∷ Γ)
                                  env2 = push x (push y env)
                              in interp env2 (sink (WCopy (WSkip WEnd)) e)
                                 ≡ interp (push x env) e
interp-sink-commute-Copy-Skip-End x env e = sym $
    interp-sink-commute (push x env) (push x (push _ env)) (WCopy (WSkip WEnd)) (refl , forall-fin-trivial (λ _ → refl )) e
   
    -- interp-sink-commute
                --   (push interp-rhs-giga env) (push interp-rhs-giga (push interp-rhs-chad env))
                --   (WCopy (WSkip WEnd)) (refl , forall-fin-trivial (λ _ → refl)) (chad t)

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
                   -> fst (interp env (chad prog)) ≡ interp env (D1Term prog)
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
giga-chad env (let' {σ = σ} {τ = τ} rhs t)
    rewrite giga-chad env rhs =
      let interp-rhs-giga = interp env (D1Term rhs)
      in  begin
          fst (interp (push interp-rhs-giga (push (interp env (chad rhs)) env))
                      (sink (WCopy (WSkip WEnd)) (chad t)))
          ≡⟨ cong fst (interp-sink-commute-Copy-Skip-End interp-rhs-giga env (chad t)) ⟩
          -- interp t using chad
          fst (interp (push interp-rhs-giga env) (chad t))
          ≡⟨ giga-chad (push interp-rhs-giga env) t ⟩ -- induction hypothesis
          -- interp t using original function
          interp (push interp-rhs-giga env) (D1Term t)
          ∎
giga-chad env (case' e l r)
    rewrite giga-chad env e
    with interp env (D1Term e)
... | inj₁ x = begin
               fst (interp (push x (push (interp env (chad e)) env))
                   (sink (WCopy (WSkip WEnd)) (chad l)))
               ≡⟨ cong fst (interp-sink-commute-Copy-Skip-End x env (chad l)) ⟩
               fst (interp (push x env) (chad l))
               ≡⟨ giga-chad (push x env) l  ⟩ -- Indution hypothesis
               interp (push x env) (D1Term l)
               ∎
... | inj₂ y = begin
               fst (interp (push y (push (interp env (chad e)) env))
                   (sink (WCopy (WSkip WEnd)) (chad r)))
               ≡⟨ cong fst (interp-sink-commute-Copy-Skip-End y env (chad r)) ⟩
               fst (interp (push y env) (chad r))
               ≡⟨ giga-chad (push y env) r ⟩
               interp (push y env) (D1Term r)
               ∎
      
 
-- Lemma just applying interp-sink-commute to a weakening of WSkip WEnd
-- Unused in this proof, but still interesting
interp-sink-commute-Skip : ∀ {tag} {Γ : Env tag} {σ τ : Typ tag}
                            → (x : Rep σ)
                            → (env : Val tag Γ)
                            → (e : Term tag Γ τ )
                            → let env' : Val tag (σ ∷ Γ)
                                  env' = push x env
                              in interp env' (sink (WSkip WEnd) e)
                                 ≡ interp env e
interp-sink-commute-Skip x env e = sym $ interp-sink-commute env (push x env) (WSkip WEnd) (forall-fin-trivial (λ _ → refl)) e  
