module correctness.lemmas.interp-sink-commutes where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Data.List using ([]; _∷_)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality using (sym; cong)

open import spec
open import correctness.spec
open import eval-sink-commute

interp-sink-commute : ∀ {tag} {Γ Γ' : Env tag} {τ : Typ tag}
                -> (env : Val tag Γ) (env2 : Val tag Γ')
                -> (w : Weakening Γ Γ')
                -> sinks-to w env env2
                -> (e : Term tag Γ τ)
                -> interp e env ≡ interp (sink w e) env2
interp-sink-commute env env2 w s e = cong fst (eval-sink-commute env env2 w s e)

-- Lemma using interp-sink-commute on a weakening of Copy-Skip-End
-- This ends up being used for the let' and case' constructors.
interp-sink-commute-Copy-Skip-End : ∀ {tag} {Γ : Env tag} {σ τ ρ : Typ tag} {y : Rep ρ}
                            → (x : Rep σ)
                            → (env : Val tag Γ)
                            → (t : Term tag (σ ∷ Γ) τ )
                            → let env' : Val tag (σ ∷ ρ ∷ Γ)
                                  env' = push x (push y env)
                              in interp (sink (WCopy (WSkip WEnd)) t) env'
                                ≡ interp t (push x env)
interp-sink-commute-Copy-Skip-End x env t = sym $
    interp-sink-commute (push x env) (push x (push _ env)) (WCopy (WSkip WEnd)) (refl , forall-fin-trivial (λ _ → refl )) t

interp-sink-commute-Copy-Copy-Cut : ∀ {tag} {Γ : Env tag} {σ1 σ2 τ : Typ tag}
                            → ( x : Rep σ1 )
                            → ( y : Rep σ2 )
                            → (env : Val tag Γ)
                            → ( t : Term tag (σ1 ∷ σ2 ∷ []) τ )
                            → let env1 : Val tag (σ1 ∷ σ2 ∷ Γ) 
                                  env1 = push x (push y env)
                                  env2 : Val tag  (σ1 ∷ σ2 ∷ [])
                                  env2 = push x (push y empty)
                              in interp (sink (WCopy (WCopy WCut)) t) env1
                                  ≡ interp t env2
interp-sink-commute-Copy-Copy-Cut x y env t =
  let env1 = push x (push y env)
      env2 = push x (push y empty)
  in sym (interp-sink-commute env2 env1 (WCopy (WCopy WCut)) (refl , refl , tt) t)