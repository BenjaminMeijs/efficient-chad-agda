module correctness.lemmas.simplify-exec-chad where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Maybe using (just; nothing)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import correctness.lemmas.LACMexec-properties
open import correctness.lemmas.interp-sink-commutes

open import spec
open import correctness.spec
import spec.LACM as LACM
open import chad-preserves-primal

interp-zerot-equiv-zerov : {Γ : Env Du} { env : Val Du Γ }
                          → (τ : Typ Pr)
                          → interp (zerot τ) env ≡ zerov (D2τ' τ) .fst
interp-zerot-equiv-zerov Un = refl
interp-zerot-equiv-zerov Inte = refl
interp-zerot-equiv-zerov R = refl
interp-zerot-equiv-zerov (σ :* τ) = refl
interp-zerot-equiv-zerov (σ :+ τ) = refl 

simplify-exec-chad-fst : {Γ : Env Pr} {σ τ : Typ Pr} 
    → (val : Val Pr Γ)
      (evIn : LEtup (map D2τ' Γ) )
      (ctg : LinRep (D2τ' σ))
      (t : Term Pr Γ (σ :* τ))
    → LACMexec (interp (chad (fst' t)) (primalVal val) .snd ctg .fst ) evIn
      ≡ LACMexec (interp (chad t) (primalVal val) .snd (just (ctg , zerov (D2τ' τ) .fst)) .fst) evIn
simplify-exec-chad-fst {Γ} {σ} {τ} val evIn ctg t 
  using ρ ← D1τ (σ :* τ) :* (D2τ (σ :* τ) :-> D2Γ Γ)
  using val2 ← (push {Du} {ρ ∷ []} {Lin (D2τ' σ)} ctg (push {Du} {[]} {ρ} (interp (chad t) (primalVal val))  empty))
  rewrite interp-zerot-equiv-zerov {Lin (D2τ' σ) ∷ ρ ∷ []} {val2} τ
  = refl

simplify-exec-chad-snd : {Γ : Env Pr} {σ τ : Typ Pr} 
    → (val : Val Pr Γ)
      (evIn : LEtup (map D2τ' Γ) )
      (ctg : LinRep (D2τ' τ))
      (t : Term Pr Γ (σ :* τ))
    → LACMexec (interp (chad (snd' t)) (primalVal val) .snd ctg .fst ) evIn
      ≡ LACMexec (interp (chad t) (primalVal val) .snd (just (zerov (D2τ' σ) .fst , ctg)) .fst) evIn
simplify-exec-chad-snd {Γ} {σ} {τ} val evIn ctg t 
  using ρ ← D1τ (σ :* τ) :* (D2τ (σ :* τ) :-> D2Γ Γ)
  using val2 ← (push {Du} {ρ ∷ []} {Lin (D2τ' τ)} ctg (push {Du} {[]} {ρ} (interp (chad t) (primalVal val))  empty))
  rewrite interp-zerot-equiv-zerov {Lin (D2τ' τ) ∷ ρ ∷ []} {val2} σ
  = refl

-- This lemma is used to simplify LACMexec of a let'
-- it is polymorphic in the valuation v for example:
-- -> A is Val Pr Γ, toVal is id
-- -> A is Etup Pr Γ, toVal is Etup-to-val
simplify-exec-chad-let : {A : Set} {Γ : Env Pr} {τ σ : Typ Pr} 
    → (v : A) (toVal : A → Val Pr Γ)
    → (evIn : LEtup (map D2τ' Γ) )
      (ctg : LinRep (D2τ' τ))
    → (rhs : Term Pr Γ σ)
      (body : Term Pr (σ ∷ Γ) τ)
    → let val' = primalVal (push (interp rhs (toVal v)) (toVal v))
          body' = interp (chad body) val' .snd ctg .fst
          ev-body = LACMexec body' (zerov (D2τ' σ) .fst , evIn)
      in LACMexec (interp (chad (let' rhs body)) (primalVal (toVal v)) .snd ctg .fst ) evIn
          ≡ LACMexec (interp (chad rhs) (primalVal (toVal v)) .snd (ev-body .fst) .fst) (ev-body .snd)
simplify-exec-chad-let {_} {Γ} {τ} {σ} v toVal evIn ctg rhs body
  using val ← toVal v
  using ρ1 ← D1τ σ :* (D2τ σ :-> D2Γ Γ)
  using ρ2 ← D1τ τ :* (D2τ τ :-> D2Γ (σ ∷ Γ))
  using ρ3 ← Lin (D2τ' τ)
  rewrite chad-preserves-primal val rhs
  rewrite interp-sink-commute-Copy-Skip-End {ρ = ρ1} {y = interp (chad rhs) (primalVal val)} (primal σ (interp rhs val)) (primalVal val) (chad body)
  using val-verbose ← 
    (push {Du} {ρ2 ∷ ρ1 ∷ []} {ρ3} ctg
    (push {Du} {ρ1 ∷ []} {ρ2} (interp (chad body) (push (primal σ (interp rhs val)) (primalVal val)))
    (push {Du} {[]} {ρ1} (interp (chad rhs) (primalVal val)) empty)))
  rewrite interp-zerot-equiv-zerov {ρ3 ∷ ρ2 ∷ ρ1 ∷ []} {val-verbose} σ
  using m1 ← λ x → ( snd (interp (chad rhs) (primalVal val)) (fst x) .fst , ℤ.pos 5 Data.Integer.+ snd (interp (chad rhs) (primalVal val)) (fst x) .snd )
  using m2 ← (interp (chad body) (push (primal σ (interp rhs val)) (primalVal val)) .snd ctg .fst)
  using elim-bind ← LACM.run-bind (LACM.scope (zerov (D2τ' σ) .fst) m2) m1 evIn .fst
  rewrite elim-bind
  using (_ , elim-scope-snd , elim-scope-fst) ← LACMexec-scope m2 ((zerov (D2τ' σ) .fst)) evIn
  rewrite elim-scope-fst
  rewrite elim-scope-snd
  = refl

simplify-exec-chad-primop : {Γ : Env Pr} {σ τ : Typ Pr} 
  → (val : Val Pr Γ)
    (evIn : LEtup (map D2τ' Γ) )
    (ctg : LinRep (D2τ' τ))
    (t : Term Pr Γ σ)
    (op : Primop Pr σ τ )
  → let ctg-op = (interp (dprim' op) (push ctg (push (primal σ (interp t val)) empty)))
    in LACMexec (interp (chad (prim op t)) (primalVal val) .snd ctg .fst ) evIn
        ≡ LACMexec (interp (chad t) (primalVal val) .snd ctg-op .fst) evIn
simplify-exec-chad-primop {Γ} {σ} {τ} val evIn ctg t op 
  using val-ignore ← push {Du} {(D1τ σ :* (D2τ σ :-> D2Γ Γ)) ∷ []} {Lin (D2τ' τ)} ctg (push {Du} {[]} {D1τ σ :* (D2τ σ :-> D2Γ Γ)} (interp (chad t) (primalVal val)) empty)
  rewrite chad-preserves-primal val t
  rewrite interp-sink-commute-Copy-Copy-Cut ctg (primal σ (interp t val)) val-ignore (dprim' op)
  = refl

-- This lemma is used to simplify LACMexec of a case' after having done:
-- 1. a rewrite using: rewrite chad-preserves-primal val e
-- 2. a with and case distinction on: interp e val
-- Then, you can use this lemma, for example with a rewrite.
-- The argument f should be either inj₁ or inj₂, depending on the case distinction
-- TODO: Extra comment over lelijke type
simplify-exec-chad-case : {Γ : Env Pr} {σ τ ρ π : Typ Pr} 
  → (val : Val Pr Γ)
    (evIn : LEtup (map D2τ' Γ) )
    (ctg : LinRep (D2τ' ρ))
    (e : Term Pr Γ (σ :+ τ))
    (t : Term Pr (π ∷ Γ) ρ)
    (x : Rep π)
    (f : LinRep (D2τ' π) → LinRep (D2τ' σ) ⊎ LinRep (D2τ' τ)  )
  → let τ1 = D1τ (σ :+ τ) :* (D2τ (σ :+ τ) :-> D2Γ Γ)
        τ2 = D1τ ρ :* (D2τ ρ :-> D2Γ (π ∷ Γ))
        zerot-π = (interp
                    (zerot π)
                      (push {Du} {τ2 ∷ τ1 ∷ []} {Lin (D2τ' ρ)}
                        ctg
                        (push {Du} {τ1 ∷ []} {τ2}
                          (interp 
                            (sink (WCopy (WSkip WEnd)) (chad t))
                            (push {Du} {τ1 ∷ map D1τ Γ} {D1τ π} (primal π x) (push {Du} {map D1τ Γ} {τ1} (interp {τ = τ1} (chad e) (primalVal val)) (primalVal val)))
                          )
                          (push {Du} {[]} {τ1} (interp (chad e) (primalVal val)) empty)
                        )
                      )
                  )
        m2 = ( (interp
                  (sink (WCopy (WSkip WEnd)) (chad t))
                  (push {Du} {τ1 ∷ map D1τ Γ} {D1τ π} (primal π x) (push {Du} {map D1τ Γ} {τ1} (interp (chad e) (primalVal val)) (primalVal val)))
                ) .snd ctg .fst
              )
        m3 = (λ y → ( interp (chad e) (primalVal val) .snd (just (f (fst y))) .fst )
                      , (ℤ.pos 6 Data.Integer.+ (interp (chad e) (primalVal val)) .snd (just (f (fst y))) .snd)
              )
        t' = LACMexec (interp (chad t) (push (primal π x) (primalVal val)) .snd ctg .fst) (zerov (D2τ' π) .fst , evIn)
    in LACMexec (LACM.bind (LACM.scope zerot-π m2) m3) evIn
        ≡ LACMexec (interp (chad e) (primalVal val) .snd (just (f (t' .fst))) .fst) (t' .snd)
simplify-exec-chad-case {Γ} {σ} {τ} {ρ} {π} val evIn ctg e t x f
  rewrite interp-sink-commute-Copy-Skip-End {ρ = D1τ (σ :+ τ) :* (D2τ (σ :+ τ) :-> D2Γ Γ)} {y = (interp (chad e) (primalVal val))} (primal π x) (primalVal val) (chad t)
  using τ1 ← D1τ (σ :+ τ) :* (D2τ (σ :+ τ) :-> D2Γ Γ)
  using τ2 ← D1τ ρ :* (D2τ ρ :-> D2Γ (π ∷ Γ))
  using val2 ← push {Du} {τ2 ∷ τ1 ∷ []} {Lin (D2τ' ρ)} ctg (push {Du} {τ1 ∷ []} {τ2} (interp  (chad t) (push (primal π x) (primalVal val)) ) (push {Du} {[]} {τ1} (interp (chad e) (primalVal val) ) empty) )
  rewrite interp-zerot-equiv-zerov {Lin (D2τ' ρ) ∷ τ2 ∷ τ1 ∷ []} {val2} π
  using m1 ← λ y → ( interp (chad e) (primalVal val) .snd (just (f (y .fst))) .fst , ℤ.pos 6 Data.Integer.+ interp (chad e) (primalVal val) .snd (just (f (y .fst))) .snd )
  using m2 ← interp (chad t) (push (primal π x) (primalVal val)) .snd ctg .fst
  using elim-bind ← LACM.run-bind (LACM.scope (zerov (D2τ' π) .fst) m2) m1 evIn .fst
  rewrite elim-bind
  using (_ , elim-scope-snd , elim-scope-fst) ← LACMexec-scope m2 ((zerov (D2τ' π) .fst)) evIn
  rewrite elim-scope-fst
  rewrite elim-scope-snd
  = refl