
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Agda.Builtin.Maybe using (just; nothing)
open import Data.List using (_∷_; map)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (sym)

open import spec
open import correctness.spec
-- open import correctness.lemmas.value-compatibility-lemmas
-- open import correctness.lemmas.simplify-exec-chad
-- open import correctness.lemmas.LACMexec-properties
-- open import chad-preserves-primal

chad-correct : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep σ) -- input of function
                  (evIn : LEtup LΓ ) -- incoming LEtup
                  (ctg : LinRep (D2τ' τ)) -- incoming cotangent
                  (t : Term Pr Γ τ) -- primal function
                → ctg  ≃τ (interp t (Etup-to-val a)) -- compatible incoming cotangent
                → evIn ≃Γ Etup-to-val a -- compatible incoming LEtup
                → (∃-dsyn : DSyn-Exists (Etup-to-val a) t) -- function is differentiable at input
                → let dsem = DSyn-Exists→DSem-Exists a t ∃-dsyn
                in ?
                -- in (LEtup2EV {LΓ} (LACMexec (interp (chad t) (Etup-to-val-primal a) .snd ctg .fst ) evIn)
                  -- ≡ Etup2EV {Γ} ( to-witness dsem (sparse2dense ctg)) ev+ LEtup2EV {LΓ} evIn)