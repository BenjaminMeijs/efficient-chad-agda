module correctness.lemmas.LACMexec-lemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Float using (Float; primFloatPlus; primNatToFloat)

open import Data.Integer using (ℤ)
open import Data.List using (_∷_)
open import Data.Product using (_×_)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)

open import spec
open import correctness.spec
import spec.LACM as LACM
open LACM using (LACM)

-- Todo: Rename to LACMexec-properties

private
    LACMbind : ∀ {Γ : LEnv} {a b : Set} -> LACM Γ a -> (a -> LACM Γ b) -> LACM Γ b
    LACMbind f g = LACM.bind f (λ x → ( g x , ℤ.pos 1 ))

LACMsequence : ∀ {Γ : LEnv} {a b : Set} -> LACM Γ a -> LACM Γ b -> LACM Γ b
LACMsequence f g = LACMbind f ( λ _ → g )

LACMexec-pure : ∀ {Γ : LEnv} {a : Set} → (x : a)
    → (ev : LEtup Γ)
    → LACMexec {Γ} (LACM.pure x) ev ≡ ev
LACMexec-pure {Γ = Γ} x ev = fst $ LACM.run-pure x ev

LACMexec-bind : ∀ {Γ : LEnv} {a b : Set} 
    → (m1 : LACM Γ a) 
    → (m2 : a -> LACM Γ b)
    → (evIn : LEtup Γ)
    → let evOut1         = LACMexec (LACMbind m1 m2) evIn
          r1 , evAux , _ = LACM.run m1 evIn
          evOut2         = LACMexec (m2 r1) evAux
    in (evOut1 ≡ evOut2) 
LACMexec-bind {Γ} m1 m2 ev = fst $ LACM.run-bind m1 (λ x → (m2 x , ℤ.pos 1)) ev

LACMexec-scope : ∀ {Γ : LEnv} {a : Set}  {τ : LTyp}
    → (m : LACM (τ ∷ Γ) a) -> (inval : LinRep τ)
    → (ev : LEtup Γ)
    → let (outval1 , x1) , ev1 , _ = LACM.run (LACM.scope inval m) ev
          x2 , (outval2 , ev2) , _ = LACM.run m (inval , ev)
    in (x1 ≡ x2) × (ev1 ≡ ev2) × (outval1 ≡ outval2)
LACMexec-scope {Γ} m val ev = let a , b , c , _ = LACM.run-scope m val ev
                                in a , c , b 

LACMexec-add : ∀ {Γ : LEnv} {τ : LTyp}
    → (idx : Idx Γ τ) → (val : LinRep τ)
    → (env : LEtup Γ)
    → let env' = LACMexec (LACM.add idx val) env
    in  env' ≡ addLEτ idx val env
LACMexec-add idx val env = LACM.run-add idx val env .fst 

LACMexec-sequence : ∀ {Γ : LEnv} {a b : Set} 
    → (m1 : LACM Γ a) 
    → (m2 : LACM Γ b)
    → (evIn : LEtup Γ)
    → let evOut1 = LACMexec (LACMsequence m1  m2) evIn
          evAux  = LACMexec m1 evIn
          evOut2 = LACMexec m2 evAux
    in (evOut1 ≡ evOut2) 
LACMexec-sequence m1 m2 ev = LACMexec-bind m1 (λ _ → m2) ev