module utility0 where
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Maybe
open import Data.Bool
import Data.Maybe as Maybe
open import Agda.Builtin.Float
open import Data.List using (List; []; _∷_; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘_; _$_; case_of_; flip)
open import Data.Fin as Fin
open import Data.Empty
open import Data.Integer using (ℤ)
open import Data.Product using (_×_)
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Nullary.Negation
open import Data.Empty
open import Data.Float.Properties
open import Level using (Level)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import spec hiding (eval)
open import eval-sink-commute
import spec as S
import spec.LACM as LACM
open LACM using (LACM)

-- The module App-Eq has been written by Lawrence Chonavel
-- Lawrence has provided this module to me to make the use of 'cong' easier
module App-Eq where
  infixl 4 _<$>_ _<*>_

  _<$>_ : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  _<$>_ _ refl = refl

  _<*>_ : {A B : Set} {f g : A → B} {x y : A} → f ≡ g → x ≡ y → f x ≡ g y
  _<*>_ refl refl = refl

  _>>=_ : {A B : Set} {x y : A} {f g : A → B} → x ≡ y → (∀ a → f a ≡ g a) → f x ≡ g y
  _>>=_ refl eq = eq _

  pure : {A : Set} → (x : A) →  x ≡ x
  pure x = refl
  -- can use do
  -- idiom brackets as well 

module Basics where
    -- eval from 'Spec', ignoring the complexity cost
    interp : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> Val tag Γ -> Term tag Γ τ -> Rep τ
    interp env e = fst (S.eval env e)

    -- Produces "a large tuple of zeros" for all variables in the environment
    zero-LEnv : (Γ : Env Pr) -> LEtup (map D2τ' Γ)
    zero-LEnv [] = tt
    zero-LEnv (x ∷ env) = fst ( zerov $ D2τ' x) , zero-LEnv env

    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {u x : A} {v y : B} {w z : C}
                    → u ≡ x
                    → v ≡ y
                    → w ≡ z
                    → f u v w ≡ f x y z
    cong₃ f refl refl refl = refl

    sparse-normal-form : {τ : LTyp} → LinRep τ → LinRep τ
    sparse-normal-form {(σ1 :*! σ2) :*! (τ1 :*! τ2)} (just (nothing , nothing)) = nothing
    sparse-normal-form {(σ1 :+! σ2) :*! (τ1 :*! τ2)} (just (nothing , nothing)) = nothing
    sparse-normal-form {(σ1 :*! σ2) :*! (τ1 :+! τ2)} (just (nothing , nothing)) = nothing
    sparse-normal-form {(σ1 :+! σ2) :*! (τ1 :+! τ2)} (just (nothing , nothing)) = nothing
    sparse-normal-form {(σ1 :*! σ2) :+! (τ1 :*! τ2)} (just (inj₁ nothing)) = nothing
    sparse-normal-form {(σ1 :*! σ2) :+! (τ1 :*! τ2)} (just (inj₂ nothing)) = nothing
    sparse-normal-form {(σ1 :+! σ2) :+! (τ1 :*! τ2)} (just (inj₁ nothing)) = nothing
    sparse-normal-form {(σ1 :+! σ2) :+! (τ1 :*! τ2)} (just (inj₂ nothing)) = nothing
    sparse-normal-form {(σ1 :*! σ2) :+! (τ1 :+! τ2)} (just (inj₁ nothing)) = nothing
    sparse-normal-form {(σ1 :*! σ2) :+! (τ1 :+! τ2)} (just (inj₂ nothing)) = nothing
    sparse-normal-form {(σ1 :+! σ2) :+! (τ1 :+! τ2)} (just (inj₁ nothing)) = nothing
    sparse-normal-form {(σ1 :+! σ2) :+! (τ1 :+! τ2)} (just (inj₂ nothing)) = nothing
    sparse-normal-form {(σ1 :+! σ2) :+! (τ1 :+! τ2)} (just (inj₂ x)) = nothing
    sparse-normal-form {τ} x = x
open Basics public

module interp-sink where
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
                                → (t : Term tag (σ ∷ Γ) τ )
                                → let env' : Val tag (σ ∷ ρ ∷ Γ)
                                      env' = push x (push y env)
                                  in interp env' (sink (WCopy (WSkip WEnd)) t)
                                    ≡ interp (push x env) t
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
                                  in interp env1 (sink (WCopy (WCopy WCut)) t)
                                     ≡ interp env2 t
    interp-sink-commute-Copy-Copy-Cut x y env t =
      let env1 = push x (push y env)
          env2 = push x (push y empty)
      in sym (interp-sink-commute env2 env1 (WCopy (WCopy WCut)) (refl , refl , tt) t)

module environment-value-tuple where
    Etup : ( tag : PDTag ) → List (Typ tag) → Typ tag
    Etup _ [] = Un
    Etup tag (τ ∷ Γ) = τ :* Etup tag Γ

    Etup-to-val : ∀ {tag} {Γ : Env tag} → Rep (Etup tag Γ) → Val tag Γ 
    Etup-to-val {_} {[]} _ = empty
    Etup-to-val {_} {τ ∷ Γ} (x , xs) = push x (Etup-to-val xs)

    val-to-Etup : ∀ {tag} {Γ : Env tag} → Val tag Γ → Rep (Etup tag Γ)
    val-to-Etup {_} {[]} _ = tt
    val-to-Etup {_} {τ ∷ Γ} (push x xs) = x , val-to-Etup xs

    D1Etup-to-val : {Γ : Env Pr} → Rep (D1τ (Etup Pr Γ)) → Val Du (D1Γ Γ)
    D1Etup-to-val {[]} x = empty
    D1Etup-to-val {τ ∷ Γ} (x , xs) = push x (D1Etup-to-val xs) 

    Etup-to-val-primal : {Γ : Env Pr} → Rep (Etup Pr Γ) → Val Du (D1Γ Γ) 
    Etup-to-val-primal x = primalVal (Etup-to-val x) 
    
    Etup-to-LEtup : {Γ : Env Pr} → LinRep (D2τ' (Etup Pr Γ)) → LEtup (map D2τ' Γ)
    Etup-to-LEtup {[]} _ = tt
    Etup-to-LEtup {τ ∷ Γ} nothing = zero-LEnv (τ ∷ Γ)
    Etup-to-LEtup {τ ∷ Γ} (just (x , xs)) = x , Etup-to-LEtup xs

    zerov-on-Etup-is-zeroLEnv : {Γ : Env Pr} → Etup-to-LEtup (fst (zerov (D2τ' (Etup Pr Γ)))) ≡ zero-LEnv Γ
    zerov-on-Etup-is-zeroLEnv {[]} = refl
    zerov-on-Etup-is-zeroLEnv {τ ∷ Γ} = refl


    Etup-valprj : ∀ {tag} {Γ : Env tag} {τ : Typ tag} → (a : Rep (Etup tag Γ)) -> Idx Γ τ -> Rep τ
    Etup-valprj (x , xs) Z = x
    Etup-valprj (x , xs) (S i) = Etup-valprj xs i


module LACMconvenience where
    LACMmap : ∀ {Γ : LEnv} {a b : Set} -> (a -> b) -> LACM Γ a -> LACM Γ b
    LACMmap f m = LACM.bind m (λ x → LACM.pure (f x) , ℤ.pos 1)

    -- LACM.run, only returning the environment
    -- Folowing the naming of the haskell state monad (MTL)
    LACMexec : ∀ {Γ : LEnv} {a : Set} -> LACM Γ a -> LEtup Γ -> LEtup Γ
    LACMexec {Γ} f e = let _ , e' , _ = LACM.run f e in e'

    LACMbind : ∀ {Γ : LEnv} {a b : Set} -> LACM Γ a -> (a -> LACM Γ b) -> LACM Γ b
    LACMbind f g = LACM.bind f (λ x → ( g x , ℤ.pos 1 ))

    LACMsequence : ∀ {Γ : LEnv} {a b : Set} -> LACM Γ a -> LACM Γ b -> LACM Γ b
    LACMsequence f g = LACMbind f ( λ _ → g )

    -- executing a pure computation doesn't change the environment, exec (pure x) env ≡ env
    LACMexec-pure : ∀ {Γ : LEnv} {a : Set} → (x : a)
                  → (ev : LEtup Γ) -- ev: Environment Vector
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

    LACMexec-sequence-unchanged : ∀ {Γ : LEnv} {a b : Set} 
                    → (m1 : LACM Γ a) 
                    → (m2 : LACM Γ b)
                    → (evIn : LEtup Γ)
                    → let evOut1 = LACMexec (LACMsequence m1 m2) evIn
                          evAux  = LACMexec m1 evIn
                          evOut2 = LACMexec m2 evIn
                      in ((evAux ≡ evIn) → (evOut1 ≡ evOut2))
    LACMexec-sequence-unchanged m1 m2 ev w = trans (LACMexec-sequence m1 m2 ev) (cong₂ LACMexec refl w)


module DenseLinRepresentation where
    LinRepDense : LTyp -> Set
    LinRepDense LUn = ⊤
    LinRepDense LR = Float
    LinRepDense (σ :*! τ) = LinRepDense σ × LinRepDense τ
    LinRepDense (σ :+! τ) = LinRepDense σ × LinRepDense τ

    LinRepDense≟ : {τ : LTyp} → DecidableEquality (LinRepDense τ)
    LinRepDense≟ {LUn} tt tt = yes refl 
    LinRepDense≟ {LR} x y = x Data.Float.Properties.≟ y
    LinRepDense≟ {σ :*! τ} (a , b) (c , d) with LinRepDense≟ a c | LinRepDense≟ b d
    ... | no ¬w | no ¬v = no λ x → ¬w (cong fst x)
    ... | no ¬w | yes v = no λ x → ¬w (cong fst x)
    ... | yes w | no ¬v = no λ x → ¬v (cong snd x)
    ... | yes w | yes v = yes (cong₂ (_,_) w v)
    LinRepDense≟ {σ :+! τ} (a , b) (c , d) with LinRepDense≟ a c | LinRepDense≟ b d
    ... | no ¬w | no ¬v = no λ x → ¬w (cong fst x)
    ... | no ¬w | yes v = no λ x → ¬w (cong fst x)
    ... | yes w | no ¬v = no λ x → ¬v (cong snd x)
    ... | yes w | yes v = yes (cong₂ (_,_) w v)

    zerovDense : (τ : LTyp) -> LinRepDense τ 
    zerovDense LUn = tt
    zerovDense LR = 0.0
    zerovDense (σ :*! τ) = zerovDense σ , zerovDense τ
    zerovDense (σ :+! τ) = zerovDense σ , zerovDense τ

    sparse2dense : { τ : LTyp } → LinRep τ → LinRepDense τ
    sparse2dense {LUn} tt = tt
    sparse2dense {LR} x = x
    sparse2dense {σ :*! τ} (just (x , y)) = sparse2dense {σ} x , sparse2dense {τ} y 
    sparse2dense {σ :*! τ} nothing = zerovDense (σ :*! τ) 
    sparse2dense {σ :+! τ} (just (inj₁ x)) = sparse2dense {σ} x , zerovDense τ
    sparse2dense {σ :+! τ} (just (inj₂ y)) = zerovDense σ , sparse2dense {τ} y 
    sparse2dense {σ :+! τ} nothing = zerovDense (σ :*! τ) 

    equals-zero : {τ : LTyp} → (x : LinRepDense τ) → Dec (x ≡ zerovDense τ)
    equals-zero {τ} x = LinRepDense≟ {τ} x (zerovDense τ)

    zero-equals-zero : ( τ : LTyp ) → LinRepDense≟ {τ} (zerovDense τ) (zerovDense τ) ≡ yes refl
    zero-equals-zero ( LUn ) = refl
    zero-equals-zero ( LR ) = refl
    zero-equals-zero ( σ :*! τ ) with zero-equals-zero σ | zero-equals-zero τ
    ... | w | v rewrite w rewrite v = refl
    zero-equals-zero ( σ :+! τ ) with zero-equals-zero σ | zero-equals-zero τ
    ... | w | v rewrite w rewrite v = refl

    dense2sparse : { τ : LTyp } → LinRepDense τ → LinRep τ
    dense2sparse { LUn } x = tt
    dense2sparse { LR } x = x
    dense2sparse { σ :*! τ } (x , y) with equals-zero {σ :*! τ} (x , y) 
    ... | yes _ = nothing
    ... | _     = just ((dense2sparse {σ} x) , (dense2sparse {τ} y))
    dense2sparse { σ :+! τ } (x , y) with equals-zero x | equals-zero y
    ... | no  _ | no  _ = nothing -- Invalid, proper implementation would error here
    ... | no  _ | yes _ = just (inj₁ (dense2sparse {σ} x))
    ... | yes _ | no  _ = just (inj₂ (dense2sparse {τ} y))
    ... | yes _ | yes _ = nothing -- Valid, both are zero

    snf : { τ : LTyp } → LinRep τ → LinRep τ
    snf {τ} x = dense2sparse (sparse2dense x)

    snf-nothing-product : ( σ τ : LTyp ) → snf { σ :*! τ } nothing ≡ nothing
    snf-nothing-product σ τ with LinRepDense≟ {σ :*! τ} (zerovDense σ , zerovDense τ) (zerovDense σ , zerovDense τ)
    ... | no ¬a = ⊥-elim (¬a refl)
    ... | yes a = refl

    snf-nothing-sum : ( σ τ : LTyp ) → snf { σ :+! τ } nothing ≡ nothing
    snf-nothing-sum σ τ with LinRepDense≟ {σ} (zerovDense σ) (zerovDense σ) | LinRepDense≟ {τ} (zerovDense τ) (zerovDense τ) 
    ... | no ¬a | no ¬b = refl
    ... | no ¬a | yes b = ⊥-elim (¬a refl)
    ... | yes a | no ¬b = ⊥-elim (¬b refl)
    ... | yes a | yes b = refl

    -- The equivalence lemma between LinRep (sparse) and LinRepDense
    -- ONLY WHEN WE IGNORE SUM TYPES
    LinRepEquiv1 : {τ : LTyp} → (x : LinRepDense τ) → sparse2dense (dense2sparse x) ≡ x
    LinRepEquiv1 {LUn} x = refl
    LinRepEquiv1 {LR} x = refl
    LinRepEquiv1 {σ :*! τ} (x , y) with (LinRepDense≟ {σ :*! τ} (x , y) (zerovDense σ , zerovDense τ))
    ... | no ¬a = cong₂ _,_ (LinRepEquiv1 x) (LinRepEquiv1 y)
    ... | yes a = sym a
    LinRepEquiv1 {σ :+! τ} (x , y) = {!   !} -- incorrect, but okay if we ignore sum-types


    -- The equivalence relation between LinRep (sparse) and LinRepDense
    LinRepEquiv2 : {τ : LTyp} → (x : LinRep τ) → sparse2dense (snf x) ≡ sparse2dense x
    LinRepEquiv2 {LUn} x = refl
    LinRepEquiv2 {LR} x = refl
    LinRepEquiv2 {σ :*! τ} (just (x , y)) 
        with LinRepDense≟ (sparse2dense x) (zerovDense σ)
        | LinRepDense≟ (sparse2dense y) (zerovDense τ)
    ... | no ¬a | no ¬b = cong₂ _,_ (LinRepEquiv2 x) (LinRepEquiv2 y) 
    ... | no ¬a | yes b = cong₂ _,_ (LinRepEquiv2 x) (LinRepEquiv2 y) 
    ... | yes a | no ¬b = cong₂ _,_ (LinRepEquiv2 x) (LinRepEquiv2 y) 
    ... | yes a | yes b = cong₂ _,_ (sym a) (sym b)
    LinRepEquiv2 {σ :*! τ} nothing = cong (sparse2dense {σ :*! τ}) (snf-nothing-product σ τ)
    LinRepEquiv2 {σ :+! τ} (just (inj₁ x)) 
        rewrite (zero-equals-zero τ)
        with LinRepDense≟ (sparse2dense x) (zerovDense σ) 
    ... | no ¬a = cong₂ _,_ (LinRepEquiv2 x) refl
    ... | yes a = cong₂ _,_ (sym a) refl
    LinRepEquiv2 {σ :+! τ} (just (inj₂ x))
        rewrite (zero-equals-zero σ)
        with LinRepDense≟ (sparse2dense x) (zerovDense τ) 
    ... | no ¬a = cong₂ _,_ refl (LinRepEquiv2 x)
    ... | yes a = cong₂ _,_ refl (sym a) 
    LinRepEquiv2 {σ :+! τ} nothing = cong (sparse2dense {σ :+! τ}) (snf-nothing-sum σ τ)


    snf-idempotence : {τ : LTyp} → ( x : LinRep τ ) → snf {τ} (snf {τ} x) ≡ snf {τ} x
    snf-idempotence x = cong dense2sparse (LinRepEquiv2 x)

 

 
 