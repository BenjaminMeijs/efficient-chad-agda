{-# OPTIONS --allow-unsolved-metas #-}
module utility3 where

open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Maybe
import Data.Maybe as Maybe
open import Agda.Builtin.Float
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
open import eval-sink-commute
import spec as S
import spec.LACM as LACM
open LACM using (LACM)

LACMmap : ∀ {Γ : LEnv} {a b : Set} -> (a -> b) -> LACM Γ a -> LACM Γ b
LACMmap f m = LACM.bind m (λ x → LACM.pure (f x) , ℤ.pos 1)


import utility0
open utility0.DenseLinRepresentation public

module Representation2 where 
    Rep2 : ∀ {tag} -> Typ tag -> Set
    Rep2 Un = ⊤
    Rep2 Inte = ℤ
    Rep2 R = Float
    Rep2 (σ :* τ) = Rep2 σ × Rep2 τ
    Rep2 (σ :+ τ) = Rep2 σ ⊎ Rep2 τ
    Rep2 (σ :-> τ) = Rep2 σ -> Rep2 τ
    Rep2 (EVM Γ τ) = LACM Γ (Rep2 τ)
    Rep2 (Lin τ) = LinRepDense τ


    dense2sparse : (τ : LTyp) → LinRepDense τ → LinRep τ
    dense2sparse LUn tt = tt
    dense2sparse LR x = x
    dense2sparse (σ :*! τ) (x , y) = just (dense2sparse σ x , dense2sparse τ y)
    dense2sparse (σ :+! τ) (x , y) = {!    !}

    from-sparse2dense-equiv-id : (τ : LTyp) → (x : LinRepDense τ) → sparse2dense {τ} (dense2sparse τ x) ≡ x
    from-sparse2dense-equiv-id LUn x = refl
    from-sparse2dense-equiv-id LR x = refl
    from-sparse2dense-equiv-id (σ :*! τ) (x , y) = cong₂ (_,_) (from-sparse2dense-equiv-id σ x) (from-sparse2dense-equiv-id τ y)
    from-sparse2dense-equiv-id (σ :+! τ) (x , y) = cong₂ (_,_) {!   !} {!   !}

    from-Rep2 : ∀ {tag} → (τ : Typ tag) → Rep2 τ → Rep τ
    to-Rep2 : ∀ {tag} → ( τ : Typ tag ) → Rep τ → Rep2 τ

    from-Rep2 Un x = x
    from-Rep2 Inte x = x
    from-Rep2 R x = x
    from-Rep2 (τ :* τ₁) x = from-Rep2 τ (x .fst) , from-Rep2 τ₁ (x .snd)
    from-Rep2 (τ :+ τ₁) (inj₁ x) = inj₁ (from-Rep2 τ x)
    from-Rep2 (τ :+ τ₁) (inj₂ y) = inj₂ (from-Rep2 τ₁ y)
    from-Rep2 (σ :-> τ) f = λ x → from-Rep2 τ (f (to-Rep2 σ x)) , ℤ.pos 0
    from-Rep2 (EVM Γ τ) m = LACMmap (from-Rep2 τ) m
    from-Rep2 (Lin τ) x = dense2sparse τ x

    to-Rep2 Un  x = x
    to-Rep2 Inte  x = x
    to-Rep2 R  x = x
    to-Rep2 (σ :* τ) (x , y) = to-Rep2 σ x , to-Rep2 τ y
    to-Rep2 (σ :+ τ) (inj₁ x) = inj₁ (to-Rep2 σ x)
    to-Rep2 (σ :+ τ) (inj₂ y) = inj₂ (to-Rep2 τ y)
    to-Rep2 (σ :-> τ ) f = λ x → to-Rep2 τ (f (from-Rep2 σ x) .fst)
    to-Rep2 (EVM Γ τ ) m = LACMmap (to-Rep2 τ) m
    to-Rep2 (Lin τ ) x = sparse2dense {τ} x

    primal2 : (τ : Typ Pr) -> Rep2 τ -> Rep2 (D1τ τ)
    primal2 τ x = to-Rep2 (D1τ τ) (primal τ (from-Rep2 τ x))

open Representation2 public

interp : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> Val tag Γ -> Term tag Γ τ -> Rep2 τ
interp {τ = τ} env e = to-Rep2 τ (S.eval env e .fst)

module environment-value-tuple where
    Etup : ( tag : PDTag ) → List (Typ tag) → Typ tag
    Etup _ [] = Un
    Etup tag (τ ∷ Γ) = τ :* Etup tag Γ

    D1Etup-to-val2 : {Γ : Env Pr} → Rep2 (D1τ (Etup Pr Γ)) → Val Du (D1Γ Γ)
    D1Etup-to-val2 {[]} x = empty
    D1Etup-to-val2 {τ ∷ Γ} (x , xs) = push (from-Rep2 (D1τ τ) x) (D1Etup-to-val2 xs)

    Etup-to-val2 : ∀ {tag} {Γ : Env tag} → Rep2 (Etup tag Γ) → Val tag Γ 
    Etup-to-val2 {_} {[]} _ = empty 
    Etup-to-val2 {_} {τ ∷ Γ} (x , xs) = push (from-Rep2 τ x) (Etup-to-val2 xs) 

    LEtup2 : LEnv -> Set
    LEtup2 [] = ⊤
    LEtup2 (τ ∷ Γ) = LinRepDense τ × LEtup2 Γ

    from-LEtup2 : (Γ : LEnv) → LEtup2 Γ → LEtup Γ
    to-LEtup2 : (Γ : LEnv) → LEtup Γ → LEtup2 Γ
    from-LEtup2 [] tt = tt
    from-LEtup2 (τ ∷ Γ) (x , xs) = dense2sparse τ x , from-LEtup2 Γ xs
    to-LEtup2 [] tt = tt
    to-LEtup2 (τ ∷ Γ) (x , xs) = sparse2dense {τ} x , to-LEtup2 Γ xs 

    Etup-to-LEtup2 : {Γ : Env Pr} → LinRepDense (D2τ' (Etup Pr Γ)) → LEtup2 (map D2τ' Γ)
    Etup-to-LEtup2 {[]} tt = tt
    Etup-to-LEtup2 {τ ∷ Γ} (x , xs) = x , Etup-to-LEtup2 xs 
open environment-value-tuple public

module environment-vector-addition where
    -- Definitions
    plusv2 : (τ : LTyp) -> LinRepDense τ -> LinRepDense τ -> LinRepDense τ
    plusv2 LUn tt tt = tt
    plusv2 LR x y = primFloatPlus x y
    plusv2 (σ :*! τ) (x , y) (a , b) = plusv2 σ x a , plusv2 τ y b
    plusv2 (σ :+! τ) (x , y) (a , b) = plusv2 σ x a , plusv2 τ y b

    _ev+_ : {Γ : Env Pr} -> LEtup2 (map D2τ' Γ) -> LEtup2 (map D2τ' Γ) -> LEtup2 (map D2τ' Γ)
    _ev+_ {[]} tt tt = tt
    _ev+_ {typ ∷ Γ} (vL , evL) (vR , evR) = plusv2 (D2τ' typ) vL vR , (evL ev+ evR) 

    zero-LEnv2 : (Γ : Env Pr) -> LEtup2 (map D2τ' Γ)
    zero-LEnv2 [] = tt
    zero-LEnv2 (x ∷ env) = zerovDense  (D2τ' x) , zero-LEnv2 env 

    -- Plusv theorems
    postulate
        primFloatPlus-comm : (x : Float) → (y : Float) → primFloatPlus x y ≡ primFloatPlus y x
        primFloatPlus-zeroR : (x : Float) → primFloatPlus x (primNatToFloat 0) ≡ x
        primFloatPlus-assoc : (x : Float) → (y : Float) → (z : Float)
                              → primFloatPlus (primFloatPlus x y) z ≡ primFloatPlus x (primFloatPlus y z)
    plusv2-zeroR : (τ : LTyp) -> (v : LinRepDense τ) -> plusv2 τ v (zerovDense τ) ≡ v
    plusv2-zeroL : (τ : LTyp) -> (v : LinRepDense τ) -> plusv2 τ (zerovDense τ) v ≡ v
    plusv2-zeroR' : { τ : LTyp } { a b : LinRepDense τ } →  {{b ≡ zerovDense τ}} → plusv2 τ a b ≡ a
    plusv2-zeroL' : { τ : LTyp } { a b : LinRepDense τ } →  {{a ≡ zerovDense τ}} → plusv2 τ a b ≡ b
    plusv2-comm : (τ : LTyp) -> (a : LinRepDense τ) -> (b : LinRepDense τ) -> plusv2 τ a b ≡ plusv2 τ b a
    plusv2-assoc : (τ : LTyp) → (a : LinRepDense τ) → (b : LinRepDense τ) (c : LinRepDense τ)
              →  plusv2 τ (plusv2 τ a b) c ≡ plusv2 τ a (plusv2 τ b c)

    -- ev+ theorems
    ev+comm : {Γ : Env Pr} → (a : LEtup2 (map D2τ' Γ)) → (b : LEtup2 (map D2τ' Γ)) → a ev+ b ≡ b ev+ a
    ev+assoc : {Γ : Env Pr} → (a : LEtup2 (map D2τ' Γ)) → (b : LEtup2 (map D2τ' Γ)) → (c : LEtup2 (map D2τ' Γ))
              → (a ev+ b) ev+ c ≡ a ev+ (b ev+ c)
    interp-zerot≡zerovDense : {Γ : Env Du} {env : Val Du Γ} → (τ : Typ Pr)
                                → interp env (zerot τ) ≡ zerovDense (D2τ' τ)
    ev+zeroR : {Γ : Env Pr} → (a : LEtup2 (map D2τ' Γ)) → a ev+ (zero-LEnv2 Γ) ≡ a
    ev+zeroL : {Γ : Env Pr} → (a : LEtup2 (map D2τ' Γ)) → (zero-LEnv2 Γ) ev+ a ≡ a
    ev+zeroL' : {Γ : Env Pr} {a : LEtup2 (map D2τ' Γ)} → {b : LEtup2 (map D2τ' Γ)} → a ≡ zero-LEnv2 Γ  → a ev+ b ≡ b
    ev+zeroR' : {Γ : Env Pr} {a : LEtup2 (map D2τ' Γ)} {b : LEtup2 (map D2τ' Γ)} → b ≡ zero-LEnv2 Γ  → a ev+ b ≡ a
    ev+congR : {Γ : Env Pr} {x : LEtup2 (map D2τ' Γ)} {y : LEtup2 (map D2τ' Γ)} {z : LEtup2 (map D2τ' Γ)} → y ≡ z
              → x ev+ y ≡ x ev+ z
    ev+congL : {Γ : Env Pr} {x : LEtup2 (map D2τ' Γ)} {y : LEtup2 (map D2τ' Γ)} {z : LEtup2 (map D2τ' Γ)} → x ≡ z
              → x ev+ y ≡ z ev+ y
    zerovDense-on-Etup-is-zeroLEnv2 : {Γ : Env Pr} → Etup-to-LEtup2 (zerovDense (D2τ' (Etup Pr Γ))) ≡ zero-LEnv2 Γ
    
    -- proofs of plusv2 theorems
    plusv2-zeroR LUn v = refl
    plusv2-zeroR LR v = primFloatPlus-zeroR v
    plusv2-zeroR (σ :*! τ) (x , y) = cong₂ (_,_) (plusv2-zeroR σ x) (plusv2-zeroR τ y)
    plusv2-zeroR (σ :+! τ) (x , y) = cong₂ (_,_) (plusv2-zeroR σ x) (plusv2-zeroR τ y) 

    plusv2-zeroL τ v = trans (plusv2-comm τ (zerovDense τ) v) (plusv2-zeroR τ v) 
    plusv2-zeroR' {τ} {a} {b} {{w}} = trans (cong (λ e → plusv2 τ a e) w) (plusv2-zeroR τ a) 
    plusv2-zeroL' {τ} {a} {b} {{w}} = trans (cong (λ e → plusv2 τ e b) w) (plusv2-zeroL τ b)

    plusv2-comm LUn a b = refl
    plusv2-comm LR a b = primFloatPlus-comm a b
    plusv2-comm (σ :*! τ) (x , y) (a , b) = cong₂ (_,_) (plusv2-comm σ x a) (plusv2-comm τ y b) 
    plusv2-comm (σ :+! τ) (x , y) (a , b) = cong₂ (_,_) (plusv2-comm σ x a) (plusv2-comm τ y b)
    
    plusv2-assoc LUn a b c = refl
    plusv2-assoc LR a b c = primFloatPlus-assoc a b c
    plusv2-assoc (σ :*! τ) (a1 , a2) (b1 , b2) (c1 , c2) = cong₂ (_,_) (plusv2-assoc σ a1 b1 c1) (plusv2-assoc τ a2 b2 c2) 
    plusv2-assoc (σ :+! τ) (a1 , a2) (b1 , b2) (c1 , c2) = cong₂ (_,_) (plusv2-assoc σ a1 b1 c1) (plusv2-assoc τ a2 b2 c2)


    -- proofs of ev+ theorems
    ev+congR w = cong₂ _ev+_ refl w
    ev+congL w = cong₂ _ev+_ w refl
    ev+zeroR {[]} x = refl
    ev+zeroR {τ ∷ Γ} (x , xs) = cong₂ (_,_) (plusv2-zeroR (D2τ' τ) x) (ev+zeroR xs) 
    ev+zeroL {Γ} x = trans (ev+comm (zero-LEnv2 Γ) x) (ev+zeroR x)  
    ev+zeroR' {Γ} {a} {b} w = trans (ev+congR w) (ev+zeroR a)
    ev+zeroL' {Γ} {a} {b} w = trans (ev+congL w) (ev+zeroL b)

    interp-zerot≡zerovDense {Γ} {val} Un = refl
    interp-zerot≡zerovDense {Γ} {val} Inte = refl
    interp-zerot≡zerovDense {Γ} {val} R = refl
    interp-zerot≡zerovDense {Γ} {val} (σ :* τ) = refl
    interp-zerot≡zerovDense {Γ} {val} (σ :+ τ) = refl

    ev+comm {[]} a b = refl 
    ev+comm {τ ∷ Γ} a b = cong₂ (_,_) (plusv2-comm (D2τ' τ) (a .fst) (b .fst)) (ev+comm (a .snd) (b .snd)) 
    ev+assoc {[]} a b c = refl
    ev+assoc {τ ∷ Γ} a b c = cong₂ (_,_) (plusv2-assoc (D2τ' τ) (a .fst) (b .fst) (c .fst)) (ev+assoc (a .snd) (b .snd) (c .snd))

    zerovDense-on-Etup-is-zeroLEnv2 {[]} = refl
    zerovDense-on-Etup-is-zeroLEnv2 {τ ∷ Γ} = cong₂ (_,_) refl zerovDense-on-Etup-is-zeroLEnv2

open environment-vector-addition public


module LACMconvenience where
    -- LACM.run, only returning the environment
    -- Folowing the naming of the haskell state monad (MTL)
    abstract
        LACMexec2 : ∀ {Γ : LEnv} {a : Set} -> LACM Γ a -> LEtup2 Γ -> LEtup2 Γ
        LACMexec2 {Γ} f e = {!   !} -- let _ , e' , _ = LACM.run f e in e'

    -- LACMmap : ∀ {Γ : LEnv} {a b : Set} -> (a -> b) -> LACM Γ a -> LACM Γ b
    -- LACMmap f m = LACM.bind m (λ x → LACM.pure (f x) , ℤ.pos 1)
        LACMexec-map2 : ∀ {Γ : LEnv} {a b : Set} → { f : a → b }
                        → (m : LACM Γ a) 
                        → (evIn : LEtup2 Γ)
                        → LACMexec2 (LACMmap f m) evIn ≡ LACMexec2 m evIn
        LACMexec-map2 {f = f} m evIn = {!   !}
            -- let elim-bind = LACMexec-bind m (λ x → LACM.pure (f x)) evIn
                -- elim-pure = LACMexec-pure (f (LACM.run m evIn .fst)) (LACMexec m evIn)
            -- in trans elim-bind elim-pure

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

    LACMexec-pure2 : ∀ {Γ : LEnv} {a : Set} → (x : a)
                  → (ev : LEtup2 Γ) -- ev: Environment Vector
                  → LACMexec2 {Γ} (LACM.pure x) ev ≡ ev
    LACMexec-pure2 {Γ = Γ} x ev = {!   !}

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
open LACMconvenience public  

module interp-sink where
    interp-sink-commute : ∀ {tag} {Γ Γ' : Env tag} {τ : Typ tag}
                    -> (env : Val tag Γ) (env2 : Val tag Γ')
                    -> (w : Weakening Γ Γ')
                    -> sinks-to w env env2
                    -> (e : Term tag Γ τ)
                    -> interp env e ≡ interp env2 (sink w e)
    interp-sink-commute env env2 w s e = {!   !} -- cong fst (eval-sink-commute env env2 w s e)

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
    interp-sink-commute-Copy-Skip-End x env t = {!   !}
        -- sym $
        -- interp-sink-commute (push x env) (push x (push _ env)) (WCopy (WSkip WEnd)) (refl , forall-fin-trivial (λ _ → refl )) t
    
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
    interp-sink-commute-Copy-Copy-Cut x y env t = {!   !}
    --   let env1 = push x (push y env)
        --   env2 = push x (push y empty)
    --   in sym (interp-sink-commute env2 env1 (WCopy (WCopy WCut)) (refl , refl , tt) t)
  
open interp-sink public