module HO-correctness.dense-rep where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Float using (Float; primFloatPlus; primFloatTimes; primFloatNegate; primFloatLess)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Unit using (⊤; tt)

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Maybe using (Is-just; maybe′)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable using (dec⇒maybe; yes; no)

open import spec
open import spec.HL
import spec.LACM as LACM
open LACM using (LACM)

-- Postulations about Floats
postulate
    primFloatPlus-comm : (x : Float) → (y : Float) → primFloatPlus x y ≡ primFloatPlus y x
    primFloatPlus-zeroR : (x : Float) → primFloatPlus x 0.0 ≡ x
    primFloatPlus-assoc : (x : Float) → (y : Float) → (z : Float)
                            → primFloatPlus (primFloatPlus x y) z ≡ primFloatPlus x (primFloatPlus y z)
    primFloatTimes-identityL : (x : Float) → primFloatTimes 0.0 x ≡ 0.0
    primFloatNegativeZero : primFloatNegate 0.0 ≡ 0.0


module environment-value-tuple where
    ET : ( tag : PDTag ) → List (Typ tag) → Typ tag
    ET _ [] = Un
    ET tag (τ ∷ Γ) = τ :* ET tag Γ

    ET-to-val : ∀ {tag} {Γ : Env tag} → Rep (ET tag Γ) → Val tag Γ 
    ET-to-val {_} {[]} _ = empty
    ET-to-val {_} {τ ∷ Γ} (x , xs) = push x (ET-to-val xs)

open environment-value-tuple public

module dense-linear-representation where

    {-# TERMINATING #-}
    LinRepDense : LTyp → Set
    LinRepDense LUn = ⊤
    LinRepDense LR = Float
    LinRepDense (σ :*! τ) = LinRepDense σ × LinRepDense τ
    LinRepDense (σ :+! τ) = LinRepDense σ × LinRepDense τ
    LinRepDense Dyn = ((t : LTyp) -> LinRepDense t)

    {-# TERMINATING #-}
    zerovDense : (τ : LTyp) → LinRepDense τ 
    zerovDense LUn = tt
    zerovDense LR = 0.0
    zerovDense (σ :*! τ) = zerovDense σ , zerovDense τ
    zerovDense (σ :+! τ) = zerovDense σ , zerovDense τ
    zerovDense Dyn t = zerovDense t

    sparse2dense : { τ : LTyp } → LinRep τ → LinRepDense τ
    sparse2dense {LUn} tt = tt
    sparse2dense {LR} x = x
    sparse2dense {σ :*! τ} (just (x , y)) = sparse2dense {σ} x , sparse2dense {τ} y 
    sparse2dense {σ :*! τ} nothing = zerovDense (σ :*! τ) 
    sparse2dense {σ :+! τ} (just (inj₁ x)) = sparse2dense {σ} x , zerovDense τ
    sparse2dense {σ :+! τ} (just (inj₂ y)) = zerovDense σ , sparse2dense {τ} y 
    sparse2dense {σ :+! τ} nothing = zerovDense (σ :*! τ) 
    sparse2dense {Dyn} (just (τ , x)) = 
        λ t → case dec⇒maybe (τ LTyp≟ t) of 
            maybe′ (λ w → subst LinRepDense w (sparse2dense x)) 
                (zerovDense t) -- error, we decide to give a zero value
    sparse2dense {Dyn} nothing = zerovDense

    {-# TERMINATING #-}
    plusvDense : (τ : LTyp) → LinRepDense τ → LinRepDense τ → LinRepDense τ
    plusvDense LUn tt tt = tt
    plusvDense LR x y = primFloatPlus x y
    plusvDense (σ :*! τ) (x , y) (a , b) = plusvDense σ x a , plusvDense τ y b
    plusvDense (σ :+! τ) (x , y) (a , b) = plusvDense σ x a , plusvDense τ y b
    plusvDense Dyn x y = λ τ → plusvDense τ (x τ) (y τ)

    postulate 
        LRD-ext : (x : LinRepDense Dyn) → (y : LinRepDense Dyn) → ((τ : LTyp) → x τ ≡ y τ) → x ≡ y
open dense-linear-representation public

module environment-vector where
    EV : LEnv → Set
    EV Γ = HL Γ LinRepDense

    LETs2d : { Γ : LEnv } → LETs Γ → EV Γ
    LETs2d {[]} tt = tt
    LETs2d {(τ ∷ Γ)} (x , xs) = sparse2dense {τ} x , LETs2d {Γ} xs 

    LRD-ET2LETd : {Γ : Env Pr} → LinRepDense (D2τ' (ET Pr Γ)) → EV (map D2τ' Γ)
    LRD-ET2LETd {[]} tt = tt
    LRD-ET2LETd {τ ∷ Γ} (x , xs) = x , LRD-ET2LETd xs 

    zero-EV : (Γ : LEnv) → EV Γ
    zero-EV [] = tt
    zero-EV (x ∷ env) = zerovDense x , zero-EV env 

    _ev+_ : {Γ : LEnv} → EV Γ → EV Γ → EV Γ
    _ev+_ {[]} tt tt = tt
    _ev+_ {typ ∷ Γ} (vL , evL) (vR , evR) = plusvDense _ vL vR , (evL ev+ evR)

open environment-vector public


module value-compatibility where
    -- x ≃ y is a witness to the fact that x and y are compatible (of the same shape) in their constructors for sum types.
    -- i.e. whenever x is inj₁, y is also inj₁
    _≃τ_ : {τ : Typ Pr} → LinRep (D2τ' τ) → Rep τ  → Set
    _≃τ_ {Un} x y = ⊤
    _≃τ_ {Inte} x y = ⊤
    _≃τ_ {R} x y = ⊤
    _≃τ_ {σ :* τ} (just (x1 , x2)) (y1 , y2) = x1 ≃τ y1 × x2 ≃τ y2
    _≃τ_ {σ :* τ} nothing _ = ⊤
    _≃τ_ {σ :+ τ} (just (inj₁ x)) (inj₁ y) = x ≃τ y
    _≃τ_ {σ :+ τ} (just (inj₂ x)) (inj₁ y) = ⊥
    _≃τ_ {σ :+ τ} (just (inj₁ x)) (inj₂ y) = ⊥
    _≃τ_ {σ :+ τ} (just (inj₂ x)) (inj₂ y) = x ≃τ y
    _≃τ_ {σ :+ τ} nothing _ = ⊤
    -- TODO: Figure out what compatible functions with Dyn should be
    _≃τ_ {σ :-> τ} x f = ⊤


    _≃Γ_ : {Γ : Env Pr} → LETs (map D2τ' Γ) → Val Pr Γ  → Set
    _≃Γ_ {[]} x y = ⊤
    _≃Γ_ {τ ∷ Γ} (x , xs) (push y ys) = (_≃τ_ {τ} x y) × (xs ≃Γ ys)

    -- Note that these other kinds of compatibility are not part of the specification for the correctness proof
    -- These witnesses are only used as preconditions for (internal) compatibility lemmas.
    Compatible-LinReps : {τ : LTyp} → LinRep τ → LinRep τ → Set
    Compatible-LinReps {LUn} x y = ⊤
    Compatible-LinReps {LR} x y = ⊤
    Compatible-LinReps {σ :*! τ} (just (x1 , x2)) (just (y1 , y2)) = (Compatible-LinReps x1 y1) × (Compatible-LinReps x2 y2) 
    Compatible-LinReps {σ :*! τ} (just x) nothing = ⊤
    Compatible-LinReps {σ :*! τ} nothing (just x) = ⊤
    Compatible-LinReps {σ :*! τ} nothing nothing = ⊤
    Compatible-LinReps {σ :+! τ} (just (inj₁ x)) (just (inj₁ y)) = Compatible-LinReps x y
    Compatible-LinReps {σ :+! τ} (just (inj₁ x)) (just (inj₂ y)) = ⊥
    Compatible-LinReps {σ :+! τ} (just (inj₂ x)) (just (inj₁ y)) = ⊥
    Compatible-LinReps {σ :+! τ} (just (inj₂ x)) (just (inj₂ y)) = Compatible-LinReps x y
    Compatible-LinReps {σ :+! τ} (just x) nothing = ⊤
    Compatible-LinReps {σ :+! τ} nothing (just x) = ⊤
    Compatible-LinReps {σ :+! τ} nothing nothing = ⊤
    -- TODO: figure out what Compatible-LinReps means for Dyn
    Compatible-LinReps {Dyn} _ _ = ⊤

    Compatible-idx-LETs : {Γ : Env Pr} {τ : Typ Pr} → ((Idx Γ τ) × (LinRep (D2τ' τ)))  → (LETs (map D2τ' Γ) ) → Set
    Compatible-idx-LETs {Γ} {τ} (Z , x) (y , ys) = Compatible-LinReps x y
    Compatible-idx-LETs {Γ} {τ} (S idx , x) (y , ys) = Compatible-idx-LETs (idx , x) ys

    Compatible-idx-val : {Γ : Env Pr} {τ : Typ Pr} → ((Idx Γ τ) × (LinRep (D2τ' τ)))  → (Val Pr Γ) → Set
    Compatible-idx-val {Γ} {τ} (Z , x) (push y ys) = x ≃τ y 
    Compatible-idx-val {Γ} {τ} (S idx , x) (push y ys) = Compatible-idx-val (idx , x) ys
open value-compatibility public