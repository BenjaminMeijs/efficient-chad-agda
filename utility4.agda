module utility4 where

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

open import utility0
open utility0.App-Eq public
open utility0.Basics public
open utility0.interp-sink public
open utility0.environment-value-tuple public
open utility0.LACMconvenience public  
open utility0.DenseLinRepresentation public

module environment-value-tuple-dense where
    LEtupDense : LEnv -> Set
    LEtupDense [] = ⊤
    LEtupDense (τ ∷ Γ) = LinRepDense τ × LEtupDense Γ

    LEtup-to-LEtupDense : { Γ : LEnv } → LEtup Γ → LEtupDense Γ
    LEtup-to-LEtupDense {[]} tt = tt
    LEtup-to-LEtupDense {(τ ∷ Γ)} (x , xs) = to-LinRepDense {τ} x , LEtup-to-LEtupDense {Γ} xs 

    LEtupDense-to-LEtup : { Γ : LEnv } → LEtupDense Γ → LEtup Γ
    LEtupDense-to-LEtup {[]} tt = tt
    LEtupDense-to-LEtup {(τ ∷ Γ)} (x , xs) = from-LinRepDense {τ} x , LEtupDense-to-LEtup {Γ} xs 

    Etup-to-LEtupDense : {Γ : Env Pr} → LinRepDense (D2τ' (Etup Pr Γ)) → LEtupDense (map D2τ' Γ)
    Etup-to-LEtupDense {[]} tt = tt
    Etup-to-LEtupDense {τ ∷ Γ} (x , xs) = x , Etup-to-LEtupDense xs 

open environment-value-tuple-dense public

module environment-vector-addition where
    -- Definitions
    plusvDense : (τ : LTyp) -> LinRepDense τ -> LinRepDense τ -> LinRepDense τ
    plusvDense LUn tt tt = tt
    plusvDense LR x y = primFloatPlus x y
    plusvDense (σ :*! τ) (x , y) (a , b) = plusvDense σ x a , plusvDense τ y b
    plusvDense (σ :+! τ) (x , y) (a , b) = plusvDense σ x a , plusvDense τ y b

    _ev+_ : {Γ : Env Pr} -> LEtupDense (map D2τ' Γ) -> LEtupDense (map D2τ' Γ) -> LEtupDense (map D2τ' Γ)
    _ev+_ {[]} tt tt = tt
    _ev+_ {typ ∷ Γ} (vL , evL) (vR , evR) = plusvDense (D2τ' typ) vL vR , (evL ev+ evR) 

    zero-LEnvDense : (Γ : Env Pr) -> LEtupDense (map D2τ' Γ)
    zero-LEnvDense [] = tt
    zero-LEnvDense (x ∷ env) = zerovDense  (D2τ' x) , zero-LEnvDense env 

    zerov-is-zerovDense : ( τ : LTyp ) 
                        → to-LinRepDense {τ} (fst (zerov τ)) ≡ zerovDense τ
    zerov-is-zerovDense LUn = refl
    zerov-is-zerovDense LR = refl
    zerov-is-zerovDense (σ :*! τ) = refl
    zerov-is-zerovDense (σ :+! τ) = refl

    -- onehot-LEnv : {Γ : Env Pr} {τ : LTyp} → let Γ' = map D2τ' Γ in 
    --               (idx : Idx Γ' τ) → (val : LinRep τ) → LEtup Γ'
    -- onehot-LEnv {Γ} {τ} idx val = addLEτ {Γ = map D2τ' Γ} idx val (zero-LEnv Γ)
    -- -- plusvDense-is-plusv : {τ : LTyp} {x y : LinRep τ} → plusvDense τ (to-LinRepDense x) (to-LinRepDense y) ≡ to-LinRepDense (plusv τ x y .fst)
    -- addLEτ-to-onehot : {Γ : Env Pr} {τ : LTyp} → let Γ' = map D2τ' Γ in 
    --                   (idx : Idx Γ' τ) -> (val : LinRep τ) -> (evIn : LEtup Γ')
    --                   -> LEtup-to-LEtupDense (addLEτ idx val evIn) ≡ LEtup-to-LEtupDense evIn ev+ LEtup-to-LEtupDense (onehot-LEnv idx val)

    -- Plusv theorems
    postulate
        primFloatPlus-comm : (x : Float) → (y : Float) → primFloatPlus x y ≡ primFloatPlus y x
        primFloatPlus-zeroR : (x : Float) → primFloatPlus x (primNatToFloat 0) ≡ x
        primFloatPlus-assoc : (x : Float) → (y : Float) → (z : Float)
                              → primFloatPlus (primFloatPlus x y) z ≡ primFloatPlus x (primFloatPlus y z)
    plusvDense-zeroR : (τ : LTyp) -> (v : LinRepDense τ) -> plusvDense τ v (zerovDense τ) ≡ v
    plusvDense-zeroL : (τ : LTyp) -> (v : LinRepDense τ) -> plusvDense τ (zerovDense τ) v ≡ v
    plusvDense-zeroR' : { τ : LTyp } { a b : LinRepDense τ } →  {{b ≡ zerovDense τ}} → plusvDense τ a b ≡ a
    plusvDense-zeroL' : { τ : LTyp } { a b : LinRepDense τ } →  {{a ≡ zerovDense τ}} → plusvDense τ a b ≡ b
    plusvDense-comm : (τ : LTyp) -> (a : LinRepDense τ) -> (b : LinRepDense τ) -> plusvDense τ a b ≡ plusvDense τ b a
    plusvDense-assoc : (τ : LTyp) → (a : LinRepDense τ) → (b : LinRepDense τ) (c : LinRepDense τ)
              →  plusvDense τ (plusvDense τ a b) c ≡ plusvDense τ a (plusvDense τ b c)
    plusvDense-congR : { τ : LTyp } -> { a b c : LinRepDense τ } → b ≡ c → plusvDense τ a b ≡ plusvDense τ a c
    plusvDense-congL : { τ : LTyp } -> { a b c : LinRepDense τ } → a ≡ c → plusvDense τ a b ≡ plusvDense τ c b

    -- ev+ theorems
    ev+comm : {Γ : Env Pr} → (a : LEtupDense (map D2τ' Γ)) → (b : LEtupDense (map D2τ' Γ)) → a ev+ b ≡ b ev+ a
    ev+assoc : {Γ : Env Pr} → (a : LEtupDense (map D2τ' Γ)) → (b : LEtupDense (map D2τ' Γ)) → (c : LEtupDense (map D2τ' Γ))
              → (a ev+ b) ev+ c ≡ a ev+ (b ev+ c)
    -- interp-zerot≡zerovDense : {Γ : Env Du} {env : Val Du Γ} → (τ : Typ Pr)
    --                             → interp env (zerot τ) ≡ zerovDense (D2τ' τ)
    ev+zeroR : {Γ : Env Pr} → (a : LEtupDense (map D2τ' Γ)) → a ev+ (zero-LEnvDense Γ) ≡ a
    ev+zeroL : {Γ : Env Pr} → (a : LEtupDense (map D2τ' Γ)) → (zero-LEnvDense Γ) ev+ a ≡ a
    ev+zeroL' : {Γ : Env Pr} {a : LEtupDense (map D2τ' Γ)} → {b : LEtupDense (map D2τ' Γ)} → a ≡ zero-LEnvDense Γ  → a ev+ b ≡ b
    ev+zeroR' : {Γ : Env Pr} {a : LEtupDense (map D2τ' Γ)} {b : LEtupDense (map D2τ' Γ)} → b ≡ zero-LEnvDense Γ  → a ev+ b ≡ a
    ev+congR : {Γ : Env Pr} {x : LEtupDense (map D2τ' Γ)} {y : LEtupDense (map D2τ' Γ)} {z : LEtupDense (map D2τ' Γ)} → y ≡ z
              → x ev+ y ≡ x ev+ z
    ev+congL : {Γ : Env Pr} {x : LEtupDense (map D2τ' Γ)} {y : LEtupDense (map D2τ' Γ)} {z : LEtupDense (map D2τ' Γ)} → x ≡ z
              → x ev+ y ≡ z ev+ y
    zerovDense-on-Etup-is-zeroLEnv2 : {Γ : Env Pr} → Etup-to-LEtupDense (zerovDense (D2τ' (Etup Pr Γ))) ≡ zero-LEnvDense Γ
    zerov-LEnvDense-is-zero-LEnv : {Γ : Env Pr} → zero-LEnvDense Γ ≡ LEtup-to-LEtupDense (zero-LEnv Γ) 
    evplus-on-Etup-is-plusv : {Γ : Env Pr} → ( x : LinRepDense (D2τ' (Etup Pr Γ)) ) → ( y : LinRepDense (D2τ' (Etup Pr Γ)) )
                        → Etup-to-LEtupDense x ev+ Etup-to-LEtupDense y
                        ≡ Etup-to-LEtupDense (plusvDense (D2τ' (Etup Pr Γ)) x y)
    interp-zerot≡zerov : {Γ : Env Du} {env : Val Du Γ}
                                → (τ : Typ Pr)
                                → interp env (zerot τ) ≡ zerov (D2τ' τ) .fst
    interp-zerot≡zerovDense : {Γ : Env Du} {env : Val Du Γ}
                                → (τ : Typ Pr)
                                → to-LinRepDense {D2τ' τ} (interp env (zerot τ)) ≡ zerovDense (D2τ' τ)
    
    -- proofs of plusvDense theorems
    plusvDense-zeroR LUn v = refl
    plusvDense-zeroR LR v = primFloatPlus-zeroR v
    plusvDense-zeroR (σ :*! τ) (x , y) = cong₂ (_,_) (plusvDense-zeroR σ x) (plusvDense-zeroR τ y)
    plusvDense-zeroR (σ :+! τ) (x , y) = cong₂ (_,_) (plusvDense-zeroR σ x) (plusvDense-zeroR τ y) 

    plusvDense-zeroL τ v = trans (plusvDense-comm τ (zerovDense τ) v) (plusvDense-zeroR τ v) 
    plusvDense-zeroR' {τ} {a} {b} {{w}} = trans (cong (λ e → plusvDense τ a e) w) (plusvDense-zeroR τ a) 
    plusvDense-zeroL' {τ} {a} {b} {{w}} = trans (cong (λ e → plusvDense τ e b) w) (plusvDense-zeroL τ b)

    plusvDense-comm LUn a b = refl
    plusvDense-comm LR a b = primFloatPlus-comm a b
    plusvDense-comm (σ :*! τ) (x , y) (a , b) = cong₂ (_,_) (plusvDense-comm σ x a) (plusvDense-comm τ y b) 
    plusvDense-comm (σ :+! τ) (x , y) (a , b) = cong₂ (_,_) (plusvDense-comm σ x a) (plusvDense-comm τ y b)
    
    plusvDense-assoc LUn a b c = refl
    plusvDense-assoc LR a b c = primFloatPlus-assoc a b c
    plusvDense-assoc (σ :*! τ) (a1 , a2) (b1 , b2) (c1 , c2) = cong₂ (_,_) (plusvDense-assoc σ a1 b1 c1) (plusvDense-assoc τ a2 b2 c2) 
    plusvDense-assoc (σ :+! τ) (a1 , a2) (b1 , b2) (c1 , c2) = cong₂ (_,_) (plusvDense-assoc σ a1 b1 c1) (plusvDense-assoc τ a2 b2 c2)

    plusvDense-congR refl = refl
    plusvDense-congL refl = refl


    -- proofs of ev+ theorems
    ev+congR w = cong₂ _ev+_ refl w
    ev+congL w = cong₂ _ev+_ w refl
    ev+zeroR {[]} x = refl
    ev+zeroR {τ ∷ Γ} (x , xs) = cong₂ (_,_) (plusvDense-zeroR (D2τ' τ) x) (ev+zeroR xs) 
    ev+zeroL {Γ} x = trans (ev+comm (zero-LEnvDense Γ) x) (ev+zeroR x)  
    ev+zeroR' {Γ} {a} {b} w = trans (ev+congR w) (ev+zeroR a)
    ev+zeroL' {Γ} {a} {b} w = trans (ev+congL w) (ev+zeroL b)

    interp-zerot≡zerov Un = refl
    interp-zerot≡zerov Inte = refl
    interp-zerot≡zerov R = refl
    interp-zerot≡zerov (σ :* τ) = refl
    interp-zerot≡zerov (σ :+ τ) = refl 

    interp-zerot≡zerovDense Un = refl
    interp-zerot≡zerovDense Inte = refl
    interp-zerot≡zerovDense R = refl
    interp-zerot≡zerovDense (σ :* τ) = refl
    interp-zerot≡zerovDense (σ :+ τ) = refl

    ev+comm {[]} a b = refl 
    ev+comm {τ ∷ Γ} a b = cong₂ (_,_) (plusvDense-comm (D2τ' τ) (a .fst) (b .fst)) (ev+comm (a .snd) (b .snd)) 
    ev+assoc {[]} a b c = refl
    ev+assoc {τ ∷ Γ} a b c = cong₂ (_,_) (plusvDense-assoc (D2τ' τ) (a .fst) (b .fst) (c .fst)) (ev+assoc (a .snd) (b .snd) (c .snd))

    zerovDense-on-Etup-is-zeroLEnv2 {[]} = refl
    zerovDense-on-Etup-is-zeroLEnv2 {τ ∷ Γ} = cong₂ (_,_) refl zerovDense-on-Etup-is-zeroLEnv2

    zerov-LEnvDense-is-zero-LEnv {[]} = refl
    zerov-LEnvDense-is-zero-LEnv {τ ∷ Γ} = cong₂ (_,_) (sym (zerov-is-zerovDense (D2τ' τ))) zerov-LEnvDense-is-zero-LEnv 

    evplus-on-Etup-is-plusv {[]} x y = refl
    evplus-on-Etup-is-plusv {τ ∷ t} (x , xs) (y , ys) = cong₂ (_,_) refl (evplus-on-Etup-is-plusv xs ys)
 
open environment-vector-addition public
