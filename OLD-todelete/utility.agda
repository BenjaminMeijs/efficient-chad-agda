{-# OPTIONS --allow-unsolved-metas #-}
module utility where
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

module environment-vector-addition where
    -- Question, Is it smart to base the proof around Environment Vector addition?
    _ev+_ : {Γ : Env Pr} -> LEtup (map D2τ' Γ) -> LEtup (map D2τ' Γ) -> LEtup (map D2τ' Γ)
    _ev+_ {[]} tt tt = tt
    _ev+_ {typ ∷ Γ} (vL , evL) (vR , evR) = fst (plusv (D2τ' typ) vL vR) , (evL   ev+  evR )

    postulate
        primFloatPlus-comm : (x : Float) → (y : Float) → primFloatPlus x y ≡ primFloatPlus y x
        primFloatPlus-zeroR : (x : Float) → primFloatPlus x (primNatToFloat 0) ≡ x
        primFloatPlus-assoc : (x : Float) → (y : Float) → (z : Float)
                              → primFloatPlus (primFloatPlus x y) z ≡ primFloatPlus x (primFloatPlus y z)

    plusv-comm : (τ : LTyp) -> (a : LinRep τ) -> (b : LinRep τ) -> fst (plusv τ a b) ≡ fst (plusv τ b a)
    plusv-comm LUn tt tt = refl
    plusv-comm LR x y = primFloatPlus-comm x y
    plusv-comm (σ :*! τ) nothing nothing = refl
    plusv-comm (σ :*! τ) nothing (just x) = refl
    plusv-comm (σ :*! τ) (just x) nothing = refl
    plusv-comm (σ :*! τ) (just (x , y)) (just (x' , y')) = cong₂ (λ a b → just (a , b)) (plusv-comm σ x x' ) (plusv-comm τ y y' )
    plusv-comm (σ :+! τ) nothing nothing = refl
    plusv-comm (σ :+! τ) (just x) nothing = refl
    plusv-comm (σ :+! τ) nothing (just y) = refl
    plusv-comm (σ :+! τ) (just (inj₁ x)) (just (inj₁ y)) = cong (λ a → just (inj₁ a)) (plusv-comm σ x y) 
    plusv-comm (σ :+! τ) (just (inj₂ x)) (just (inj₂ y)) = cong (λ a → just (inj₂ a)) (plusv-comm τ x y)
    plusv-comm (σ :+! τ) (just (inj₁ x)) (just (inj₂ y)) = refl
    plusv-comm (σ :+! τ) (just (inj₂ x)) (just (inj₁ y)) = refl

    ev+comm : {Γ : Env Pr} → (a : LEtup (map D2τ' Γ)) → (b : LEtup (map D2τ' Γ)) → a ev+ b ≡ b ev+ a
    ev+comm {[]} tt tt = refl
    ev+comm {x ∷ Γ} (vL , evL) (vR , evR) = cong₂ (_,_) (plusv-comm (D2τ' x) vL  vR) (ev+comm evL evR)

    plusv-zeroR : (τ : LTyp) -> (v : LinRep τ) -> fst (plusv τ v (fst (zerov τ))) ≡ v
    plusv-zeroR LUn tt = refl
    plusv-zeroR LR v = primFloatPlus-zeroR v
    plusv-zeroR (σ :*! τ) (just (x , y)) = refl
    plusv-zeroR (σ :*! τ) nothing = refl
    plusv-zeroR (σ :+! τ) (just (inj₁ x)) = refl
    plusv-zeroR (σ :+! τ) (just (inj₂ x)) = refl
    plusv-zeroR (σ :+! τ) nothing = refl

    plusv-zeroR' : { τ : LTyp } { a b : LinRep τ } →  {{b ≡ (fst (zerov τ))}} → fst (plusv τ a b) ≡ a
    plusv-zeroR' {τ} {a} {b} {{w}} = trans (cong (λ e → fst (plusv τ a e)) w) (plusv-zeroR τ a)

    plusv-zeroL : (τ : LTyp) -> (v : LinRep τ) -> fst (plusv τ (fst (zerov τ)) v) ≡ v
    plusv-zeroL τ v = trans (plusv-comm τ (fst (zerov τ)) v) (plusv-zeroR τ v)

    plusv-zeroL' : { τ : LTyp } { a b : LinRep τ } →  {{a ≡ (fst (zerov τ))}} → fst (plusv τ a b) ≡ b
    plusv-zeroL' {τ} {a} {b} {{w}} = trans (cong (λ e → fst (plusv τ e b)) w) (plusv-zeroL τ b)

    ev+zeroR : {Γ : Env Pr} → (a : LEtup (map D2τ' Γ)) → a ev+ (zero-LEnv Γ) ≡ a
    ev+zeroR {Γ = []} tt = refl
    ev+zeroR {Γ = x ∷ Γ} (v , ev) = cong₂ (_,_) (plusv-zeroR (D2τ' x) v)  (ev+zeroR ev)

    ev+zeroL : {Γ : Env Pr} → (a : LEtup (map D2τ' Γ)) → (zero-LEnv Γ) ev+ a ≡ a
    ev+zeroL {Γ} v = trans (ev+comm (zero-LEnv Γ) v)  (ev+zeroR v)

    ev+zeroR' : {Γ : Env Pr} {a : LEtup (map D2τ' Γ)} {b : LEtup (map D2τ' Γ)} → b ≡ zero-LEnv Γ  → a ev+ b ≡ a
    ev+zeroR' {Γ} {a} {b} w = trans (cong₂ _ev+_ refl w) (ev+zeroR a)
    ev+zeroL' : {Γ : Env Pr} {a : LEtup (map D2τ' Γ)} → {b : LEtup (map D2τ' Γ)} → a ≡ zero-LEnv Γ  → a ev+ b ≡ b
    ev+zeroL' {Γ} {a} {b} w = trans (cong₂ _ev+_ w refl) (ev+zeroL b)

    plusv-assoc : (τ : LTyp) → (a : LinRep τ) → (b : LinRep τ) (c : LinRep τ)
              →  fst (plusv τ (fst (plusv τ a b)) c) ≡ fst (plusv τ a (fst (plusv τ b c)))
    plusv-assoc LUn tt tt tt = refl
    plusv-assoc LR a b c = primFloatPlus-assoc a b c
    plusv-assoc (σ :*! τ) nothing b c = refl
    plusv-assoc (σ :*! τ) (just a) nothing c = refl
    plusv-assoc (σ :*! τ) (just a) (just b) nothing = refl
    plusv-assoc (σ :*! τ) (just a) (just b) (just c) = cong₂ (λ x y → just (x , y)) (plusv-assoc σ (a .fst) (b .fst) (c .fst)) (plusv-assoc τ (a .snd) (b .snd) (c .snd))
    plusv-assoc (σ :+! τ) nothing nothing nothing = refl
    plusv-assoc (σ :+! τ) nothing nothing (just c) = refl
    plusv-assoc (σ :+! τ) nothing (just b) nothing = refl
    plusv-assoc (σ :+! τ) (just a) nothing (just x) = refl
    plusv-assoc (σ :+! τ) (just a) nothing nothing = refl
    plusv-assoc (σ :+! τ) (just a) (just b) nothing = refl
    plusv-assoc (σ :+! τ) nothing (just (inj₁ b)) (just (inj₁ c)) = refl
    plusv-assoc (σ :+! τ) nothing (just (inj₁ b)) (just (inj₂ c)) = refl
    plusv-assoc (σ :+! τ) nothing (just (inj₂ b)) (just (inj₁ c)) = refl
    plusv-assoc (σ :+! τ) nothing (just (inj₂ b)) (just (inj₂ c)) = refl
    plusv-assoc (σ :+! τ) (just (inj₁ a)) (just (inj₁ b)) (just (inj₁ c)) = cong (λ x → just (inj₁ x)) (plusv-assoc σ a b c) 
    plusv-assoc (σ :+! τ) (just (inj₂ a)) (just (inj₂ b)) (just (inj₂ c)) = cong (λ x → just (inj₂ x)) (plusv-assoc τ a b c) 
    -- Note: These are impossible to prove due to the "wrong" definition of LinRep σ :+! τ
    plusv-assoc (σ :+! τ) (just (inj₁ a)) (just (inj₁ b)) (just (inj₂ c)) = {!   !}
    plusv-assoc (σ :+! τ) (just (inj₁ a)) (just (inj₂ b)) (just (inj₁ c)) = {!   !}
    plusv-assoc (σ :+! τ) (just (inj₁ a)) (just (inj₂ b)) (just (inj₂ c)) = {!   !}
    plusv-assoc (σ :+! τ) (just (inj₂ a)) (just (inj₁ b)) (just (inj₁ c)) = {!   !}
    plusv-assoc (σ :+! τ) (just (inj₂ a)) (just (inj₁ b)) (just (inj₂ c)) = {!   !}
    plusv-assoc (σ :+! τ) (just (inj₂ a)) (just (inj₂ b)) (just (inj₁ c)) = {!   !}

    ev+assoc : {Γ : Env Pr} → (a : LEtup (map D2τ' Γ)) → (b : LEtup (map D2τ' Γ)) → (c : LEtup (map D2τ' Γ))
              → (a ev+ b) ev+ c ≡ a ev+ (b ev+ c)
    ev+assoc {[]} a b c = refl
    ev+assoc {τ ∷ Γ} a b c = cong₂ (_,_) (plusv-assoc (D2τ' τ) (a .fst) (b .fst) (c .fst))  (ev+assoc (a .snd) (b .snd) (c .snd))
    
    interp-zerot≡zerov : {Γ : Env Du} {env : Val Du Γ}
                                → (τ : Typ Pr)
                                → interp env (zerot τ) ≡ zerov (D2τ' τ) .fst
    interp-zerot≡zerov Un = refl
    interp-zerot≡zerov Inte = refl
    interp-zerot≡zerov R = refl
    interp-zerot≡zerov (σ :* τ) = refl
    interp-zerot≡zerov (σ :+ τ) = refl 

    onehot-LEnv : {Γ : Env Pr} {τ : LTyp} → let Γ' = map D2τ' Γ in 
                  (idx : Idx Γ' τ) → (val : LinRep τ) → LEtup Γ'
    onehot-LEnv {Γ} {τ} idx val = addLEτ {Γ = map D2τ' Γ} idx val (zero-LEnv Γ)

    addLEτ-to-onehot : {Γ : Env Pr} {τ : LTyp} → let Γ' = map D2τ' Γ in 
                      (idx : Idx Γ' τ) -> (val : LinRep τ) -> (evIn : LEtup Γ')
                      -> (addLEτ idx val evIn) ≡ evIn ev+ onehot-LEnv idx val
    addLEτ-to-onehot {σ ∷ Γ} {τ} Z val (x , xs) =
      cong₂ (_,_) (trans (plusv-comm (D2τ' σ) val x)
                        (cong (λ e → fst (plusv (D2τ' σ) x e)) (sym (plusv-zeroR (D2τ' σ) val))))
                  (sym (ev+zeroR' refl ))
    addLEτ-to-onehot {σ ∷ Γ} {τ} (S idx) val (x , xs) =
      cong₂ (_,_) (sym (trans (cong (λ e → fst (plusv (D2τ' σ) x e)) refl) (plusv-zeroR (D2τ' σ) x)))
                  (addLEτ-to-onehot idx val xs)
    
    ev+congR : {Γ : Env Pr} {x : LEtup (map D2τ' Γ)} {y : LEtup (map D2τ' Γ)} {z : LEtup (map D2τ' Γ)} → y ≡ z
              → x ev+ y ≡ x ev+ z
    ev+congR w = cong₂ _ev+_ refl w
    ev+congL : {Γ : Env Pr} {x : LEtup (map D2τ' Γ)} {y : LEtup (map D2τ' Γ)} {z : LEtup (map D2τ' Γ)} → x ≡ z
              → x ev+ y ≡ z ev+ y
    ev+congL w = cong₂ _ev+_ w refl

open environment-vector-addition public

ev+-onEtup-is-plusv : {Γ : Env Pr} → ( x : LinRep (D2τ' (Etup Pr Γ)) ) → ( y : LinRep (D2τ' (Etup Pr Γ)) )
                    → Etup-to-LEtup x ev+ Etup-to-LEtup y
                      ≡ Etup-to-LEtup (plusv (D2τ' (Etup Pr Γ)) x y .fst)
ev+-onEtup-is-plusv {[]} x y = refl
ev+-onEtup-is-plusv {τ ∷ Γ} ( just x )  ( nothing ) = cong₂ (_,_) plusv-zeroR'  (ev+zeroR' refl) 
ev+-onEtup-is-plusv {τ ∷ Γ} ( just x )  ( just y )  = cong₂ (_,_) refl (ev+-onEtup-is-plusv (x .snd) (y .snd)) 
ev+-onEtup-is-plusv {τ ∷ Γ} ( nothing ) ( just y )  = cong₂ (_,_) plusv-zeroL' (ev+zeroL' refl)
ev+-onEtup-is-plusv {τ ∷ Γ} ( nothing ) ( nothing ) = cong₂ (_,_) plusv-zeroL' (ev+zeroL' refl) 
