open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Maybe
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
import spec as S
import spec.LACM as LACM
open LACM using (LACM)

-- ==========================================
-- Convenience functions
-- ==========================================

-- eval from 'Spec', ignoring the complexity cost
interp : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> Val tag Γ -> Term tag Γ τ -> Rep τ
interp env e = fst (S.eval env e)

-- Produces "a large tuple of zeros" for all variables in the environment
zero-LEnv : (Γ : Env Pr) -> LEtup (map D2τ' Γ)
zero-LEnv [] = tt
zero-LEnv (x ∷ env) = fst ( zerov $ D2τ' x) , zero-LEnv env

-- Question, Is it smart to base the proof around Environment Vector addition?
_ev+_ : {Γ : Env Pr} -> LEtup (map D2τ' Γ) -> LEtup (map D2τ' Γ) -> LEtup (map D2τ' Γ)
_ev+_ {[]} tt tt = tt
_ev+_ {typ ∷ Γ} (vL , evL) (vR , evR) = fst (plusv (D2τ' typ) vL vR) , (evL   ev+  evR )

postulate
    primFloatPlus-comm : (x : Float) → (y : Float) → primFloatPlus x y ≡ primFloatPlus y x
    primFloatPlus-zeroR : (x : Float) → primFloatPlus x (primNatToFloat 0) ≡ x

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
plusv-zeroR (τ :*! τ₁) (just (x , y)) = refl
plusv-zeroR (σ :*! τ) nothing = refl
plusv-zeroR (σ :+! τ) (just (inj₁ x)) = refl
plusv-zeroR (σ :+! τ) (just (inj₂ x)) = refl
plusv-zeroR (σ :+! τ) nothing = refl

ev+zeroR : {Γ : Env Pr} → (a : LEtup (map D2τ' Γ)) → a ev+ (zero-LEnv Γ) ≡ a
ev+zeroR {Γ = []} tt = refl
ev+zeroR {Γ = x ∷ Γ} (v , ev) = cong₂ (_,_) (plusv-zeroR (D2τ' x) v)  (ev+zeroR ev)

ev+zeroL : {Γ : Env Pr} → (a : LEtup (map D2τ' Γ)) → (zero-LEnv Γ) ev+ a ≡ a
ev+zeroL {Γ} v = trans (ev+comm (zero-LEnv Γ) v)  (ev+zeroR v)

ev+zeroR' : {Γ : Env Pr} {b : LEtup (map D2τ' Γ)} → (a : LEtup (map D2τ' Γ)) → b ≡ zero-LEnv Γ  → a ev+ b ≡ a
ev+zeroR' {Γ} {b} a w = trans (cong₂ _ev+_ refl w) (ev+zeroR a)

-- LACM.run, only returning the environment
-- Folowing the naming of the haskell state monad
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



-- TODO: voor D2τ' een normaal vorm maken
-- Vanwege sumtypes, just (nothing, nothing) -> nothing . Zo sparse mogelijk, in plaats van zo dense mogelijk.

postulate
    DSem : {Γ : Env Pr} {τ : Typ Pr} 
            → (Val Pr Γ →  Rep τ)                          -- f(x)
            → (Val Du (D1Γ Γ) → Rep (D2τ τ) → LEtup (map D2τ' Γ)) -- f'(x)
    

    -- In essence: When the incoming cotangent is zero, the outgoing cotangent is zero
    DSem-ctg-zero : {Γ : Env Pr} {τ : Typ Pr}
            → (f : Val Pr Γ →  Rep τ) 
            → (env : Val Du (D1Γ Γ)) → (ctg : Rep (D2τ τ))
            → ctg ≡ fst (zerov (D2τ' τ))
            → DSem f env ctg ≡ zero-LEnv Γ

-- Derived lemmas of DSem
DSem-unit : {Γ : Env Pr}
        → (f : Val Pr Γ →  Rep (Un {Pr})) 
        → (env : Val Du (D1Γ Γ)) → (ctg : Rep (D2τ Un))
        → DSem {Γ} {Un} f env ctg ≡ zero-LEnv Γ
DSem-unit f env ctg = DSem-ctg-zero f env ctg refl 

-- Same as DSem-ctg-zero, but more arguments are left implicit for convenient usage.
DSem-ctg-zero' : {Γ : Env Pr} {τ : Typ Pr}
            → { f : Val Pr Γ →  Rep τ } 
            → { env : Val Du (D1Γ Γ) } → { ctg : Rep (D2τ τ) }
            → ctg ≡ fst (zerov (D2τ' τ))
            → DSem f env ctg ≡ zero-LEnv Γ
DSem-ctg-zero' {Γ} {τ} {f} {env} {ctg} w = DSem-ctg-zero f env ctg w

chad-equiv-DSem : {Γ : Env Pr} {τ : Typ Pr} 
                  (env : Val Du (D1Γ Γ))       -- the typing environment
                  (evIn : LEtup (map D2τ' Γ))
                  (ctg : Rep (D2τ τ))            -- ctg, some arbitrary (gradient) input
                  (t : Term Pr Γ τ)            -- f(ctg), the original program
                → LACMexec (fst ((interp env (snd' $ chad t)) ctg)) evIn -- f'(ctg) according to CHAD
                  ≡ evIn ev+ ((DSem (flip interp t) env) ctg)            -- f'(ctg) according to DSem
chad-equiv-DSem {Γ = Γ} env evIn ctg unit = 
  begin
  LACMexec (fst (interp env (snd' $ chad unit) ctg)) evIn 
  ≡⟨ LACMexec-pure _ evIn ⟩
  evIn
  ≡⟨ sym (ev+zeroR' evIn (DSem-ctg-zero' refl)) ⟩
  evIn ev+ (DSem (flip interp unit) env ctg) 
  ∎
chad-equiv-DSem {Γ = Γ} env evIn nothing (pair l r) = 
  let m1 = snd (interp env (chad l)) _ .fst
      m2 = snd (interp env (chad r)) _ .fst
      ihl = chad-equiv-DSem env evIn _ l
      ihr = chad-equiv-DSem env evIn _ r
      ihl' = trans ihl (ev+zeroR' evIn (DSem-ctg-zero' refl))
      ihr' = trans ihr (ev+zeroR' evIn (DSem-ctg-zero' refl))
  in begin
      LACMexec (LACMsequence m1 m2) evIn
      ≡⟨ LACMexec-sequence-unchanged m1 m2 evIn ihl' ⟩
      LACMexec m2 evIn
      ≡⟨ ihr' ⟩
      evIn
      ≡⟨ sym (ev+zeroR' evIn (DSem-ctg-zero' refl)) ⟩
      evIn ev+ DSem (flip interp (pair l r)) env nothing 
      ∎
chad-equiv-DSem {Γ = Γ} env evIn ctg@(just (ctgL , ctgR)) (pair l r) = {!   !}
        -- let m1 = snd (interp env (chad l)) ctgL .fst
        --     m2 = snd (interp env (chad r)) ctgR .fst
        --     m2' = λ _ → m2
        --     r1 , evOutL , _ = LACM.run m1 (zero-LEnv Γ)
        --     r2 , evOutR , _ = LACM.run m2 (zero-LEnv Γ)
        --     ihl = chad-equiv-DSem env ctgL l
        --     ihr = chad-equiv-DSem env ctgR r
        -- in begin
        --    LACMexec (LACMbind m1 m2') (zero-LEnv Γ)
        --    ≡⟨ LACMexec-bind→sum m1 m2' ⟩
        --    evOutL ev+ evOutR
        --    ≡⟨ cong₂ _ev+_ ihl ihr ⟩ -- Apply induction hypothesis
        --    (DSem (flip interp l) env ctgL)
        --    ev+
        --    (DSem (flip interp r) env ctgR)
        --    ≡⟨ {!  !} ⟩ -- chad rule for pairs 
        --    DSem (flip interp (pair l r)) env (just (ctgL , ctgR))
        --    ∎
chad-equiv-DSem {Γ = Γ} env evIn ctg (fst' t) = {!   !}
chad-equiv-DSem {Γ = Γ} env evIn ctg (snd' t) = {!   !}
chad-equiv-DSem {Γ = Γ} env evIn ctg (var x) = {!   !}
chad-equiv-DSem {Γ = Γ} env evIn ctg (let' e t) = {!   !}
chad-equiv-DSem {Γ = Γ} env evIn ctg (prim op t) = {!   !}
chad-equiv-DSem {Γ = Γ} env evIn ctg (inl t) = {!   !}
chad-equiv-DSem {Γ = Γ} env evIn ctg (inr t) = {!   !}
chad-equiv-DSem {Γ = Γ} env evIn ctg (case' c l r) = {!   !}

