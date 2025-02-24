module correctness.lemmas.environment-vector-lemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Float using (Float; primFloatPlus; primNatToFloat)

open import Data.List using ([]; _∷_; map)
open import Data.Product using (_×_)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)

open import spec
open import correctness.spec

-- TODO: rename to LinRep-is-monoid

module plusv-lemmas where
    -- This can be derived from the postulations
    primFloatPlus-zeroL : (x : Float) → primFloatPlus (primNatToFloat 0) x ≡ x

    -- sparse plus
    plusvSparse-zeroR : (τ : LTyp) -> (v : LinRep τ) -> plusv τ v (zerov τ .fst) .fst ≡ v
    plusvSparse-zeroL : (τ : LTyp) -> (v : LinRep τ) -> plusv τ (zerov τ .fst) v .fst ≡ v
    plusvSparse-comm : (τ : LTyp) -> (a : LinRep τ) -> (b : LinRep τ) -> plusv τ a b .fst ≡ plusv τ b a .fst

    -- dense plus
    plusvDense-zeroR : (τ : LTyp) -> (v : LinRepDense τ) -> plusvDense τ v (zerovDense τ) ≡ v
    plusvDense-zeroL : (τ : LTyp) -> (v : LinRepDense τ) -> plusvDense τ (zerovDense τ) v ≡ v
    plusvDense-zeroR' : { τ : LTyp } { a b : LinRepDense τ } →  {{b ≡ zerovDense τ}} → plusvDense τ a b ≡ a
    plusvDense-zeroL' : { τ : LTyp } { a b : LinRepDense τ } →  {{a ≡ zerovDense τ}} → plusvDense τ a b ≡ b
    plusvDense-comm : (τ : LTyp) -> (a : LinRepDense τ) -> (b : LinRepDense τ) -> plusvDense τ a b ≡ plusvDense τ b a
    plusvDense-assoc : (τ : LTyp) → (a : LinRepDense τ) → (b : LinRepDense τ) (c : LinRepDense τ)
              →  plusvDense τ (plusvDense τ a b) c ≡ plusvDense τ a (plusvDense τ b c)
    plusvDense-congR : { τ : LTyp } -> { a b c : LinRepDense τ } → b ≡ c → plusvDense τ a b ≡ plusvDense τ a c
    plusvDense-congL : { τ : LTyp } -> { a b c : LinRepDense τ } → a ≡ c → plusvDense τ a b ≡ plusvDense τ c b

    -- relation between sparse and dense plus
    zerov-equiv-zerovDense : ( τ : LTyp ) 
                        → sparse2dense {τ} (zerov τ .fst) ≡ zerovDense τ

    plusv-equiv-plusvDense : {τ : LTyp}
                            → (x : LinRep τ) (y : LinRep τ)
                            → (Compatible-LinReps x y)
                            →  sparse2dense (plusv τ x y .fst)
                             ≡ plusvDense τ (sparse2dense x) (sparse2dense y)
    -- ==================
    -- Proofs for: primitive operations on floats
    -- ==================
    primFloatPlus-zeroL x = trans (primFloatPlus-comm 0.0 x) (primFloatPlus-zeroR x) 

    -- ==================
    -- Proofs for: sparse plus
    -- ==================
    plusvSparse-zeroR LUn v = refl
    plusvSparse-zeroR LR v = primFloatPlus-zeroR v
    plusvSparse-zeroR (σ :*! τ) (just x) = refl
    plusvSparse-zeroR (σ :*! τ) nothing = refl
    plusvSparse-zeroR (σ :+! τ) v = refl

    plusvSparse-zeroL LUn v = refl
    plusvSparse-zeroL LR v = primFloatPlus-zeroL v
    plusvSparse-zeroL (σ :*! τ) (just x) = refl
    plusvSparse-zeroL (σ :*! τ) nothing = refl
    plusvSparse-zeroL (σ :+! τ) (just x) = refl
    plusvSparse-zeroL (σ :+! τ) nothing = refl

    plusvSparse-comm LUn a b = refl
    plusvSparse-comm LR a b = primFloatPlus-comm a b
    plusvSparse-comm (σ :*! τ) (just (x1 , x2)) (just (y1 , y2)) = cong just (cong₂ _,_ (plusvSparse-comm σ x1 y1) (plusvSparse-comm τ x2 y2))
    plusvSparse-comm (σ :*! τ) (just x) nothing = refl
    plusvSparse-comm (σ :*! τ) nothing (just y) = refl
    plusvSparse-comm (σ :*! τ) nothing nothing = refl
    plusvSparse-comm (σ :+! τ) (just (inj₁ x)) (just (inj₁ y)) = cong (just ∘ inj₁) (plusvSparse-comm σ x y)
    plusvSparse-comm (σ :+! τ) (just (inj₁ x)) (just (inj₂ y)) = refl
    plusvSparse-comm (σ :+! τ) (just (inj₂ x)) (just (inj₁ y)) = refl
    plusvSparse-comm (σ :+! τ) (just (inj₂ x)) (just (inj₂ y)) = cong (just ∘ inj₂) (plusvSparse-comm τ x y)
    plusvSparse-comm (σ :+! τ) (just x) nothing = refl
    plusvSparse-comm (σ :+! τ) nothing (just y) = refl
    plusvSparse-comm (σ :+! τ) nothing nothing = refl

    -- ==================
    -- Proofs for: dense plus
    -- ==================
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

    -- ==================
    -- Proofs for: relation between sparse and dense plus
    -- ==================
    zerov-equiv-zerovDense LUn = refl
    zerov-equiv-zerovDense LR = refl
    zerov-equiv-zerovDense (σ :*! τ) = refl
    zerov-equiv-zerovDense (σ :+! τ) = refl

    plusv-equiv-plusvDense {LUn} x y _ = refl
    plusv-equiv-plusvDense {LR} x y _ = refl
    plusv-equiv-plusvDense {σ :*! τ} (just x) (just y) w = cong₂ _,_ (plusv-equiv-plusvDense (x .fst) (y .fst) (w .fst)) (plusv-equiv-plusvDense (x .snd) (y .snd) (w .snd))
    plusv-equiv-plusvDense {σ :*! τ} (just x) nothing _ = cong₂ _,_ (sym plusvDense-zeroR') (sym plusvDense-zeroR') 
    plusv-equiv-plusvDense {σ :*! τ} nothing (just y) _ = cong₂ _,_ (sym plusvDense-zeroL') (sym plusvDense-zeroL')
    plusv-equiv-plusvDense {σ :*! τ} nothing nothing _ = cong₂ _,_ (sym plusvDense-zeroL') (sym plusvDense-zeroL')
    plusv-equiv-plusvDense {σ :+! τ} (just (inj₁ x)) (just (inj₁ y)) w = cong₂ _,_ (plusv-equiv-plusvDense x y w) (sym plusvDense-zeroL')
    plusv-equiv-plusvDense {σ :+! τ} (just (inj₁ x)) (just (inj₂ y)) () -- Absurd case
    plusv-equiv-plusvDense {σ :+! τ} (just (inj₂ x)) (just (inj₁ y)) () -- Absurd case
    plusv-equiv-plusvDense {σ :+! τ} (just (inj₂ x)) (just (inj₂ y)) w = cong₂ _,_ (sym plusvDense-zeroL') (plusv-equiv-plusvDense x y w)
    plusv-equiv-plusvDense {σ :+! τ} (just x) nothing _ = cong₂ _,_ (sym plusvDense-zeroR') (sym plusvDense-zeroR')
    plusv-equiv-plusvDense {σ :+! τ} nothing (just y) _ = cong₂ _,_ (sym plusvDense-zeroL') (sym plusvDense-zeroL')
    plusv-equiv-plusvDense {σ :+! τ} nothing nothing _ = cong₂ _,_ (sym plusvDense-zeroL') (sym plusvDense-zeroL')
open plusv-lemmas public


ev+congR : {Γ : LEnv} {x : EV Γ} {y : EV Γ} {z : EV Γ}
            → y ≡ z → x ev+ y ≡ x ev+ z
ev+congL : {Γ : LEnv} {x : EV Γ} {y : EV Γ} {z : EV Γ}
            → x ≡ z → x ev+ y ≡ z ev+ y
ev+zeroR : {Γ : LEnv} → (a : EV Γ) → a ev+ (zero-EV Γ) ≡ a
ev+zeroL : {Γ : LEnv} → (a : EV Γ) → (zero-EV Γ) ev+ a ≡ a
ev+zeroL' : {Γ : LEnv} {a : EV Γ} → {b : EV Γ} → a ≡ zero-EV Γ  → a ev+ b ≡ b
ev+zeroR' : {Γ : LEnv} {a : EV Γ} {b : EV Γ} → b ≡ zero-EV Γ  → a ev+ b ≡ a
ev+comm : {Γ : LEnv} → (a : EV Γ) → (b : EV Γ) → a ev+ b ≡ b ev+ a
ev+assoc : {Γ : LEnv} → (a : EV Γ) → (b : EV Γ) → (c : EV Γ)
            → (a ev+ b) ev+ c ≡ a ev+ (b ev+ c)

-- Relation of EV to other constructs
Etup-equiv-EV : {Γ : Env Pr} → LinRepDense (D2τ' (Etup Pr Γ)) ≡ EV (map D2τ' Γ)
Etup-zerovDense-equiv-zero-EV : {τ : Env Pr} → Etup2EV (zerovDense (D2τ' (Etup Pr τ))) ≡ zero-EV (map D2τ' τ)
plusvDense-equiv-ev+ : {Γ : Env Pr} → ( x : LinRepDense (D2τ' (Etup Pr Γ)) ) → ( y : LinRepDense (D2τ' (Etup Pr Γ)) )
                    → Etup2EV (plusvDense (D2τ' (Etup Pr Γ)) x y)
                        ≡ Etup2EV x ev+ Etup2EV y

ev+congR w = cong₂ _ev+_ refl w
ev+congL w = cong₂ _ev+_ w refl

ev+zeroR {[]} x = refl
ev+zeroR {τ ∷ Γ} (x , xs) = cong₂ (_,_) (plusvDense-zeroR τ x) (ev+zeroR xs) 
ev+zeroL {Γ} x = trans (ev+comm (zero-EV Γ) x) (ev+zeroR x)  
ev+zeroR' {Γ} {a} {b} w = trans (ev+congR w) (ev+zeroR a)
ev+zeroL' {Γ} {a} {b} w = trans (ev+congL w) (ev+zeroL b)

ev+comm {[]} a b = refl 
ev+comm {τ ∷ Γ} a b = cong₂ (_,_) (plusvDense-comm τ (a .fst) (b .fst)) (ev+comm (a .snd) (b .snd)) 

ev+assoc {[]} a b c = refl
ev+assoc {τ ∷ Γ} a b c = cong₂ (_,_) (plusvDense-assoc τ (a .fst) (b .fst) (c .fst)) (ev+assoc (a .snd) (b .snd) (c .snd))

Etup-equiv-EV {[]} = refl
Etup-equiv-EV {x ∷ Γ} = cong₂ _×_ refl Etup-equiv-EV

Etup-zerovDense-equiv-zero-EV {[]} = refl
Etup-zerovDense-equiv-zero-EV {x ∷ τ} = cong₂ _,_ refl Etup-zerovDense-equiv-zero-EV

plusvDense-equiv-ev+ {[]} x y = refl
plusvDense-equiv-ev+ {τ ∷ Γ} x y = cong₂ _,_ refl (plusvDense-equiv-ev+ (x .snd) (y .snd))