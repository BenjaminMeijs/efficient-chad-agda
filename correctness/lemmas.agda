module correctness.lemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Float using (Float; primFloatPlus; primNatToFloat)

open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)

open import spec
open import correctness.spec
open import correctness.dsem
import spec.LACM as LACM
open LACM using (LACM)


module plusv-lemmas where
    -- Floats
    postulate
        primFloatPlus-comm : (x : Float) → (y : Float) → primFloatPlus x y ≡ primFloatPlus y x
        primFloatPlus-zeroR : (x : Float) → primFloatPlus x (primNatToFloat 0) ≡ x
        primFloatPlus-assoc : (x : Float) → (y : Float) → (z : Float)
                              → primFloatPlus (primFloatPlus x y) z ≡ primFloatPlus x (primFloatPlus y z)

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
                            → (x ≃₃ y)
                            →  sparse2dense (plusv τ x y .fst)
                             ≡ plusvDense τ (sparse2dense x) (sparse2dense y)
    -- ==================
    -- Proofs for: sparse plus
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

module environment-vector-lemmas where
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

    Etup-equiv-EV : {Γ : Env Pr} → LinRepDense (D2τ' (Etup Pr Γ)) ≡ EV (map D2τ' Γ)
    Etup-zerovDense-equiv-zero-EV : {τ : Env Pr} → Etup2EV (zerovDense (D2τ' (Etup Pr τ))) ≡ zero-EV (map D2τ' τ)

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

open environment-vector-lemmas public


module LACM-exec-lemmas where
    private
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

open LACM-exec-lemmas public

module dsem-lemmas where 
    DSemᵀ-lemma-ctg-zero' : {σ τ : Typ Pr} { f : Rep σ  →  Rep τ } { a : Rep σ }
            → DSemᵀ {σ} {τ} f a (zerovDense (D2τ' τ)) ≡ zerovDense (D2τ' σ)
    DSemᵀ-lemma-ctg-zero' {f = f} {a = a} = DSemᵀ-ctg-zero f a

    DSemᵀ-lemma-ctg-zeroLEnv : {Γ : Env Pr} {τ : Typ Pr}
                    → let σ = Etup Pr Γ in
                    ( f : Rep σ  →  Rep τ ) 
                    ( a : Rep σ ) 
                    ( ctg : LinRepDense (D2τ' τ) )
                    → ( ctg ≡ zerovDense (D2τ' τ))
                    → Etup2EV (DSemᵀ {σ} {τ} f a ctg) ≡ zero-EV (map D2τ' Γ)
    DSemᵀ-lemma-ctg-zeroLEnv {σ} {τ} f a ctg w = trans (cong (Etup2EV ∘ (DSemᵀ f a)) w)
                                                   (trans (cong Etup2EV DSemᵀ-lemma-ctg-zero') 
                                                          Etup-zerovDense-equiv-zero-EV) 

    DSemᵀ-lemma-ctg-zeroLEnv' : {Γ : Env Pr} {τ : Typ Pr}
                    → let σ = Etup Pr Γ
                    in { f : Rep σ  →  Rep τ } 
                       { a : Rep σ } 
                       { ctg : LinRepDense (D2τ' τ) }
                    →  {{ ctg ≡ zerovDense (D2τ' τ) }}
                    → Etup2EV (DSemᵀ {σ} {τ} f a ctg) ≡ zero-EV (map D2τ' Γ) 
    DSemᵀ-lemma-ctg-zeroLEnv' {σ} {τ} {f} {a} {ctg} {{w}} = DSemᵀ-lemma-ctg-zeroLEnv f a ctg w

open dsem-lemmas public

module sparse-LTyp-harmony-lemmas where
    ≃₁-zerov : ( τ : Typ Pr ) →  ( x : Rep τ )  → zerov (D2τ' τ) .fst ≃₁ x
    ≃₁-zerov Un _ = tt
    ≃₁-zerov Inte _ = tt
    ≃₁-zerov R _ = tt
    ≃₁-zerov ( σ :* τ ) _ = tt
    ≃₁-zerov ( σ :+ τ ) _ = tt

    ≃₁-transL : {τ : Typ Pr} → { x : LinRep (D2τ' τ) } → { y : LinRep (D2τ' τ) } → { z : Rep τ }
            → x ≡ y → x ≃₁ z → y ≃₁ z
    ≃₁-transL {Un} {x} {y} {z} x≡y w = tt
    ≃₁-transL {Inte} {x} {y} {z} x≡y w = tt
    ≃₁-transL {R} {x} {y} {z} x≡y w = tt
    ≃₁-transL {σ :* τ} {just (x1 , x2)} {just (y1 , y2)} {z1 , z2} refl (w1 , w2) = w1 , w2
    ≃₁-transL {σ :* τ} {nothing} {nothing} {y1 , y2} x≡y w = tt
    ≃₁-transL {σ :+ τ} {just x} {y} {inj₁ z} refl w = w
    ≃₁-transL {σ :+ τ} {just x} {y} {inj₂ z} refl w = w
    ≃₁-transL {σ :+ τ} {nothing} {y} {inj₁ z} refl w = tt
    ≃₁-transL {σ :+ τ} {nothing} {y} {inj₂ z} refl w = tt

    -- ≃₂-transL : {Γ : Env Pr} → ( x : LEtup (map D2τ' Γ) ) → ( y : LEtup (map D2τ' Γ) ) → ( z : Val Pr Γ )
    --         → x ≡ y → x ≃₂ z → y ≃₂ z
    -- ≃₂-transL {[]} x y z x≡y w = tt
    -- ≃₂-transL {τ ∷ Γ} x y z refl w = w

    ≃₂-fst : {Γ' : Env Pr} {τ : Typ Pr} 
        → let Γ = τ ∷ Γ' in ( x : LEtup (map D2τ' Γ) )
        → (y : Rep τ ) ( ys : Val Pr Γ' )
        → (x ≃₂ push y ys) → fst x ≃₁ y
    ≃₂-fst {Γ} {Un} (x , xs) y ys w = tt
    ≃₂-fst {Γ} {Inte} (x , xs) y ys w = tt
    ≃₂-fst {Γ} {R} (x , xs) y ys w = tt
    ≃₂-fst {Γ} {σ :* τ} (x , xs) y ys w = w .fst
    ≃₂-fst {Γ} {σ :+ τ} (x , xs) y ys w = w .fst

    ≃₂-snd : {Γ' : Env Pr} {τ : Typ Pr} 
        → let Γ = τ ∷ Γ' in ( x : LEtup (map D2τ' Γ) )
        → (y : Rep τ ) ( ys : Val Pr Γ' )
        → (x ≃₂ push y ys) → snd x ≃₂ ys
    ≃₂-snd {Γ} {Un} (x , xs) y ys w = w
    ≃₂-snd {Γ} {Inte} (x , xs) y ys w = w
    ≃₂-snd {Γ} {R} (x , xs) y ys w = w
    ≃₂-snd {Γ} {σ :* τ} (x , xs) y ys w = w .snd
    ≃₂-snd {Γ} {σ :+ τ} (x , xs) y ys w = w .snd

    x≃₁z-and-y≃₁z-implies-x≃₃y : {τ : Typ Pr}
        → (x : LinRep (D2τ' τ)) (y : LinRep (D2τ' τ)) (z : Rep τ)
        → (x ≃₁ z) → (y ≃₁ z) → (x ≃₃ y)
    x≃₁z-and-y≃₁z-implies-x≃₃y {Un} x y z w1 w2 = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {Inte} x y z w1 w2 = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {R} x y z w1 w2 = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :* τ} (just (x , xs)) (just (y , ys)) (z , zs) w1 w2
        = x≃₁z-and-y≃₁z-implies-x≃₃y x y z (w1 .fst) (w2 .fst) , x≃₁z-and-y≃₁z-implies-x≃₃y xs ys zs (w1 .snd) (w2 .snd)
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :* τ} (just _) nothing (_ , _) _ _ = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :* τ} nothing (just _) (_ , _) _ _ = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :* τ} nothing nothing (_ , _) _ _ = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :+ τ} (just (inj₁ x)) (just (inj₁ y)) (inj₁ z) w1 w2
        = x≃₁z-and-y≃₁z-implies-x≃₃y x y z w1 w2
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :+ τ} (just (inj₂ x)) (just (inj₂ y)) (inj₂ z) w1 w2
        = x≃₁z-and-y≃₁z-implies-x≃₃y x y z w1 w2
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :+ τ} (just (inj₁ _)) nothing (inj₁ z) _ _ = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :+ τ} (just (inj₂ _)) nothing (inj₂ _) _ _ = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :+ τ} nothing (just _) (inj₁ _) _ _ = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :+ τ} nothing (just _) (inj₂ _) _ _ = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :+ τ} nothing nothing (inj₁ _) _ _ = tt
    x≃₁z-and-y≃₁z-implies-x≃₃y {σ :+ τ} nothing nothing (inj₂ _) _ _ = tt

    ≃₁-and-≃₂-implies-≃₄ : {Γ : Env Pr} {τ : Typ Pr}
        → (idx : Idx Γ τ) (ctg : LinRep (D2τ' τ)) (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ)
        → (ctg ≃₁ valprj val idx) → (evIn ≃₂ val)
        → (idx , ctg) ≃₄ evIn
    ≃₁-and-≃₂-implies-≃₄ Z ctg (x , xs) (push y ys) w1 w2
        = x≃₁z-and-y≃₁z-implies-x≃₃y ctg x y w1 (≃₂-fst (x , xs) y ys w2)
    ≃₁-and-≃₂-implies-≃₄ (S idx) ctg (x , xs) (push y ys) w1 w2
        = ≃₁-and-≃₂-implies-≃₄ idx ctg xs ys w1 (≃₂-snd (x , xs) y ys w2)

    ≃₁-and-≃₂-implies-≃₅ : {Γ : Env Pr} {τ : Typ Pr}
        → (idx : Idx Γ τ) (ctg : LinRep (D2τ' τ)) (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ)
        → (ctg ≃₁ valprj val idx) → (evIn ≃₂ val)
        → (idx , ctg) ≃₅ val
    ≃₁-and-≃₂-implies-≃₅ Z ctg (x , xs) (push y ys) w1 w2
        = w1
    ≃₁-and-≃₂-implies-≃₅ (S idx) ctg (x , xs) (push y ys) w1 w2
        = ≃₁-and-≃₂-implies-≃₅ idx ctg xs ys w1 (≃₂-snd (x , xs) y ys w2)
    
    
    plusv-preserves-≃₁ : {τ : Typ Pr}
        → (x : LinRep (D2τ' τ)) (y : LinRep (D2τ' τ)) (z : Rep τ)
        → (x ≃₃ y) → (x ≃₁ z) → (y ≃₁ z)
        → fst (plusv (D2τ' τ) x y) ≃₁ z
    plusv-preserves-≃₁ {Un} _ _ _ _ _ _ = tt
    plusv-preserves-≃₁ {Inte} _ _ _ _ _ _ = tt
    plusv-preserves-≃₁ {R} _ _ _ _ _ _ = tt
    plusv-preserves-≃₁ {σ :* τ} (just x) (just x₁) z w1 w2 w3
        = plusv-preserves-≃₁ (x .fst) (x₁ .fst) (z .fst) (w1 .fst) (w2 .fst) (w3 .fst) , plusv-preserves-≃₁ (x .snd) (x₁ .snd) (z .snd) (w1 .snd) (w2 .snd) (w3 .snd)
    plusv-preserves-≃₁ {σ :* τ} (just (x , xs)) nothing (z , zs) tt w2 w3 = w2 .fst , w2 .snd
    plusv-preserves-≃₁ {σ :* τ} nothing (just (y , ys)) (z , zs) w1 w2 w3 = w3 .fst , w3 .snd
    plusv-preserves-≃₁ {σ :* τ} nothing nothing _ _ _ _ = tt
    plusv-preserves-≃₁ {σ :+ τ} (just (inj₁ x)) (just (inj₁ x₁)) (inj₁ x₂) w1 w2 w3 = plusv-preserves-≃₁ x x₁ x₂ w1 w2 w3
    plusv-preserves-≃₁ {σ :+ τ} (just (inj₂ y₁)) (just (inj₂ y₂)) (inj₂ y) w1 w2 w3 = plusv-preserves-≃₁ y₁ y₂ y w1 w2 w3
    plusv-preserves-≃₁ {σ :+ τ} (just _) nothing (inj₁ x₁) w1 w2 w3 = w2
    plusv-preserves-≃₁ {σ :+ τ} (just _) nothing (inj₂ y) w1 w2 w3 = w2
    plusv-preserves-≃₁ {σ :+ τ} nothing (just _) (inj₁ _) w1 w2 w3 = w3
    plusv-preserves-≃₁ {σ :+ τ} nothing (just _) (inj₂ _) w1 w2 w3 = w3
    plusv-preserves-≃₁ {σ :+ τ} nothing nothing (inj₁ _) w1 w2 w3 = tt
    plusv-preserves-≃₁ {σ :+ τ} nothing nothing (inj₂ _) w1 w2 w3 = tt
    
    addLEτ-preserves-≃₂ : {Γ : Env Pr} {τ : Typ Pr}
                → (idx : Idx Γ τ) (ctg : LinRep (D2τ' τ)) (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ)
                → (evIn ≃₂ val) → ((idx , ctg) ≃₄ evIn) → ((idx , ctg) ≃₅ val)
                → addLEτ (convIdx D2τ' idx) ctg evIn ≃₂ val
    addLEτ-preserves-≃₂ {Un ∷ Γ} Z ctg (x , xs) (push y val) w _ _ = w
    addLEτ-preserves-≃₂ {Inte ∷ Γ} Z ctg (x , xs) (push y val) w _ _ = w
    addLEτ-preserves-≃₂ {R ∷ Γ} Z ctg (x , xs) (push y val) w _ _ = w
    addLEτ-preserves-≃₂ {(σ :* τ) ∷ Γ} Z ctg (x , xs) (push y val) w1 w2 w3 = plusv-preserves-≃₁ {σ :* τ} ctg x y w2 w3 (w1 .fst) , (w1 .snd)
    addLEτ-preserves-≃₂ {(σ :+ τ) ∷ Γ} Z ctg (x , xs) (push y val) w1 w2 w3 = plusv-preserves-≃₁ {σ :+ τ} ctg x y w2 w3 (w1 .fst) , (w1 .snd)
    addLEτ-preserves-≃₂ {Un ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = addLEτ-preserves-≃₂ idx ctg xs val w1 w2 w3 
    addLEτ-preserves-≃₂ {Inte ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = addLEτ-preserves-≃₂ idx ctg xs val w1 w2 w3 
    addLEτ-preserves-≃₂ {R ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = addLEτ-preserves-≃₂ idx ctg xs val w1 w2 w3 
    addLEτ-preserves-≃₂ {(σ :* τ) ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = w1 .fst , addLEτ-preserves-≃₂ idx ctg xs val (w1 .snd) w2 w3 
    addLEτ-preserves-≃₂ {(σ :+ τ) ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = w1 .fst , addLEτ-preserves-≃₂ idx ctg xs val (w1 .snd) w2 w3
open sparse-LTyp-harmony-lemmas public


module exec-chad-lemmas where

module todo-misc where
    interp-zerot-equiv-zerov : {Γ : Env Du} {env : Val Du Γ}
                                → (τ : Typ Pr)
                                → interp (zerot τ) env ≡ zerov (D2τ' τ) .fst
    interp-zerot-equiv-zerov Un = refl
    interp-zerot-equiv-zerov Inte = refl
    interp-zerot-equiv-zerov R = refl
    interp-zerot-equiv-zerov (σ :* τ) = refl
    interp-zerot-equiv-zerov (σ :+ τ) = refl 
