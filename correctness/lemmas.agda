{-# OPTIONS --allow-unsolved-metas #-}
module correctness.lemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Float using (Float; primFloatPlus; primNatToFloat)

open import Data.Integer using (ℤ; _+_)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_$_; _∘_; id; case_of_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; cong-app)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import spec
open import correctness.spec
open import correctness.dsem
import spec.LACM as LACM
open LACM using (LACM)
open import chad-preserves-primal
open import eval-sink-commute


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
    onehot-equiv-addLEτ-lemma : {Γ : Env Pr} {τ : Typ Pr}
        → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
        in (ctg : LinRep (D2τ' τ))
        → (evIn : LEtup (map D2τ' Γ) )
        → (idx , ctg) ≃₄ evIn
        → LEtup2EV (addLEτ idx' ctg evIn)
          ≡ (Etup2EV (onehot idx (sparse2dense ctg)) ev+ LEtup2EV evIn)
    onehot-equiv-addLEτ-lemma {τ ∷ Γ}  Z      ctg (x , xs) w = cong₂ _,_ (plusv-equiv-plusvDense ctg x w) (sym (ev+zeroL' Etup-zerovDense-equiv-zero-EV))
    onehot-equiv-addLEτ-lemma {τ ∷ Γ} (S idx) ctg (x , xs) w = cong₂ _,_ (sym plusvDense-zeroL') (onehot-equiv-addLEτ-lemma idx ctg xs w)

    DSemᵀ-lemma-ctg-zero' : {σ τ : Typ Pr} { f : Rep σ  →  Rep τ } { a : Rep σ }
                    { ctg : LinRepDense (D2τ' τ) }
                    → {{ ctg ≡ zerovDense (D2τ' τ) }}
            → DSemᵀ {σ} {τ} f a ctg ≡ zerovDense (D2τ' σ)
    DSemᵀ-lemma-ctg-zero' {f = f} {a = a} {{ refl }} = DSemᵀ-ctg-zero f a

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

    DSemᵀ-lemma-pair : {Γ : Env Pr} {τ1 τ2 : Typ Pr}
            → let σ  = Etup Pr Γ 
            in (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → (a : Rep σ)
            → (ctg-f : LinRepDense (D2τ' τ1))
            → (ctg-g : LinRepDense (D2τ' τ2))
            → let dsem-f = DSemᵀ {σ} {τ1} f a ctg-f
                  dsem-g = DSemᵀ {σ} {τ2} g a ctg-g
                  h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
                  ctg : LinRepDense (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
              in Etup2EV dsem-f ev+ Etup2EV dsem-g
                 ≡ Etup2EV (DSemᵀ {σ} {τ1 :* τ2} h a ctg)
    DSemᵀ-lemma-pair f g a ctg-f ctg-g = sym $ trans (cong Etup2EV (DSemᵀ-pair f g a ctg-f ctg-g))
                                                (plusvDense-equiv-ev+ (DSemᵀ f a ctg-f) (DSemᵀ g a ctg-g))

    -- TODO: Betere naam verzinnen, dit zou de naam moeten zijn van een Lemma die zegt dat fst linear is
    DSemᵀ-lemma-fst : {Γ : Env Pr} {τ1 τ2 : Typ Pr}
            → let σ  = Etup Pr Γ 
            in (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → (a : Rep σ)
            → (ctg-f : LinRepDense (D2τ' τ1))
            → let ctg-g = sparse2dense (zerov (D2τ' τ2) .fst)
                  ctg : LinRepDense (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
                  h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
              in DSemᵀ {σ} {τ1 :* τ2} h a ctg 
                 ≡ DSemᵀ {σ} {τ1} f a ctg-f
    DSemᵀ-lemma-fst {Γ} {τ1} {τ2} f g a ctg-f =
      let ctg-g = (sparse2dense (zerov (D2τ' τ2) .fst))
      in trans (DSemᵀ-pair f g a ctg-f ctg-g) (plusvDense-zeroR' {{DSemᵀ-lemma-ctg-zero' {{zerov-equiv-zerovDense (D2τ' τ2)}}}})

    DSemᵀ-lemma-snd : {Γ : Env Pr} {τ1 τ2 : Typ Pr}
            → let σ  = Etup Pr Γ 
            in (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → (a : Rep σ)
            → (ctg-g : LinRepDense (D2τ' τ2))
            → let ctg-f = sparse2dense (zerov (D2τ' τ1) .fst)
                  ctg : LinRepDense (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
                  h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
              in DSemᵀ {σ} {τ1 :* τ2} h a ctg 
                 ≡ DSemᵀ {σ} {τ2} g a ctg-g
    DSemᵀ-lemma-snd {Γ} {τ1} {τ2} f g a ctg-g = 
      let ctg-f = (sparse2dense (zerov (D2τ' τ1) .fst))
      in trans (DSemᵀ-pair f g a ctg-f ctg-g) (plusvDense-zeroL' {{DSemᵀ-lemma-ctg-zero' {{zerov-equiv-zerovDense (D2τ' τ1)}}}}) 
    

    DSemᵀ-lemma-interp-let : {Γ : Env Pr} {σ τ : Typ Pr}
      → (a : Rep (Etup Pr Γ))
      → (ctg : LinRepDense (D2τ' τ))
      → (rhs : Term Pr Γ σ)
      → (body : Term Pr (σ ∷ Γ) τ)
      → let a' = (interp rhs (Etup-to-val a)) , a
            dsem-body = DSemᵀ {σ = σ :* (Etup Pr Γ)} {τ = τ} (interp body ∘ Etup-to-val) a' ctg
            dsem-rhs = DSemᵀ {σ = Etup Pr Γ } {τ = σ} (interp rhs ∘ Etup-to-val) a (Etup2EV dsem-body .fst)
        in (Etup2EV dsem-rhs ev+ Etup2EV dsem-body .snd)
           ≡ Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = τ} (interp (let' rhs body) ∘ Etup-to-val) a ctg)
    DSemᵀ-lemma-interp-let {Γ} {σ} {τ} a ctg rhs body =
      let -- Expressions used for applying the chain rule
          f : (env : Rep (Etup Pr (σ ∷ Γ))) → Rep τ
          f = interp body ∘ Etup-to-val
          g : (env : Rep (Etup Pr Γ)) → Rep σ × Rep (Etup Pr Γ) -- Note that g constructs a pair, thus we can use the pair rule of DSem on it
          g = (λ env → (interp rhs (Etup-to-val env) , env))

          dsem-body = DSemᵀ {σ = σ :* (Etup Pr Γ)} {τ = τ} f (g a) ctg
          dsem-rhs = DSemᵀ {σ = Etup Pr Γ } {τ = σ} (fst ∘ g) a (Etup2EV dsem-body .fst)
      in begin
      Etup2EV dsem-rhs ev+ Etup2EV dsem-body .snd
        ≡⟨ ev+congR (sym (cong Etup2EV (DSemᵀ-identity a (dsem-body .snd)))) ⟩
      Etup2EV dsem-rhs ev+ Etup2EV (DSemᵀ id a (dsem-body .snd))
        ≡⟨ DSemᵀ-lemma-pair (interp rhs ∘ Etup-to-val) id a (dsem-body .fst) (dsem-body .snd) ⟩
      Etup2EV ((DSemᵀ {σ = Etup Pr Γ} {τ = σ :* Etup Pr Γ} g a ∘ DSemᵀ {σ = σ :* Etup Pr Γ} {τ = τ} f (g a)) ctg)
        ≡⟨ cong Etup2EV (sym (DSemᵀ-chain f g a ctg)) ⟩
      Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = τ} (f ∘ g) a ctg)
        ≡⟨⟩
      Etup2EV (DSemᵀ {σ = Etup Pr Γ} {τ = τ} (interp (let' rhs body) ∘ Etup-to-val) a ctg)
      ∎

    DSemᵀ-lemma-inj₁ : {σ τ ρ : Typ Pr}
            → (f : Rep σ →  Rep τ) → (a : Rep σ)
            → (ctgL : LinRepDense (D2τ' τ)) → (ctgR : LinRepDense (D2τ' ρ))
            → DSemᵀ {σ} {τ} f a ctgL
              ≡ DSemᵀ {σ} {τ :+ ρ} (inj₁ ∘ f) a ( ctgL , ctgR ) 
    DSemᵀ-lemma-inj₁ {σ} {τ} {ρ} f a ctgL ctgR =
      begin
      DSemᵀ f a ctgL
        ≡⟨ cong (DSemᵀ f a) (sym (DSemᵀ-inj₁ (f a) (ctgL , ctgR))) ⟩
      DSemᵀ f a (DSemᵀ inj₁ (f a) (ctgL , ctgR))
        ≡⟨ sym (DSemᵀ-chain inj₁ f a (ctgL , ctgR)) ⟩
      DSemᵀ {σ} {τ :+ ρ} (inj₁ ∘ f) a (ctgL , ctgR)
      ∎

    DSemᵀ-lemma-inj₂ : {σ τ ρ : Typ Pr}
            → (f : Rep σ →  Rep τ) → (a : Rep σ)
            → (ctgL : LinRepDense (D2τ' ρ)) → (ctgR : LinRepDense (D2τ' τ))
            → DSemᵀ {σ} {τ} f a ctgR
              ≡ DSemᵀ {σ} {ρ :+ τ} (inj₂ ∘ f) a ( ctgL , ctgR ) 
    DSemᵀ-lemma-inj₂ {σ} {τ} {ρ} f a ctgL ctgR =
      begin
      DSemᵀ f a ctgR
        ≡⟨ cong (DSemᵀ f a) (sym (DSemᵀ-inj₂ (f a) (ctgL , ctgR))) ⟩
      DSemᵀ f a (DSemᵀ inj₂ (f a) (ctgL , ctgR))
        ≡⟨ sym (DSemᵀ-chain inj₂ f a (ctgL , ctgR)) ⟩
      DSemᵀ {σ} {ρ :+ τ} (inj₂ ∘ f) a (ctgL , ctgR)
      ∎

    fst-case : {A B : Set} {σ τ : Typ Pr}
            → (x : Rep (σ :+ τ))
            → (a₁ : Rep σ → A) (a₂ : Rep τ → A)
            → (b₁ : Rep σ → B) (b₂ : Rep τ → B)
            → let f : (Rep (σ :+ τ)) → A × B
                  f = λ where (inj₁ z) → (a₁ z , b₁ z)
                              (inj₂ z) → (a₂ z , b₂ z)
                      
                  g : (Rep (σ :+ τ)) → A
                  g = λ where (inj₁ z) → a₁ z
                              (inj₂ z) → a₂ z
              in fst (f x) ≡ g x
    fst-case (inj₁ x) a₁ a₂ b₁ b₂ = refl
    fst-case (inj₂ y) a₁ a₂ b₁ b₂ = refl

    -- DSemᵀ-lemma-chain-app : {τ1 τ2 τ3 : Typ Pr}
    --             → (f : Rep τ2 → Rep τ3)
    --             → (g : Rep τ1 → Rep τ2)
    --             → (a : Rep τ1)
    --             → (ctg : LinRepDense (D2τ' τ3))
    --             → DSemᵀ {τ1} {τ3} (λ a' → f (g a')) a ctg
    --               ≡ DSemᵀ {τ1} {τ2} g a (DSemᵀ {τ2} {τ3} f (g a) ctg)
    -- DSemᵀ-lemma-chain-app {τ1} {τ2} {τ3} f g a ctg = cong-app (DSemᵀ-chain {τ1} {τ2} {τ3} f g a) ctg

    -- DSemᵀ-lemma-interp-case : {Γ : Env Pr} {σ τ ρ : Typ Pr}
    --   → (a : Rep (Etup Pr Γ))
    --   → (ctg : LinRepDense (D2τ' ρ))
    --   → (e : Term Pr Γ (σ :+ τ))
    --   → (l : Term Pr (σ ∷ Γ) ρ)
    --   → (r : Term Pr (τ ∷ Γ) ρ)
    --   → (x : Rep σ)
    --   → let dsem-l = DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a) ctg
    --         dsem-e = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (dsem-l .fst , zerovDense (D2τ' τ))
    --     in Etup2EV dsem-e ev+ Etup2EV (dsem-l .snd)
    --        ≡ Etup2EV (DSemᵀ (interp (case' e l r) ∘ Etup-to-val) a ctg)
    -- DSemᵀ-lemma-interp-case {Γ} {σ} {τ} {ρ} a ctg e l r x =
    --   let dsem-l = DSemᵀ {σ :* Etup Pr Γ} {ρ} (interp l ∘ Etup-to-val) (x , a) ctg
    --       dsem-e = DSemᵀ {Etup Pr Γ} {σ :+ τ} (interp e ∘ Etup-to-val) a (dsem-l .fst , zerovDense (D2τ' τ))
    --       dsem-g₁ = DSemᵀ {Etup Pr Γ} {(σ :+ τ)} ? a ?
    --       dsem-g₂ = DSemᵀ {Etup Pr Γ} {Etup Pr Γ} ? a ?
    --   in begin
    --   Etup2EV dsem-e ev+ Etup2EV (dsem-l .snd)
    --   ≡⟨ {!   !} ⟩
    --   -- ?
    --   -- -- Etup2EV (DSemᵀ {Etup Pr Γ} {(σ :+ τ) :* (Etup Pr Γ)} g a
    --   -- --           (match-inj ((σ :+ τ) :* (Etup Pr Γ)) ρ 
    --   -- --               ?
    --   -- --               ?
    --   -- --               (g a)
    --   -- --           ))
    --   -- ≡⟨ cong Etup2EV {!   !} ⟩
    --   -- Etup2EV (DSemᵀ {Etup Pr Γ} {(σ :+ τ) :* (Etup Pr Γ)} g a (DSemᵀ {(σ :+ τ) :* (Etup Pr Γ)} {ρ} f (g a) ctg))
    --   -- ≡⟨ cong Etup2EV (sym (DSemᵀ-lemma-chain-app f g a ctg)) ⟩
    --   -- Etup2EV (DSemᵀ (f ∘ g) a ctg)
    --   -- ≡⟨ cong Etup2EV (DSemᵀ-extensionality {Etup Pr Γ} {ρ} (f ∘ g) (interp (case' e l r) ∘ Etup-to-val) a ctg w) ⟩
    --   Etup2EV (DSemᵀ (?) a ctg)
    --   ≡⟨ {!   !} ⟩
    --   Etup2EV (DSemᵀ (interp (case' e l r) ∘ Etup-to-val) a ctg)
    --   ∎
    --   where f : Rep ((σ :+ τ) :* (Etup Pr Γ)) → Rep ρ
    --         f = λ (zs , a) → match-inj σ τ 
    --                           (λ z → interp l (Etup-to-val (z , a))) 
    --                           (λ z → interp r (Etup-to-val (z , a)))
    --                           zs
    --         g : Rep (Etup Pr Γ) → Rep ((σ :+ τ) :* (Etup Pr Γ)) 
    --         g = λ a → ( interp e (Etup-to-val a) , a)
    --         w : (y : Rep (Etup Pr Γ)) → (f ∘ g) y ≡ interp (case' e l r) (Etup-to-val y) -- TODO: extract this lemma
    --         w y with interp e (Etup-to-val y)
    --         ... | inj₁ _ = refl
    --         ... | inj₂ _ = refl
                                 

open dsem-lemmas public

module sparse-LTyp-harmony-lemmas where
    ≃₁-zerov : ( τ : Typ Pr ) →  ( x : Rep τ )  → zerov (D2τ' τ) .fst ≃₁ x
    ≃₁-zerov Un _ = tt
    ≃₁-zerov Inte _ = tt
    ≃₁-zerov R _ = tt
    ≃₁-zerov ( σ :* τ ) _ = tt
    ≃₁-zerov ( σ :+ τ ) _ = tt

    ≃₁-inj₁ : ( σ τ : Typ Pr ) 
        → ( x : LinRep (D2τ' σ)) (y : Rep σ)
        → (x ≃₁ y) → _≃₁_ {σ :+ τ} (just (inj₁ x)) (inj₁ y)
    ≃₁-inj₁ Un _ _ _ _ = tt
    ≃₁-inj₁ Inte _ _ _ _ = tt
    ≃₁-inj₁ R _ _ _ _ = tt
    ≃₁-inj₁ ( _ :* _ ) _ _ _ w = w
    ≃₁-inj₁ ( _ :+ _ ) _ _ _ w = w

    ≃₁-transL : ( τ : Typ Pr ) → ( x : LinRep (D2τ' τ) ) → ( y : LinRep (D2τ' τ) ) → ( z : Rep τ )
            → x ≡ y → x ≃₁ z → y ≃₁ z
    ≃₁-transL τ x y z refl w2 = w2

    ≃₁-transR : ( τ : Typ Pr ) → ( x : LinRep (D2τ' τ) ) → ( y : Rep τ ) → ( z : Rep τ )
            → y ≡ z → x ≃₁ y → x ≃₁ z
    ≃₁-transR τ x y z refl w = w

    ≃₂-transL : {Γ : Env Pr} {τ : Typ Pr} 
            → ( x : LEtup (map D2τ' Γ) ) → ( y : LEtup (map D2τ' Γ) ) → ( z : Val Pr Γ )
            → x ≡ y → x ≃₂ z → y ≃₂ z
    ≃₂-transL {[]}    {τ} _ _ _ _    _ = tt
    ≃₂-transL {σ ∷ Γ} {τ} _ _ _ refl w = w

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

    ≃₂-intro-zero : {Γ : Env Pr} {τ : Typ Pr}
                → (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ) (x : Rep τ)
                → evIn ≃₂ val
                → (zerov (D2τ' τ) .fst , evIn) ≃₂ push x val
    ≃₂-intro-zero {Γ} {Un}     _ _ _ w = w
    ≃₂-intro-zero {Γ} {Inte}   _ _ _ w = w
    ≃₂-intro-zero {Γ} {R}      _ _ _ w = w
    ≃₂-intro-zero {Γ} {σ :* τ} _ _ _ w = tt , w
    ≃₂-intro-zero {Γ} {σ :+ τ} _ _ _ w = tt , w
    

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

module interp-sink where
    interp-sink-commute : ∀ {tag} {Γ Γ' : Env tag} {τ : Typ tag}
                    -> (env : Val tag Γ) (env2 : Val tag Γ')
                    -> (w : Weakening Γ Γ')
                    -> sinks-to w env env2
                    -> (e : Term tag Γ τ)
                    -> interp e env ≡ interp (sink w e) env2
    interp-sink-commute env env2 w s e = cong fst (eval-sink-commute env env2 w s e)

    -- Lemma using interp-sink-commute on a weakening of Copy-Skip-End
    -- This ends up being used for the let' and case' constructors.
    interp-sink-commute-Copy-Skip-End : ∀ {tag} {Γ : Env tag} {σ τ ρ : Typ tag} {y : Rep ρ}
                                → (x : Rep σ)
                                → (env : Val tag Γ)
                                → (t : Term tag (σ ∷ Γ) τ )
                                → let env' : Val tag (σ ∷ ρ ∷ Γ)
                                      env' = push x (push y env)
                                  in interp (sink (WCopy (WSkip WEnd)) t) env'
                                    ≡ interp t (push x env)
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
                                  in interp (sink (WCopy (WCopy WCut)) t) env1
                                     ≡ interp t env2
    interp-sink-commute-Copy-Copy-Cut x y env t =
      let env1 = push x (push y env)
          env2 = push x (push y empty)
      in sym (interp-sink-commute env2 env1 (WCopy (WCopy WCut)) (refl , refl , tt) t)
open interp-sink public

module simplify-exec-chad where
  interp-zerot-equiv-zerov : {Γ : Env Du} { env : Val Du Γ }
                              → (τ : Typ Pr)
                              → interp (zerot τ) env ≡ zerov (D2τ' τ) .fst
  interp-zerot-equiv-zerov Un = refl
  interp-zerot-equiv-zerov Inte = refl
  interp-zerot-equiv-zerov R = refl
  interp-zerot-equiv-zerov (σ :* τ) = refl
  interp-zerot-equiv-zerov (σ :+ τ) = refl 

  simplify-exec-chad-fst : {Γ : Env Pr} {σ τ : Typ Pr} 
      → (val : Val Pr Γ)
        (evIn : LEtup (map D2τ' Γ) )
        (ctg : LinRep (D2τ' σ))
        (t : Term Pr Γ (σ :* τ))
      → LACMexec (interp (chad (fst' t)) (primalVal val) .snd ctg .fst ) evIn
        ≡ LACMexec (interp (chad t) (primalVal val) .snd (just (ctg , zerov (D2τ' τ) .fst)) .fst) evIn
  simplify-exec-chad-fst {Γ} {σ} {τ} val evIn ctg t 
    using ρ ← D1τ (σ :* τ) :* (D2τ (σ :* τ) :-> D2Γ Γ)
    using val2 ← (push {Du} {ρ ∷ []} {Lin (D2τ' σ)} ctg (push {Du} {[]} {ρ} (interp (chad t) (primalVal val))  empty))
    rewrite interp-zerot-equiv-zerov {Lin (D2τ' σ) ∷ ρ ∷ []} {val2} τ
    = refl

  simplify-exec-chad-snd : {Γ : Env Pr} {σ τ : Typ Pr} 
      → (val : Val Pr Γ)
        (evIn : LEtup (map D2τ' Γ) )
        (ctg : LinRep (D2τ' τ))
        (t : Term Pr Γ (σ :* τ))
      → LACMexec (interp (chad (snd' t)) (primalVal val) .snd ctg .fst ) evIn
        ≡ LACMexec (interp (chad t) (primalVal val) .snd (just (zerov (D2τ' σ) .fst , ctg)) .fst) evIn
  simplify-exec-chad-snd {Γ} {σ} {τ} val evIn ctg t 
    using ρ ← D1τ (σ :* τ) :* (D2τ (σ :* τ) :-> D2Γ Γ)
    using val2 ← (push {Du} {ρ ∷ []} {Lin (D2τ' τ)} ctg (push {Du} {[]} {ρ} (interp (chad t) (primalVal val))  empty))
    rewrite interp-zerot-equiv-zerov {Lin (D2τ' τ) ∷ ρ ∷ []} {val2} σ
    = refl

  simplify-exec-chad-let : {Γ : Env Pr} {τ σ : Typ Pr} 
      → (a : Rep (Etup Pr Γ))
        (evIn : LEtup (map D2τ' Γ) )
        (ctg : LinRep (D2τ' τ))
      → (rhs : Term Pr Γ σ)
        (body : Term Pr (σ ∷ Γ) τ)
      → let val' = Etup-to-val-primal ((interp rhs (Etup-to-val a)) , a)
            body' = interp (chad body) val' .snd ctg .fst
            ev-body = LACMexec body' (zerov (D2τ' σ) .fst , evIn)
        in LACMexec (interp (chad (let' rhs body)) (Etup-to-val-primal a) .snd ctg .fst ) evIn
           ≡ LACMexec (interp (chad rhs) (Etup-to-val-primal a) .snd (ev-body .fst) .fst) (ev-body .snd)
  simplify-exec-chad-let {Γ} {τ} {σ} a evIn ctg rhs body
    using val ← Etup-to-val a
    using ρ1 ← D1τ σ :* (D2τ σ :-> D2Γ Γ)
    using ρ2 ← D1τ τ :* (D2τ τ :-> D2Γ (σ ∷ Γ))
    using ρ3 ← Lin (D2τ' τ)
    rewrite chad-preserves-primal val rhs
    rewrite interp-sink-commute-Copy-Skip-End {ρ = ρ1} {y = interp (chad rhs) (primalVal val)} (primal σ (interp rhs val)) (primalVal val) (chad body)
    using val-verbose ← 
      (push {Du} {ρ2 ∷ ρ1 ∷ []} {ρ3} ctg
      (push {Du} {ρ1 ∷ []} {ρ2} (interp (chad body) (push (primal σ (interp rhs val)) (primalVal val)))
      (push {Du} {[]} {ρ1} (interp (chad rhs) (primalVal val)) empty)))
    rewrite interp-zerot-equiv-zerov {ρ3 ∷ ρ2 ∷ ρ1 ∷ []} {val-verbose} σ
    using m1 ← λ x → ( snd (interp (chad rhs) (primalVal val)) (fst x) .fst , ℤ.pos 5 Data.Integer.+ snd (interp (chad rhs) (primalVal val)) (fst x) .snd )
    using m2 ← (interp (chad body) (push (primal σ (interp rhs val)) (primalVal val)) .snd ctg .fst)
    using elim-bind ← LACM.run-bind (LACM.scope (zerov (D2τ' σ) .fst) m2) m1 evIn .fst
    rewrite elim-bind
    using (_ , elim-scope-snd , elim-scope-fst) ← LACMexec-scope m2 ((zerov (D2τ' σ) .fst)) evIn
    rewrite elim-scope-fst
    rewrite elim-scope-snd
    = refl

  simplify-exec-chad-let-val : {Γ : Env Pr} {τ σ : Typ Pr} 
      → (val : Val Pr Γ)
        (evIn : LEtup (map D2τ' Γ) )
        (ctg : LinRep (D2τ' τ))
      → (rhs : Term Pr Γ σ)
        (body : Term Pr (σ ∷ Γ) τ)
      → let val' = primalVal (push (interp rhs val) val)
            body' = interp (chad body) val' .snd ctg .fst
            ev-body = LACMexec body' (zerov (D2τ' σ) .fst , evIn)
        in LACMexec (interp (chad (let' rhs body)) (primalVal val) .snd ctg .fst ) evIn
            ≡ LACMexec (interp (chad rhs) (primalVal val) .snd (ev-body .fst) .fst) (ev-body .snd)
  simplify-exec-chad-let-val {Γ} {τ} {σ} val evIn ctg rhs body
    using ρ1 ← D1τ σ :* (D2τ σ :-> D2Γ Γ)
    using ρ2 ← D1τ τ :* (D2τ τ :-> D2Γ (σ ∷ Γ))
    using ρ3 ← Lin (D2τ' τ)
    rewrite chad-preserves-primal val rhs
    rewrite interp-sink-commute-Copy-Skip-End {ρ = ρ1} {y = interp (chad rhs) (primalVal val)} (primal σ (interp rhs val)) (primalVal val) (chad body)
    using val-verbose ← 
      (push {Du} {ρ2 ∷ ρ1 ∷ []} {ρ3} ctg
      (push {Du} {ρ1 ∷ []} {ρ2} (interp (chad body) (push (primal σ (interp rhs val)) (primalVal val)))
      (push {Du} {[]} {ρ1} (interp (chad rhs) (primalVal val)) empty)))
    rewrite interp-zerot-equiv-zerov {ρ3 ∷ ρ2 ∷ ρ1 ∷ []} {val-verbose} σ
    using m1 ← λ x → ( snd (interp (chad rhs) (primalVal val)) (fst x) .fst , ℤ.pos 5 Data.Integer.+ snd (interp (chad rhs) (primalVal val)) (fst x) .snd )
    using m2 ← (interp (chad body) (push (primal σ (interp rhs val)) (primalVal val)) .snd ctg .fst)
    using elim-bind ← LACM.run-bind (LACM.scope (zerov (D2τ' σ) .fst) m2) m1 evIn .fst
    rewrite elim-bind
    using (_ , elim-scope-snd , elim-scope-fst) ← LACMexec-scope m2 ((zerov (D2τ' σ) .fst)) evIn
    rewrite elim-scope-fst
    rewrite elim-scope-snd
    = refl
    
  simplify-exec-chad-primop : {Γ : Env Pr} {σ τ : Typ Pr} 
      → (val : Val Pr Γ)
        (evIn : LEtup (map D2τ' Γ) )
        (ctg : LinRep (D2τ' τ))
        (t : Term Pr Γ σ)
        (op : Primop Pr σ τ )
      → let ctg-op = (interp (dprim' op) (push ctg (push (primal σ (interp t val)) empty)))
        in LACMexec (interp (chad (prim op t)) (primalVal val) .snd ctg .fst ) evIn
           ≡ LACMexec (interp (chad t) (primalVal val) .snd ctg-op .fst) evIn
  simplify-exec-chad-primop {Γ} {σ} {τ} val evIn ctg t op 
    using val-ignore ← push {Du} {(D1τ σ :* (D2τ σ :-> D2Γ Γ)) ∷ []} {Lin (D2τ' τ)} ctg (push {Du} {[]} {D1τ σ :* (D2τ σ :-> D2Γ Γ)} (interp (chad t) (primalVal val)) empty)
    rewrite chad-preserves-primal val t
    rewrite interp-sink-commute-Copy-Copy-Cut ctg (primal σ (interp t val)) val-ignore (dprim' op)
    = refl

  -- This lemma is used to simplify LACMexec of a case' after having done:
  -- 1. a rewrite using: rewrite chad-preserves-primal val e
  -- 2. a with and case distinction on: interp e val
  -- Then, you can use this lemma, for example with a rewrite
  -- the argument f should be either inj₁ or inj₂, depending on the case distinction
  simplify-exec-chad-case : {Γ : Env Pr} {σ τ ρ π : Typ Pr} 
      → (val : Val Pr Γ)
        (evIn : LEtup (map D2τ' Γ) )
        (ctg : LinRep (D2τ' ρ))
        (e : Term Pr Γ (σ :+ τ))
        (t : Term Pr (π ∷ Γ) ρ)
        (x : Rep π)
        (f : LinRep (D2τ' π) → LinRep (D2τ' σ) ⊎ LinRep (D2τ' τ)  )
      → let τ1 = D1τ (σ :+ τ) :* (D2τ (σ :+ τ) :-> D2Γ Γ)
            τ2 = D1τ ρ :* (D2τ ρ :-> D2Γ (π ∷ Γ))
            zerot-π = (interp
                        (zerot π)
                          (push {Du} {τ2 ∷ τ1 ∷ []} {Lin (D2τ' ρ)}
                            ctg
                            (push {Du} {τ1 ∷ []} {τ2}
                              (interp 
                                (sink (WCopy (WSkip WEnd)) (chad t))
                                (push {Du} {τ1 ∷ map D1τ Γ} {D1τ π} (primal π x) (push {Du} {map D1τ Γ} {τ1} (interp {τ = τ1} (chad e) (primalVal val)) (primalVal val)))
                              )
                              (push {Du} {[]} {τ1} (interp (chad e) (primalVal val)) empty)
                            )
                          )
                      )
            m2 = ( (interp
                      (sink (WCopy (WSkip WEnd)) (chad t))
                      (push {Du} {τ1 ∷ map D1τ Γ} {D1τ π} (primal π x) (push {Du} {map D1τ Γ} {τ1} (interp (chad e) (primalVal val)) (primalVal val)))
                    ) .snd ctg .fst
                 )
            m3 = (λ y → ( interp (chad e) (primalVal val) .snd (just (f (fst y))) .fst )
                         , (ℤ.pos 6 Data.Integer.+ (interp (chad e) (primalVal val)) .snd (just (f (fst y))) .snd)
                 )
            t' = LACMexec (interp (chad t) (push (primal π x) (primalVal val)) .snd ctg .fst) (zerov (D2τ' π) .fst , evIn)
        in LACMexec (LACM.bind (LACM.scope zerot-π m2) m3) evIn
           ≡ LACMexec (interp (chad e) (primalVal val) .snd (just (f (t' .fst))) .fst) (t' .snd)
  simplify-exec-chad-case {Γ} {σ} {τ} {ρ} {π} val evIn ctg e t x f
    rewrite interp-sink-commute-Copy-Skip-End {ρ = D1τ (σ :+ τ) :* (D2τ (σ :+ τ) :-> D2Γ Γ)} {y = (interp (chad e) (primalVal val))} (primal π x) (primalVal val) (chad t)
    using τ1 ← D1τ (σ :+ τ) :* (D2τ (σ :+ τ) :-> D2Γ Γ)
    using τ2 ← D1τ ρ :* (D2τ ρ :-> D2Γ (π ∷ Γ))
    using val2 ← push {Du} {τ2 ∷ τ1 ∷ []} {Lin (D2τ' ρ)} ctg (push {Du} {τ1 ∷ []} {τ2} (interp  (chad t) (push (primal π x) (primalVal val)) ) (push {Du} {[]} {τ1} (interp (chad e) (primalVal val) ) empty) )
    rewrite interp-zerot-equiv-zerov {Lin (D2τ' ρ) ∷ τ2 ∷ τ1 ∷ []} {val2} π
    using m1 ← λ y → ( interp (chad e) (primalVal val) .snd (just (f (y .fst))) .fst , ℤ.pos 6 Data.Integer.+ interp (chad e) (primalVal val) .snd (just (f (y .fst))) .snd )
    using m2 ← interp (chad t) (push (primal π x) (primalVal val)) .snd ctg .fst
    using elim-bind ← LACM.run-bind (LACM.scope (zerov (D2τ' π) .fst) m2) m1 evIn .fst
    rewrite elim-bind
    using (_ , elim-scope-snd , elim-scope-fst) ← LACMexec-scope m2 ((zerov (D2τ' π) .fst)) evIn
    rewrite elim-scope-fst
    rewrite elim-scope-snd
    = refl
       
open simplify-exec-chad public 