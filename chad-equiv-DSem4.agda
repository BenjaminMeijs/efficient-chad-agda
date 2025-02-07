module chad-equiv-DSem4 where
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Maybe
open import Agda.Builtin.Float
open import Data.List using (List; []; _∷_; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (uncurry)
open import Function.Base using (id; _∘_; _$_; case_of_; flip)
open import Data.Fin as Fin
open import Data.Empty
open import Data.Integer using (ℤ)
import Data.Integer as Integer
open import Data.Product using (_×_)
open import Level using (Level)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import utility4
-- open import giga-chad using (D1Term ; giga-chad)
open import chad-preserves-primal using (chad-preserves-primal)
open import spec hiding (eval)
import spec as S
import spec.LACM as LACM
import utility as U
open LACM using (LACM)

postulate
    -- ======================
    -- Definition
    -- ======================
    DSem4 :  {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep (D1τ σ)) 
            → (ctg : LinRepDense (D2τ' τ))
            → LinRepDense (D2τ' σ)

    DSem5 :  {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep σ) 
            → (ctg : LinRepDense (D2τ' τ))
            → LinRepDense (D2τ' σ)

    -- ======================
    -- Misc. rules
    -- ======================
    DSem5-ctg-zero : {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep σ)
            → (ctg : LinRepDense (D2τ' τ)) 
            → ctg ≡ zerovDense (D2τ' τ)
            → DSem5 {σ} {τ} f a ctg ≡ zerovDense (D2τ' σ)

    DSem5-chain : {τ1 τ2 τ3 : Typ Pr}
                → (f : Rep τ2 → Rep τ3)
                → (g : Rep τ1 → Rep τ2)
                → (a : Rep τ1)
                → DSem5 {τ1} {τ3} (f ∘ g) a
                  ≡ DSem5 {τ1} {τ2} g a ∘ DSem5 {τ2} {τ3} f (g a)

    DSem5-pair : {σ τ1 τ2 : Typ Pr}
            → (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → (a : Rep σ)
            → (ctg-f : LinRepDense (D2τ' τ1))
            → (ctg-g : LinRepDense (D2τ' τ2))
            → let dsem-f = DSem5 {σ} {τ1} f a ctg-f
                  dsem-g = DSem5 {σ} {τ2} g a ctg-g
                  h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
                  ctg : LinRepDense (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
              in DSem5 {σ} {τ1 :* τ2} h a ctg
                 ≡ plusvDense (D2τ' σ) dsem-f dsem-g

    DSem5-var : {Γ : Env Pr} {τ : Typ Pr}
              → let σ = Etup Pr Γ
              in (a : Rep σ)
              → (idx : Idx Γ τ)
              → (ctg : LinRepDense (D2τ' τ))
              → DSem5 {σ} {τ} (flip valprj idx ∘ Etup-to-val) a ctg
                ≡ onehot idx ctg

    -- ======================
    -- DSem on linear functions (Derivative of a linear function f is f)
    -- ======================
    DSem5-identity : {τ : Typ Pr} 
            → (a : Rep τ)
            → (ctg : LinRepDense (D2τ' τ)) 
            → DSem5 {τ} {τ} id a ctg ≡ ctg

    DSem5-inj₁ : {σ τ : Typ Pr}
            → (a : Rep σ)
            → DSem5 {σ} {σ :+ τ} inj₁ a
              ≡ fst

    DSem5-inj₂ : {σ τ : Typ Pr}
            → (a : Rep σ)
            → DSem5 {σ} {τ :+ σ} inj₂ a
              ≡ snd

    -- ======================
    -- (primitive) Operations on Floats
    -- ======================
    DSem5-prim-floatPlus : let  σ : Typ Pr ; σ = (R :* R) ; τ : Typ Pr ; τ = R 
            in (a : Rep σ)
            → (ctg : LinRepDense (D2τ' τ))
            → let (x , y) = a
              in DSem5 {σ} {τ} (uncurry primFloatPlus) (x , y) ctg
              ≡ (ctg , ctg)

    DSem5-prim-floatTimes : let  σ : Typ Pr ; σ = (R :* R) ; τ : Typ Pr ; τ = R 
            in (a : Rep σ)
            → (ctg : LinRepDense (D2τ' τ))
            → let (x , y) = a
              in DSem5 {σ} {τ} (uncurry primFloatTimes) (x , y) ctg
              ≡ (primFloatTimes ctg y , primFloatTimes ctg x)

    DSem5-prim-floatNegate : let  σ : Typ Pr ; σ = R ; τ : Typ Pr ; τ = R 
            in (a : Rep σ) 
            → (ctg : LinRepDense (D2τ' τ))
            → DSem5 {σ} {τ} primFloatNegate a ctg
              ≡ primFloatNegate ctg

DSem5-ctg-zero' : {σ τ : Typ Pr} → { f : Rep σ  →  Rep τ } → { a : Rep σ } → { ctg : LinRepDense (D2τ' τ) } → {{ctg ≡ zerovDense (D2τ' τ)}} → DSem5 {σ} {τ} f a ctg ≡ zerovDense (D2τ' σ)
DSem5-ctg-zero' {σ} {τ} {f} {a} {ctg} {{w}} = DSem5-ctg-zero f a ctg w

DSem5-ctg-zeroLEnv : {Γ : Env Pr} {τ : Typ Pr}
                  → let σ = Etup Pr Γ in
                  ( f : Rep σ  →  Rep τ ) 
                  ( a : Rep σ ) 
                  → etup2EV (DSem5 {σ} {τ} f a (zerovDense (D2τ' τ))) ≡ (zero-LEnvDense Γ)
DSem5-ctg-zeroLEnv {σ} {τ} f a = trans (cong etup2EV DSem5-ctg-zero') zerovDense-on-Etup-is-zeroLEnv2

DSem5-ctg-zeroLEnv' : {Γ : Env Pr} {τ : Typ Pr}
                  → let σ = Etup Pr Γ in { f : Rep σ  →  Rep τ } 
                  → { a : Rep σ } → { ctg : LinRepDense (D2τ' τ) } 
                  → {{ w : ctg ≡ zerovDense (D2τ' τ) }} 
                  → etup2EV (DSem5 {σ} {τ} f a ctg) ≡ (zero-LEnvDense Γ)
DSem5-ctg-zeroLEnv' {σ} {τ} {f} {a} {ctg} {{w}} = trans (cong etup2EV (cong (DSem5 f a) w)) (DSem5-ctg-zeroLEnv {σ} {τ} f a)


DSem5-chain-app : {τ1 τ2 τ3 : Typ Pr}
            → (f : Rep τ2 → Rep τ3)
            → (g : Rep τ1 → Rep τ2)
            → (a : Rep τ1)
            → (ctg : LinRepDense (D2τ' τ3)) 
            → DSem5 {τ1} {τ3} (f ∘ g) a ctg
              ≡ (DSem5 {τ1} {τ2} g a ∘ DSem5 {τ2} {τ3} f (g a)) ctg
DSem5-chain-app f g a ctg = cong-app (DSem5-chain f g a) ctg

DSem5-inj₁-lemma : {σ τ ρ : Typ Pr}
        → (f : Rep σ →  Rep τ) 
        → (a : Rep σ)
        → (ctgL : LinRepDense (D2τ' τ))
        → (ctgR : LinRepDense (D2τ' ρ))
        → let g : Rep σ → Rep τ ⊎ Rep ρ
              g = inj₁ ∘ f
          in DSem5 {σ} {τ} f a ctgL -- DSem f a ctg 
              ≡ DSem5 {σ} {τ :+ ρ} g a ( ctgL , ctgR ) 
DSem5-inj₁-lemma {σ} {τ} {ρ} f a ctgL ctgR =
  let ctg' = ctgL , ctgR
  in begin
  DSem5 f a ctgL
    ≡⟨ cong (DSem5 f a) (cong-app (sym (DSem5-inj₁ (f a))) ctg') ⟩
  DSem5 {σ} {τ} f a (DSem5 inj₁ (f a) ctg')
    ≡⟨ sym (DSem5-chain-app {σ} {τ} {τ :+ ρ} inj₁ f a ctg') ⟩
  DSem5 {σ} {τ :+ ρ} (inj₁ ∘ f) a ctg'
  ∎



onehot-equiv-addLEτ-lemma : {Γ : Env Pr} {τ : Typ Pr}
                    → (idx : Idx Γ τ) → let idx' = convIdx D2τ' idx
                    in (ctg : LinRep (D2τ' τ))
                    → (evIn : LEtup (map D2τ' Γ) )
                    → EVs2d (addLEτ idx' ctg evIn)
                      ≡ EVs2d evIn ev+ etup2EV (onehot idx (sparse2dense ctg))
onehot-equiv-addLEτ-lemma {σ ∷ Γ} {τ} Z       ctg (x , xs) = cong₂ _,_ {!   !} 
                                                (sym (ev+zeroR' zerovDense-on-Etup-is-zeroLEnv2))
onehot-equiv-addLEτ-lemma {σ ∷ Γ} {τ} (S idx) ctg (x , xs) = cong₂ _,_ (sym plusvDense-zeroR') (onehot-equiv-addLEτ-lemma idx ctg xs)

evalprim-equiv-DSem : {σ τ : Typ Pr}
                      → (x : Rep σ)
                      → (ctg : LinRep (D2τ' τ))
                      → (op : Primop Pr σ τ )
                      → sparse2dense (interp (push ctg (push (primal σ x) empty)) (dprim' op))
                        ≡ DSem5 (evalprim op) x (sparse2dense ctg)
evalprim-equiv-DSem (x , y) ctg ADD = sym (DSem5-prim-floatPlus (x , y) ctg) 
evalprim-equiv-DSem (x , y) ctg MUL = sym (DSem5-prim-floatTimes (x , y) ctg) 
evalprim-equiv-DSem {σ} {τ} x ctg NEG = sym (DSem5-prim-floatNegate x ctg) 
evalprim-equiv-DSem tt ctg (LIT x) = refl
evalprim-equiv-DSem x ctg IADD = cong₂ _,_ refl refl 
evalprim-equiv-DSem x ctg IMUL = cong₂ _,_ refl refl 
evalprim-equiv-DSem x tt INEG = refl
evalprim-equiv-DSem x ctg SIGN = sym DSem5-ctg-zero'


chad-equiv-DSem5 : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep σ)
                  (evIn : LEtup LΓ )
                  (ctg : LinRep (D2τ' τ))
                  (t : Term Pr Γ τ)
                → EVs2d {LΓ} (LACMexec (interp (Etup-to-val-primal a) (chad t) .snd ctg .fst ) evIn)
                  ≡ EVs2d {LΓ} evIn ev+ etup2EV {Γ} (DSem5 {σ} {τ}  (flip interp t ∘ Etup-to-val) a (sparse2dense {D2τ' τ} ctg))
chad-equiv-DSem5 {Γ = Γ} a evIn ctg unit
  rewrite (LACMexec-pure tt evIn)
  rewrite (DSem5-ctg-zeroLEnv {Γ} {Un} (flip (interp {Γ = Γ}) unit ∘ Etup-to-val) a)
  rewrite (ev+zeroR {Γ} (EVs2d evIn))
  = refl
  -- begin
  -- EVs2d (LACMexec (interp (Etup-to-val-primal a) (chad unit) .snd ctg .fst) evIn)
  -- ≡⟨ cong EVs2d (LACMexec-pure tt evIn) ⟩
  -- EVs2d evIn
  -- ≡⟨ sym (ev+zeroR' DSem5-ctg-zeroLEnv') ⟩
  -- EVs2d evIn ev+ etup2EV (DSem5 (flip (interp {Γ = Γ}) unit ∘ Etup-to-val) a (sparse2dense {D2τ' Un} (snf ctg)))
  -- ∎
chad-equiv-DSem5 {Γ = Γ} a evIn nothing (pair {σ = σ} {τ = τ} l r) =
  let ctgL = _ ; ctgR = _
      m1 = interp (Etup-to-val-primal a) (chad l) .snd ctgL .fst
      m2 = interp (Etup-to-val-primal a) (chad r) .snd ctgR .fst
      ihr = trans (chad-equiv-DSem5 a (LACMexec m1 evIn) ctgR r)
                  (ev+zeroR' (DSem5-ctg-zeroLEnv' {{ w = zerov-is-zerovDense (D2τ' τ)}}))
      ihl = trans (chad-equiv-DSem5 a evIn ctgL l)
                  (ev+zeroR' (DSem5-ctg-zeroLEnv' {{ w = zerov-is-zerovDense (D2τ' σ) }}))
  in begin
  EVs2d (LACMexec (LACMsequence m1 m2) evIn)
  ≡⟨ cong EVs2d (LACMexec-sequence m1 m2 evIn) ⟩ EVs2d (LACMexec m2 (LACMexec m1 evIn))
  ≡⟨ ihr ⟩ EVs2d (LACMexec m1 evIn)
  ≡⟨ ihl ⟩ EVs2d evIn
  ≡⟨ sym (ev+zeroR' DSem5-ctg-zeroLEnv') ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp (pair l r) ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} nothing))
  ∎
chad-equiv-DSem5 {Γ = Γ} a evIn ctg@(just (ctgL , ctgR)) (pair {σ = σ} {τ = τ} l r) = 
  let ctgL = _ ; ctgR = _
      m1 = interp (Etup-to-val-primal a) (chad l) .snd ctgL .fst
      m2 = interp (Etup-to-val-primal a) (chad r) .snd ctgR .fst

      ihr = chad-equiv-DSem5 a (LACMexec m1 evIn) ctgR r
      ihl = chad-equiv-DSem5 a evIn ctgL l
  in begin
  EVs2d (LACMexec (LACMsequence m1 m2) evIn)
  ≡⟨ cong EVs2d (LACMexec-sequence m1 m2 evIn) ⟩
  EVs2d (LACMexec m2 (LACMexec m1 evIn))
  ≡⟨ ihr ⟩ EVs2d (LACMexec m1 evIn) ev+ etup2EV (DSem5 (flip interp r ∘ Etup-to-val) a (sparse2dense ctgR))
  ≡⟨ ev+congL ihl ⟩ (EVs2d evIn ev+ etup2EV (DSem5 (flip interp l ∘ Etup-to-val) a (sparse2dense ctgL))) ev+ etup2EV (DSem5 (flip interp r ∘ Etup-to-val) a (sparse2dense ctgR))
  ≡⟨ ev+assoc _ _ _ ⟩ EVs2d evIn ev+ (etup2EV (DSem5 (flip interp l ∘ Etup-to-val) a (sparse2dense ctgL)) ev+ etup2EV (DSem5 (flip interp r ∘ Etup-to-val) a (sparse2dense ctgR)))
  ≡⟨ ev+congR (evplus-on-Etup-is-plusv _ _) ⟩ EVs2d evIn ev+ (etup2EV $ plusvDense _ (DSem5 (flip interp l ∘ Etup-to-val) a (sparse2dense ctgL)) (DSem5 (flip interp r ∘ Etup-to-val) a (sparse2dense ctgR)))
  ≡⟨ ev+congR (cong etup2EV (sym $ DSem5-pair _ _ _ _ _)) ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp (pair l r) ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} (just (ctgL , ctgR))))
  ∎
chad-equiv-DSem5 {Γ = Γ} a evIn ctg (fst' {σ = σ} {τ = τ} t) =
  let zeroR = zerov (D2τ' _) .fst
      ctg' = just (ctg , zeroR)
      f =  flip interp (fst' t) ∘ Etup-to-val
      g =  flip interp (snd' t) ∘ Etup-to-val
      dsemL = DSem5 {Etup Pr Γ} {σ} f a (sparse2dense ctg)
      dsemR = DSem5 {Etup Pr Γ} {τ} g a (sparse2dense zeroR)
  in begin
  EVs2d (LACMexec (interp (Etup-to-val-primal a) (chad (fst' t)) .snd ctg .fst) evIn)
    ≡⟨ cong ( λ ▰ → EVs2d (LACMexec (interp (Etup-to-val-primal a) (chad t) .snd (just (ctg , ▰)) .fst) evIn) ) (interp-zerot≡zerov _) ⟩
  EVs2d (LACMexec (interp (Etup-to-val-primal a) (chad t) .snd ctg' .fst) evIn)
    ≡⟨ chad-equiv-DSem5 a evIn ctg' t ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} ctg'))
    ≡⟨ ev+congR (trans (cong etup2EV (DSem5-pair f g a (sparse2dense ctg) (sparse2dense zeroR))) (sym (evplus-on-Etup-is-plusv _ _))) ⟩
  EVs2d evIn ev+ (etup2EV dsemL ev+ etup2EV dsemR)
    ≡⟨ ev+congR (ev+zeroR' (DSem5-ctg-zeroLEnv' {{zerov-is-zerovDense (D2τ' τ)}})) ⟩
  EVs2d evIn ev+ etup2EV dsemL
  ∎
chad-equiv-DSem5 {Γ = Γ} a evIn ctg (var x) =
  let idx = convIdx D2τ' x
  in begin
  EVs2d (LACMexec (interp (Etup-to-val-primal a) (chad (var x)) .snd ctg .fst) evIn)
    ≡⟨ (cong EVs2d (LACMexec-add idx ctg evIn)) ⟩
  EVs2d (addLEτ idx ctg evIn)
    ≡⟨ onehot-equiv-addLEτ-lemma x ctg evIn ⟩
  EVs2d evIn ev+ etup2EV (onehot x (sparse2dense ctg))
    ≡⟨ ev+congR (sym (cong etup2EV (DSem5-var a x (sparse2dense ctg)))) ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip valprj x ∘ Etup-to-val) a (sparse2dense ctg))
    ≡⟨⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp (var x) ∘ Etup-to-val) a (sparse2dense ctg))
  ∎
chad-equiv-DSem5 {Γ = Γ} a evIn ctg (let' {σ = σ} {τ = τ} rhs body) =
  let -- Useful names just used for evaluating to a simpeler form
      val = Etup-to-val-primal a
      rhs-interp = interp val (chad rhs)
      body-interp-verbose = (interp (push (fst rhs-interp) (push rhs-interp val)) (sink (WCopy (WSkip WEnd)) (chad body)))
      body-interp-verbose2 = interp (push (fst rhs-interp) val) (chad body)
      body-interp = interp (push (primal σ (interp (Etup-to-val a) rhs)) val) (chad body)
      body-interp1equiv2 : body-interp-verbose2 ≡ body-interp
      body-interp1equiv2 = cong (λ ▰ → interp (push ▰ val) (chad body))  (chad-preserves-primal (Etup-to-val a) rhs)
      body-interp-equiv-verbose = interp-sink-commute-Copy-Skip-End (fst rhs-interp) (val) (chad body)
      zeroV-verbose = interp (push ctg (push body-interp-verbose (push rhs-interp empty))) (zerot σ)
      chad-t-verbose = snd body-interp-verbose ctg .fst
      m1 = λ x → ( snd rhs-interp (fst x) .fst , ℤ.pos 5 Data.Integer.+ snd rhs-interp (fst x) .snd )
      zeroV = zerov (D2τ' σ) .fst
      chad-t = body-interp .snd ctg .fst

      a2 : Rep σ × Rep (Etup Pr Γ)
      a2 = (interp (Etup-to-val a) rhs , a)
      (outval1 , _) , ev1 , _ = LACM.run (LACM.scope zeroV chad-t) evIn
      (outval2 , ev2) = LACMexec chad-t (zeroV , evIn)
      equiv-lemma = cong₂ (λ α β → EVs2d (LACMexec (m1 (α , tt) .fst) β))
      
      dsem-t = (DSem5 {σ :* Etup Pr Γ} {τ} (flip interp body ∘ Etup-to-val) a2 (sparse2dense ctg))
      (dsem-rhs , dsem-body) = dsem-t

      ih = chad-equiv-DSem5 a2 (zeroV , evIn) ctg body
                
      -- Expressions used for applying the chain rule
      chain-f : (env : Rep (Etup Pr (σ ∷ Γ))) → Rep τ
      chain-f = flip interp body ∘ Etup-to-val
      chain-g : (env : Rep (Etup Pr Γ)) → Rep σ × Rep (Etup Pr Γ) -- Note that chain-g constructs a pair, thus we can use the pair rule of DSem on it
      chain-g = (λ env → (interp (Etup-to-val env) rhs , env))

  in begin
  EVs2d ((LACMexec (LACM.bind (LACM.scope zeroV-verbose chad-t-verbose) m1) evIn))
    ≡⟨ cong EVs2d (cong₂ (λ α β → LACMexec (LACM.bind (LACM.scope α β) m1) evIn) (interp-zerot≡zerov σ) (cong (λ α → snd α ctg .fst) (trans body-interp-equiv-verbose body-interp1equiv2))) ⟩
  EVs2d ((LACMexec (LACM.bind (LACM.scope zeroV chad-t) m1) evIn))
    ≡⟨ cong EVs2d (LACM.run-bind (LACM.scope zeroV chad-t) m1 evIn .fst) ⟩
  EVs2d (LACMexec (m1 (outval1 , tt) .fst) ev1)
    ≡⟨ (let (_ , α , β) = (LACMexec-scope chad-t zeroV evIn) in equiv-lemma β α) ⟩
  EVs2d (LACMexec (m1 (outval2 , tt) .fst) ev2)
    ≡⟨⟩
  EVs2d (LACMexec (interp val (chad rhs) .snd outval2 .fst) ev2)
    ≡⟨ chad-equiv-DSem5 a ev2 outval2 rhs ⟩
  EVs2d ev2 ev+ etup2EV (DSem5 (flip interp rhs ∘ Etup-to-val) a (sparse2dense outval2))
    ≡⟨ cong₂ (λ α β → α ev+ etup2EV (DSem5 (flip interp rhs ∘ Etup-to-val) a β)) (cong snd ih) (trans (cong fst ih) (plusvDense-zeroL' {{zerov-is-zerovDense _}})) ⟩
  (EVs2d evIn ev+ etup2EV dsem-body) ev+ etup2EV (DSem5 (flip interp rhs ∘ Etup-to-val) a dsem-rhs)
    ≡⟨ ev+assoc _ _ _ ⟩
  EVs2d evIn ev+ (etup2EV dsem-body ev+ etup2EV (DSem5 (flip interp rhs ∘ Etup-to-val) a dsem-rhs))
    ≡⟨ ev+congR (evplus-on-Etup-is-plusv _ _) ⟩ 
  EVs2d evIn ev+ etup2EV (plusvDense (D2τ' (Etup Pr Γ)) dsem-body (DSem5 (flip interp rhs ∘ Etup-to-val) a dsem-rhs) )
    ≡⟨ ev+congR (cong etup2EV (plusvDense-congL (sym (DSem5-identity a dsem-body)))) ⟩
  EVs2d evIn ev+ etup2EV (plusvDense (D2τ' (Etup Pr Γ)) (DSem5 id a dsem-body) (DSem5 (flip interp rhs ∘ Etup-to-val) a dsem-rhs) )
    ≡⟨ ev+congR (cong etup2EV (plusvDense-comm (D2τ' (Etup Pr Γ)) _ _)) ⟩
  EVs2d evIn ev+ etup2EV (plusvDense (D2τ' (Etup Pr Γ)) (DSem5 (flip interp rhs ∘ Etup-to-val) a dsem-rhs) (DSem5 id a dsem-body))
    ≡⟨ ev+congR (cong etup2EV (sym (DSem5-pair (flip interp rhs ∘ Etup-to-val) id a dsem-rhs dsem-body))) ⟩
  EVs2d evIn ev+ etup2EV ((DSem5 chain-g a dsem-t))
    ≡⟨⟩
  EVs2d evIn ev+ etup2EV ((DSem5 chain-g a (DSem5 {σ :* Etup Pr Γ} {τ} chain-f a2 (sparse2dense {D2τ' τ} ctg))))
    ≡⟨⟩
  EVs2d evIn ev+ etup2EV ((DSem5 {Etup Pr Γ} {σ :* Etup Pr Γ} chain-g a ∘ DSem5 {σ :* Etup Pr Γ} {τ} chain-f (chain-g a) ) (sparse2dense {D2τ' τ} ctg))
    ≡⟨ ev+congR (cong etup2EV (sym (DSem5-chain-app chain-f chain-g a (sparse2dense {D2τ' τ} ctg)))) ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (chain-f ∘ chain-g) a (sparse2dense {D2τ' τ} ctg))
    ≡⟨⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp (let' rhs body) ∘ Etup-to-val) a (sparse2dense {D2τ' τ} ctg))
  ∎ 
chad-equiv-DSem5 {Γ = Γ} a evIn ctg (prim {σ = σ} {τ = τ} op t) =
  let val = Etup-to-val-primal a
      d-op-env-verbose1 = push ctg (push (fst (interp val (chad t))) (push ctg (push (interp val (chad t) ) empty)))
      d-op-verbose1 = interp d-op-env-verbose1 (sink (WCopy (WCopy WCut)) (dprim' op))
      d-op-env-verbose2 = push ctg (push (fst (interp val (chad t))) empty)
      d-op-verbose2 = interp d-op-env-verbose2 (dprim' op) 
      d-op-equiv-verbose = trans (interp-sink-commute-Copy-Copy-Cut ctg (fst (interp val (chad t))) (push ctg (push (interp val (chad t)) empty))  (dprim' op))
                                (cong (flip interp (dprim' op)) (cong (push ctg ∘ flip push empty) (chad-preserves-primal (Etup-to-val a) t)))

      d-op-env = push ctg (push (primal σ (interp (Etup-to-val a) t)) empty)
      d-op = interp d-op-env (dprim' op) 

  in begin
  EVs2d (LACMexec (interp val (chad t) .snd d-op-verbose1 .fst) evIn)
    ≡⟨ cong (λ ▰ → EVs2d (LACMexec (interp val (chad t) .snd ▰ .fst) evIn)) d-op-equiv-verbose ⟩
  EVs2d (LACMexec (interp val (chad t) .snd d-op .fst) evIn)
    ≡⟨ chad-equiv-DSem5 a evIn d-op t ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp t ∘ Etup-to-val) a (sparse2dense d-op))
    ≡⟨ ev+congR (cong etup2EV (cong (DSem5 _ a) (evalprim-equiv-DSem (interp (Etup-to-val a) t) ctg op))) ⟩
  EVs2d evIn ev+ etup2EV (DSem5 {Etup Pr Γ} {σ} (flip interp t ∘ Etup-to-val) a (DSem5 {σ} {τ} (evalprim op) (interp (Etup-to-val a) t) (sparse2dense ctg)))
    ≡⟨ ev+congR (cong etup2EV (sym (DSem5-chain-app (evalprim op) (flip interp t ∘ Etup-to-val) a (sparse2dense ctg)))) ⟩
  EVs2d evIn ev+ etup2EV (DSem5 {Etup Pr Γ} {τ} (evalprim op ∘ (flip interp t ∘ Etup-to-val)) a (sparse2dense ctg))
    ≡⟨⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp (prim op t) ∘ Etup-to-val) a (sparse2dense ctg))
  ∎
chad-equiv-DSem5 {Γ = Γ} a evIn nothing (inl {σ = σ} {τ = τ} t) =
  let zero-σ = zerov (D2τ' σ) .fst
  in begin
  EVs2d (LACMexec (interp (Etup-to-val-primal a) (chad t) .snd zero-σ .fst) evIn)
    ≡⟨ chad-equiv-DSem5 a evIn zero-σ t ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp t ∘ Etup-to-val) a (sparse2dense zero-σ))
    ≡⟨ ev+congR (DSem5-ctg-zeroLEnv' {{zerov-is-zerovDense (D2τ' σ)}}) ⟩
  EVs2d evIn ev+ zero-LEnvDense Γ
    ≡⟨ ev+congR (sym DSem5-ctg-zeroLEnv') ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (inj₁ ∘ flip interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :*! D2τ' τ} nothing))
  ∎
chad-equiv-DSem5 {Γ = Γ} a evIn ctg'@(just (inj₁ ctg)) (inl {σ = σ} {τ = τ} t) = 
  begin
  EVs2d (LACMexec (interp (Etup-to-val-primal a) (chad (inl t)) .snd ctg' .fst) evIn)
    ≡⟨⟩
  EVs2d (LACMexec (interp (Etup-to-val-primal a) (chad t) .snd ctg .fst) evIn)
    ≡⟨ chad-equiv-DSem5 a evIn ctg t ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp t ∘ Etup-to-val) a (sparse2dense ctg))
    ≡⟨ ev+congR (cong etup2EV (DSem5-inj₁-lemma (flip interp t ∘ Etup-to-val) a (sparse2dense ctg) (zerovDense (D2τ' τ)) )) ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (inj₁ ∘ flip interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :+! D2τ' τ} ctg'))
  ∎
chad-equiv-DSem5 {Γ = Γ} a evIn ctg'@(just (inj₂ ctg)) (inl {σ = σ} {τ = τ} t) = 
  let zero-σ = zerov (D2τ' σ) .fst
  in begin
  EVs2d (LACMexec (interp (Etup-to-val-primal a) (chad (inl t)) .snd (just (inj₂ ctg)) .fst) evIn)
    ≡⟨⟩
  EVs2d (LACMexec (interp (Etup-to-val-primal a) (chad t) .snd zero-σ .fst) evIn)
    ≡⟨ chad-equiv-DSem5 a evIn zero-σ t ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp t ∘ Etup-to-val) a (sparse2dense zero-σ))
    ≡⟨ ev+congR (DSem5-ctg-zeroLEnv' {{zerov-is-zerovDense (D2τ' σ)}}) ⟩
  EVs2d evIn ev+ zero-LEnvDense Γ
    ≡⟨ ev+congR (sym DSem5-ctg-zeroLEnv' ) ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (flip interp t ∘ Etup-to-val) a (zerovDense (D2τ' σ)))
    ≡⟨ ev+congR (cong etup2EV (DSem5-inj₁-lemma (flip interp t ∘ Etup-to-val) a (zerovDense (D2τ' σ)) (sparse2dense ctg))) ⟩
  EVs2d evIn ev+ etup2EV (DSem5 (inj₁ ∘ flip interp t ∘ Etup-to-val) a (zerovDense (D2τ' σ) , sparse2dense ctg))
    ≡⟨⟩
  EVs2d evIn ev+ etup2EV (DSem5 (inj₁ ∘ flip interp t ∘ Etup-to-val) a (sparse2dense {D2τ' σ :+! D2τ' τ} (just (inj₂ ctg))))
  ∎ 
chad-equiv-DSem5 {Γ = Γ} a evIn ctg t = {!   !} 