module chad-equiv-DSem4 where
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
import Data.Integer as Integer
open import Data.Product using (_×_)
open import Level using (Level)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import utility4
open import giga-chad using (D1Term)
open import spec hiding (eval)
import spec as S
import spec.LACM as LACM
import utility as U
open LACM using (LACM)

postulate
    DSem4 :  {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep (D1τ σ)) 
            → (ctg : LinRepDense (D2τ' τ))
            → LinRepDense (D2τ' σ)

    -- New DSem5 proposal
    -- Otherwise the chain rule can not be applied
    DSem5 :  {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep σ) 
            → (ctg : LinRepDense (D2τ' τ))
            → LinRepDense (D2τ' σ)

    DSem4-ctg-zero : {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep (D1τ σ))
            → (ctg : LinRepDense (D2τ' τ)) 
            → ctg ≡ zerovDense (D2τ' τ)
            → DSem4 {σ} {τ} f a ctg ≡ zerovDense (D2τ' σ)

    DSem4-pair : {σ τ1 τ2 : Typ Pr}
            → (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → (a : Rep (D1τ σ))
            → (ctg-f : LinRepDense (D2τ' τ1))
            → (ctg-g : LinRepDense (D2τ' τ2))
            → let dsem-f = DSem4 {σ} {τ1} f a ctg-f
                  dsem-g = DSem4 {σ} {τ2} g a ctg-g
                  h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
                  ctg : LinRepDense (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
              in DSem4 {σ} {τ1 :* τ2} h a ctg
                 ≡ plusvDense (D2τ' σ) dsem-f dsem-g
    
    DSem4-chain : {τ1 τ2 τ3 : Typ Pr}
                → (f : Rep τ2 → Rep τ3)
                → (g : Rep τ1 → Rep τ2)
                → (a : Rep τ1)
                → DSem4 {τ1} {τ3} (f ∘ g) (primal τ1 a)
                  ≡ DSem4 {τ1} {τ2} g (primal τ1 a) ∘ DSem4 {τ2} {τ3} f (primal τ2 (g a))

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

DSem5-ctg-zero' : {σ τ : Typ Pr} → { f : Rep σ  →  Rep τ } → { a : Rep σ } → { ctg : LinRepDense (D2τ' τ) } → {{ctg ≡ zerovDense (D2τ' τ)}} → DSem5 {σ} {τ} f a ctg ≡ zerovDense (D2τ' σ)
DSem5-ctg-zero' {σ} {τ} {f} {a} {ctg} {{w}} = DSem5-ctg-zero f a ctg w

DSem5-ctg-zeroLEnv' : {Γ : Env Pr} {τ : Typ Pr}
                  → let σ = Etup Pr Γ in { f : Rep σ  →  Rep τ } 
                  → { a : Rep σ } → { ctg : LinRepDense (D2τ' τ) } 
                  → {{ ctg ≡ zerovDense (D2τ' τ) }} 
                  → Etup-to-LEtupDense (DSem5 {σ} {τ} f a ctg) ≡ (zero-LEnvDense Γ)
DSem5-ctg-zeroLEnv' {σ} {τ} {f} {a} {ctg} {{w}} = trans (cong Etup-to-LEtupDense DSem5-ctg-zero') zerovDense-on-Etup-is-zeroLEnv2

DSem5-chain-app : {τ1 τ2 τ3 : Typ Pr}
            → (f : Rep τ2 → Rep τ3)
            → (g : Rep τ1 → Rep τ2)
            → (a : Rep τ1)
            → (ctg : LinRepDense (D2τ' τ3)) 
            → DSem5 {τ1} {τ3} (f ∘ g) a ctg
              ≡ (DSem5 {τ1} {τ2} g a ∘ DSem5 {τ2} {τ3} f (g a)) ctg
DSem5-chain-app f g a ctg = cong-app (DSem5-chain f g a) ctg

-- DSem5-chain-app : {τ1 τ2 τ3 : Typ Pr}
--             → (f : Rep τ2 → Rep τ3)
--             → (g : Rep τ1 → Rep τ2)
--             → (a : Rep τ1)
--             → (ctg : LinRepDense (D2τ' τ3)) 
--             → DSem5 {τ1} {τ3} (f ∘ g) a ctg
              -- ≡ (DSem5 {τ1} {τ2} g a (DSem5 {τ2} {τ3} f (g a) ctg)
              -- ≡ (DSem5 {τ1} {τ2} g a ∘ DSem5 {τ2} {τ3} f (g a)) ctg
-- DSem5-chain-app f g a ctg = cong-app (DSem5-chain f g a) ctg
LEtup-snf : {Γ : Env Pr} → let LΓ = map D2τ' Γ in LEtup LΓ → LEtup LΓ
LEtup-snf {[]} tt = tt
LEtup-snf {τ ∷ Γ} (x , xs) = sparse-normal-form x , LEtup-snf xs

-- chad-equiv-DSem6 : {Γ : Env Pr} {τ : Typ Pr} 
--                   → let σ  = Etup Pr Γ 
--                         LΓ = map D2τ' Γ in
--                   (a : Rep σ)
--                   (evIn : LEtup LΓ )
--                   (ctg : LinRepDense (D2τ' τ))
--                   (t : Term Pr Γ τ)
--                 → LEtup-to-LEtupDense {LΓ} (LACMexec (interp (Etup-to-val-primal a) (chad t) .snd (from-LinRepDense ctg) .fst ) evIn)
--                   ≡ LEtup-to-LEtupDense {LΓ} evIn ev+ Etup-to-LEtupDense {Γ} (DSem5 {σ} {τ}  (flip interp t ∘ Etup-to-val) a ctg)
-- chad-equiv-DSem6 {Γ = Γ} a evIn ctg unit =
--   begin
--   LEtup-to-LEtupDense (LACMexec (interp (Etup-to-val-primal a) (chad unit) .snd (from-LinRepDense ctg) .fst) evIn)
--   ≡⟨ cong LEtup-to-LEtupDense (LACMexec-pure tt evIn) ⟩
--   LEtup-to-LEtupDense evIn
--   ≡⟨ sym (ev+zeroR' DSem5-ctg-zeroLEnv') ⟩
--   LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5 (flip (interp {Γ = Γ}) unit ∘ Etup-to-val) a (to-LinRepDense {D2τ' Un} ctg))
--   ∎
-- chad-equiv-DSem6 {Γ = Γ} a evIn ctg (pair' {σ = σ} {τ = τ} l r) = ?
-- chad-equiv-DSem6 {Γ = Γ} a evIn ctg (let' {σ = σ} {τ = τ} rhs body) =
--   let 
--       chain-f : (env : Rep (Etup Pr (σ ∷ Γ))) → Rep τ
--       chain-f = (λ env → interp (Etup-to-val {Pr} {σ ∷ Γ} env) body)
--       chain-g : (env : Rep (Etup Pr Γ)) → Rep σ × Rep (Etup Pr Γ)
--       chain-g = (λ env → (interp (Etup-to-val {Pr} {Γ} env) rhs , env))
--       a2 : Rep σ × Rep (Etup Pr Γ)
--       a2 = (interp (Etup-to-val a) rhs , a)

--       dsem-f = DSem5 {σ :* Etup Pr Γ} {τ} chain-f a2 ctg
--       dsem-g = DSem5 {Etup Pr Γ} {σ :* Etup Pr Γ} chain-g a dsem-f

--       ih-f = chad-equiv-DSem6 {Γ = σ ∷ Γ} a2 (zero-LEnv (σ ∷ Γ)) ctg body
--       ih-f' = trans ih-f (cong₂ (_,_) (plusvDense-zeroL' {{zerov-is-zerovDense σ}}) (ev+zeroL' (sym zerov-LEnvDense-is-zero-LEnv)))

--       -- ih-g : LEtup-to-LEtupDense (LACMexec (interp (Etup-to-val-primal a) (chad rhs) .snd (from-LinRepDense (D2τ' σ) (dsem-f .fst)) .fst) evIn)
--             -- ≡ (LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense
--             -- (DSem5 (flip interp rhs ∘ Etup-to-val) a (to-LinRepDense {D2τ' σ} (from-LinRepDense (D2τ' σ) (dsem-f .fst))))) 
--       ih-g : LEtup-to-LEtupDense (LACMexec (interp (Etup-to-val-primal a) (chad rhs) .snd (from-LinRepDense (dsem-f .fst)) .fst) evIn)
--         ≡ (LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5 (flip interp rhs ∘ Etup-to-val) a (dsem-f .fst)))
--       ih-g = chad-equiv-DSem6 {Γ = Γ} a evIn (dsem-f .fst) rhs

--       foo = {! dsem-f .fst  !}
--   in begin
--   LEtup-to-LEtupDense (LACMexec (interp (Etup-to-val-primal a) (chad (let' rhs body)) .snd (from-LinRepDense ctg) .fst) evIn)
--   -- LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5  chain-g a (LEtup-to-LEtupDense {map D2τ' (σ ∷ Γ)} (LACMexec (interp (Etup-to-val-primal a2) (chad body) .snd ctg .fst) (zero-LEnv (σ ∷ Γ)))))
--   -- LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5  chain-g a (LEtup-to-LEtupDense {map D2τ' (σ ∷ Γ)} (LACMexec (interp (Etup-to-val-primal a2) (chad body) .snd ctg .fst) (zero-LEnv (σ ∷ Γ)))))
--   -- LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5  chain-g a ({!   !}))
--   -- ≡⟨ ev+congR (cong Etup-to-LEtupDense (cong (DSem5 chain-g a) {! ih1'  !})) ⟩
--   -- LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense
--           --  (DSem5 (flip interp rhs ∘ Etup-to-val) a (to-LinRepDense {D2τ' σ} (from-LinRepDense (D2τ' σ) (DSem5 (λ env → interp (push (env .fst) (Etup-to-val (env .snd))) body) a2 (to-LinRepDense {D2τ' τ} (snf ctg)) .fst))))
--   ≡⟨ {!  !} ⟩
--   LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (dsem-g)
--   ≡⟨⟩
--   LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5 chain-g a dsem-f)
--   ≡⟨⟩
--   LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense ((DSem5 {Etup Pr Γ} {σ :* Etup Pr Γ} chain-g a ∘ DSem5 {σ :* Etup Pr Γ} {τ} chain-f (chain-g a) ) ctg)
--   ≡⟨ ev+congR (cong Etup-to-LEtupDense (sym (DSem5-chain-app chain-f chain-g a ctg))) ⟩
--   LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5 (chain-f ∘ chain-g) a ctg)
--   ≡⟨⟩
--   LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5 (flip interp (let' rhs body) ∘ Etup-to-val) a ctg)
--   ∎ 
-- chad-equiv-DSem6 {Γ = Γ} a evIn ctg t = {!   !}

-- chad-dense-lemma : {Γ : Env Pr} {τ : Typ Pr} 
                  -- → let σ  = Etup Pr Γ 
                        -- LΓ = map D2τ' Γ in
                  -- (a : Rep σ)
                  -- (evIn : LEtup LΓ )
                  -- (ctg-in : LinRep (D2τ' τ))
                  -- (t : Term Pr Γ τ)
                -- → let ctg-out = LACMexec (interp (Etup-to-val-primal a) (chad t) .snd ctg-in .fst ) evIn
                  -- in  LEtup-to-LEtupDense {LΓ} (LEtup-snf ctg-out)
                      -- ≡ {!   !}

-- Mogelijk lemma om te bewijzen  (in informele notatie)
-- to-dense (LACMexec (chad t) (snf ctg)) == to-dense (LACMexec (chad t) ctg)
lemma-snf-chad : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep σ)
                  (evIn : LEtup LΓ )
                  (ctg : LinRep (D2τ' τ))
                  (t : Term Pr Γ τ)
                → LEtup-to-LEtupDense {LΓ} (LACMexec (interp (Etup-to-val-primal a) (chad t) .snd (snf ctg) .fst ) evIn)
                  ≡ LEtup-to-LEtupDense {LΓ} (LACMexec (interp (Etup-to-val-primal a) (chad t) .snd ctg .fst ) evIn)
lemma-snf-chad {Γ = Γ} a evIn ctg unit = refl
lemma-snf-chad {Γ = Γ} a evIn ctg t = {!   !}

chad-equiv-DSem5 : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep σ)
                  (evIn : LEtup LΓ )
                  (ctg : LinRep (D2τ' τ))
                  (t : Term Pr Γ τ)
                → LEtup-to-LEtupDense {LΓ} (LACMexec (interp (Etup-to-val-primal a) (chad t) .snd (ctg) .fst ) evIn)
                  ≡ LEtup-to-LEtupDense {LΓ} evIn ev+ Etup-to-LEtupDense {Γ} (DSem5 {σ} {τ}  (flip interp t ∘ Etup-to-val) a (to-LinRepDense {D2τ' τ} ctg))
chad-equiv-DSem5 {Γ = Γ} a evIn ctg unit =
  begin
  LEtup-to-LEtupDense (LACMexec (interp (Etup-to-val-primal a) (chad unit) .snd (ctg) .fst) evIn)
  ≡⟨ cong LEtup-to-LEtupDense (LACMexec-pure tt evIn) ⟩
  LEtup-to-LEtupDense evIn
  ≡⟨ sym (ev+zeroR' DSem5-ctg-zeroLEnv') ⟩
  LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5 (flip (interp {Γ = Γ}) unit ∘ Etup-to-val) a (to-LinRepDense {D2τ' Un} ctg))
  ∎
chad-equiv-DSem5 {Γ = Γ} a evIn ctg (let' {σ = σ} {τ = τ} rhs body) =
  let -- Useful names just used for evaluating to a simpeler form
      val = Etup-to-val-primal a
      rhs-interp = interp val (chad rhs)
      body-interp-verbose = (interp
              (push (fst rhs-interp) (push rhs-interp val))
              (sink (WCopy (WSkip WEnd)) (chad body)))
      body-interp = interp (push (fst rhs-interp) (val)) (chad body)
      body-interp-equiv-verbose = interp-sink-commute-Copy-Skip-End (fst rhs-interp) (val) (chad body)
      zeroV-verbose = interp (push ctg (push body-interp-verbose (push rhs-interp empty))) (zerot σ)
      chad-t-verbose = snd body-interp-verbose ctg .fst
      m1 = (λ x → snd rhs-interp (fst x) .fst , ℤ.pos 5 Data.Integer.+ snd rhs-interp (fst x) .snd)
      zeroV = zerov (D2τ' σ) .fst
      chad-t = snd body-interp ctg .fst

      (outval1 , _) , ev1 , _ = LACM.run (LACM.scope zeroV chad-t) evIn
      (outval2 , ev2) = LACMexec chad-t (zeroV , evIn)
      equiv-lemma = cong₂ (λ α β → LEtup-to-LEtupDense (LACMexec (m1 (α , tt) .fst) β))


      -- Expressions used for applying the IH
      chain-f : (env : Rep (Etup Pr (σ ∷ Γ))) → Rep τ
      chain-f = (λ env → interp (Etup-to-val {Pr} {σ ∷ Γ} env) body)
      chain-g : (env : Rep (Etup Pr Γ)) → Rep σ × Rep (Etup Pr Γ)
      chain-g = (λ env → (interp (Etup-to-val {Pr} {Γ} env) rhs , env))
      a2 : Rep σ × Rep (Etup Pr Γ)
      a2 = (interp (Etup-to-val a) rhs , a)


      dsem-f = DSem5 {σ :* Etup Pr Γ} {τ} chain-f a2 (to-LinRepDense {D2τ' τ} ctg)
      dsem-g = DSem5 {Etup Pr Γ} {σ :* Etup Pr Γ} chain-g a dsem-f

      ih-f = chad-equiv-DSem5 {Γ = σ ∷ Γ} a2 (zero-LEnv (σ ∷ Γ)) ctg body
      ih-f' = trans ih-f (cong₂ (_,_) (plusvDense-zeroL' {{zerov-is-zerovDense σ}}) (ev+zeroL' (sym zerov-LEnvDense-is-zero-LEnv)))

      ih-g : LEtup-to-LEtupDense (LACMexec (interp (Etup-to-val-primal a) (chad rhs) .snd ((from-LinRepDense (dsem-f .fst))) .fst) evIn)
        ≡ (LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5 (flip interp rhs ∘ Etup-to-val) a (to-LinRepDense (from-LinRepDense (dsem-f .fst)))))
      ih-g = chad-equiv-DSem5 {Γ = Γ} a evIn (from-LinRepDense {D2τ' σ} (dsem-f .fst)) rhs

  in begin
  LEtup-to-LEtupDense (LACMexec (interp (Etup-to-val-primal a) (chad (let' rhs body)) .snd ctg .fst) evIn)
  ≡⟨⟩
  LEtup-to-LEtupDense ((LACMexec (LACM.bind (LACM.scope zeroV-verbose chad-t-verbose) m1) evIn))
  ≡⟨ cong LEtup-to-LEtupDense (cong₂ (λ α β → LACMexec (LACM.bind (LACM.scope α β) m1) evIn) (interp-zerot≡zerov σ) (cong (λ α → snd α ctg .fst) body-interp-equiv-verbose)) ⟩
  LEtup-to-LEtupDense ((LACMexec (LACM.bind (LACM.scope zeroV chad-t) m1) evIn))
  ≡⟨ cong LEtup-to-LEtupDense (LACM.run-bind (LACM.scope zeroV chad-t) m1 evIn .fst) ⟩
  LEtup-to-LEtupDense (LACMexec ({! m1 (outval1 , tt) .fst !}) ev1)
  ≡⟨ (let (_ , α , β) = (LACMexec-scope chad-t zeroV evIn) in equiv-lemma β α) ⟩
  LEtup-to-LEtupDense (LACMexec (m1 (outval2 , tt) .fst) ev2)
  -- ≡⟨ equiv-lemma {!   !} {!   !} ⟩
  -- LEtup-to-LEtupDense (LACMexec (m1 (from-LinRepDense (dsem-f .fst) , tt) .fst) (LEtupDense-to-LEtup (LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (dsem-f .snd))))
  ≡⟨ {!  !} ⟩

  ≡⟨ {!  !} ⟩
  -- LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (dsem-g)
  -- ≡⟨⟩
  LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5 chain-g a (DSem5 {σ :* Etup Pr Γ} {τ} chain-f a2 (to-LinRepDense {D2τ' τ} ctg)))
  ≡⟨⟩
  LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense ((DSem5 {Etup Pr Γ} {σ :* Etup Pr Γ} chain-g a ∘ DSem5 {σ :* Etup Pr Γ} {τ} chain-f (chain-g a) ) (to-LinRepDense {D2τ' τ} ctg))
  ≡⟨ ev+congR (cong Etup-to-LEtupDense (sym (DSem5-chain-app chain-f chain-g a (to-LinRepDense {D2τ' τ} ctg)))) ⟩
  LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5 (chain-f ∘ chain-g) a (to-LinRepDense {D2τ' τ} ctg))
  ≡⟨⟩
  LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem5 (flip interp (let' rhs body) ∘ Etup-to-val) a (to-LinRepDense {D2τ' τ} ctg))
  ∎ 
chad-equiv-DSem5 {Γ = Γ} a evIn ctg t = {!   !}

-- DSem4-ctg-zero' : {σ τ : Typ Pr} → { f : Rep σ  →  Rep τ } → { a : Rep (D1τ σ) } → { ctg : LinRepDense (D2τ' τ) } → {{ctg ≡ zerovDense (D2τ' τ)}} → DSem4 {σ} {τ} f a ctg ≡ zerovDense (D2τ' σ)
-- DSem4-ctg-zero' {σ} {τ} {f} {a} {ctg} {{w}} = DSem4-ctg-zero f a ctg w

-- DSem4-ctg-zeroLEnv' : {Γ : Env Pr} {τ : Typ Pr}
--                   → let σ = Etup Pr Γ in { f : Rep σ  →  Rep τ } 
--                   → { a : Rep (D1τ σ) } → { ctg : LinRepDense (D2τ' τ) } 
--                   → {{ ctg ≡ zerovDense (D2τ' τ) }} 
--                   → Etup-to-LEtupDense (DSem4 {σ} {τ} f a ctg) ≡ (zero-LEnvDense Γ)
-- DSem4-ctg-zeroLEnv' {σ} {τ} {f} {a} {ctg} {{w}} = trans (cong Etup-to-LEtupDense DSem4-ctg-zero') zerovDense-on-Etup-is-zeroLEnv2


-- DSem4-chain-lemma1 : {Γ : Env Pr} {τ ρ : Typ Pr}
--                   → let σ = Etup Pr Γ in 
--                     (a : Rep σ)
--                   → (tf : Term Pr (ρ ∷ Γ) τ)
--                   → (tg : Term Pr Γ ρ)
--                   →  let f = (λ env → interp (Etup-to-val {Pr} {ρ ∷ Γ} env) tf)
--                          g = (λ env → (interp (Etup-to-val {Pr} {Γ} env) tg , env))
--                      in DSem4 {σ} {τ} (f ∘ g) (primal σ a)
--                         ≡ DSem4 {σ} {ρ :* σ} g (primal σ a) ∘ DSem4 {ρ :* σ} {τ} f (primal (ρ :* σ) (g a))
-- DSem4-chain-lemma1 {Γ = Γ} {τ = τ} {ρ = ρ} a tf tg = 
--   let σ = Etup Pr Γ
--       f env = interp (Etup-to-val {Pr} {ρ ∷ Γ} env) tf
--       g env = interp (Etup-to-val {Pr} {Γ} env) tg , env
--   in DSem4-chain {σ} {ρ :* σ} {τ} f g a 

-- chad-equiv-DSem4 : {Γ : Env Pr} {τ : Typ Pr} 
--                   → let σ  = Etup Pr Γ 
--                         LΓ = map D2τ' Γ in
--                   (a : Rep (D1τ σ))
--                   (evIn : LEtup LΓ )
--                   (ctg : LinRep (D2τ' τ))
--                   (t : Term Pr Γ τ)
--                 → LEtup-to-LEtupDense {LΓ} (LACMexec (interp (D1Etup-to-val a) (chad t) .snd ctg .fst ) evIn)
--                   ≡ LEtup-to-LEtupDense {LΓ} evIn ev+ Etup-to-LEtupDense {Γ} (DSem4 {σ} {τ}  (flip interp t ∘ Etup-to-val) a (to-LinRepDense {D2τ' τ} ctg))
-- chad-equiv-DSem4 {Γ = Γ} a evIn ctg unit =
--   begin
--   LEtup-to-LEtupDense { map D2τ' Γ } (LACMexec (interp (D1Etup-to-val a) (chad unit) .snd ctg .fst) evIn)
--   ≡⟨ cong LEtup-to-LEtupDense (LACMexec-pure tt evIn) ⟩
--   LEtup-to-LEtupDense evIn
--   ≡⟨ sym (ev+zeroR' DSem4-ctg-zeroLEnv') ⟩
--   (LEtup-to-LEtupDense { map D2τ' Γ } evIn ev+
--      Etup-to-LEtupDense
--      (DSem4 (flip (interp {Γ = Γ}) unit ∘ Etup-to-val) a
--       (to-LinRepDense {D2τ' Un} ctg)))
--   ∎
-- chad-equiv-DSem4 {Γ = Γ} a evIn ctg@(just (ctgL , ctgR)) (pair {σ = σ} {τ = τ} l r) =
--   let m1 = snd (interp (D1Etup-to-val a) (chad l)) ctgL .fst
--       m2 = snd (interp (D1Etup-to-val a) (chad r)) ctgR .fst
--       ev1 = LACMexec m1 evIn
--       ev2 = LACMexec m2 ev1
--       dsemL = DSem4 (flip interp l ∘ Etup-to-val) a (to-LinRepDense _ ctgL)
--       dsemR = DSem4 (flip interp r ∘ Etup-to-val) a (to-LinRepDense _ ctgR)
--   in begin
--       LEtup-to-LEtupDense (LACMexec (LACMsequence m1 m2) evIn)
--       ≡⟨ cong LEtup-to-LEtupDense (LACMexec-sequence m1 m2 evIn) ⟩
--       LEtup-to-LEtupDense ev2
--       ≡⟨ chad-equiv-DSem4 a ev1 ctgR r ⟩
--       LEtup-to-LEtupDense ev1 ev+ Etup-to-LEtupDense dsemR
--       ≡⟨ ev+congL (chad-equiv-DSem4 a evIn ctgL l) ⟩
--       (LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense dsemL) ev+ Etup-to-LEtupDense dsemR
--       ≡⟨ ev+assoc _ _ _ ⟩
--       LEtup-to-LEtupDense evIn ev+ (Etup-to-LEtupDense dsemL ev+ Etup-to-LEtupDense dsemR)
--       ≡⟨ ev+congR (evplus-on-Etup-is-plusv dsemL dsemR) ⟩
--       LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (plusvDense _ dsemL dsemR)
--       ≡⟨ ev+congR (cong Etup-to-LEtupDense (sym (DSem4-pair (flip interp l ∘ Etup-to-val) (flip interp r ∘ Etup-to-val) a (to-LinRepDense {D2τ' σ} ctgL) (to-LinRepDense {D2τ' τ} ctgR)))) ⟩
--       (LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem4 (flip interp (pair l r) ∘ Etup-to-val) a (to-LinRepDense {D2τ' (σ :* τ}) ctg)))
--       ∎

-- chad-equiv-DSem4 {Γ = Γ} a evIn ctg (let' {σ = σ} {τ = τ} rhs body) =
--   let rhs-interp = interp (D1Etup-to-val a) (chad rhs)
--       body-interp-verbose = (interp
--               (push (fst rhs-interp) (push rhs-interp (D1Etup-to-val a)))
--               (sink (WCopy (WSkip WEnd)) (chad body)))
--       body-interp = interp (D1Etup-to-val (fst rhs-interp  , a)) (chad body)
--       body-interp-equiv-verbose = (interp-sink-commute-Copy-Skip-End (fst rhs-interp) (D1Etup-to-val a) (chad body))
--       zeroV-verbose = interp (push ctg (push body-interp-verbose (push rhs-interp empty))) (zerot σ)
--       chad-body-verbose = snd body-interp-verbose ctg .fst
--       zeroV = zerov (D2τ' σ) .fst
--       chad-body = snd body-interp ctg .fst
--       m1 = LACM.scope zeroV chad-body
--       m2 = (λ x → snd rhs-interp (fst x) .fst , ℤ.pos 5 Data.Integer.+ snd rhs-interp (fst x) .snd)
--       (outval-s1 , _) , ev-zeroV , _ = LACM.run (LACM.scope zeroV chad-body) evIn
--       (outval-s2 , ev-chad-body) = LACMexec chad-body (zeroV , evIn)

--       dsemBody = DSem4 {Etup Pr (σ ∷ Γ)} {τ} (flip interp body ∘ Etup-to-val) (fst rhs-interp , a) (to-LinRepDense {D2τ' τ} ctg)
--       dsemRhs = DSem4 {Etup Pr Γ} {σ} (flip interp rhs ∘ Etup-to-val) a (dsemBody .fst)
--       ihBody = (chad-equiv-DSem4 (fst rhs-interp , a) (zeroV , evIn) ctg body)

--       ev-m2-a = LACMexec (m2 (outval-s1 , tt) .fst) ev-zeroV
--       ev-m2-b = LACMexec (m2 (outval-s2 , tt) .fst) ev-chad-body
--       -- ev-m2-c = LACMexec (m2 (dsemBody .fst , tt) .fst) (evIn ev+ dsemBody .snd)
--       -- ev-m2-c = LACMexec (m2 ({! dsemBody .fst  !} , tt) .fst) {!   !}
--       ev-m2-equiv = cong₂ (λ α β → LACMexec (m2 (α , tt) .fst) β)

--       tempF : (env : Rep (Etup Pr (σ ∷ Γ))) → Rep τ
--       tempF = (λ env → interp (Etup-to-val {Pr} {σ ∷ Γ} env) body)
--       tempG : (env : Rep (Etup Pr Γ)) → Rep (Etup Pr (σ ∷ Γ))
--       tempG = (λ env → (interp (Etup-to-val {Pr} {Γ} env) rhs , env))
--   in begin
--   LEtup-to-LEtupDense (LACMexec (LACM.bind (LACM.scope zeroV-verbose chad-body-verbose) m2) evIn)
--   ≡⟨ cong LEtup-to-LEtupDense (cong₂ (λ α β → LACMexec (LACM.bind (LACM.scope α β) m2) evIn) (interp-zerot≡zerov σ) (cong (λ α → snd α ctg .fst) body-interp-equiv-verbose)) ⟩
--   LEtup-to-LEtupDense (LACMexec (LACM.bind (LACM.scope zeroV chad-body) m2) evIn)
--   -- ≡⟨ {!   !} ⟩
--   -- (LEtup-to-LEtupDense evIn ev+ (Etup-to-LEtupDense (dsemBody .snd) ev+ Etup-to-LEtupDense dsemRhs))
--   ≡⟨ {!   !} ⟩
--                         -- DSem4 {σ} {ρ :* σ} g (primal σ a) ∘ DSem4 {ρ :* σ} {τ} f (primal (ρ :* σ) (g a))
--   -- LEtup-to-LEtupDense evIn ev+ (Etup-to-LEtupDense (DSem4 (() ∘ ()) a (to-LinRepDense {D2τ' τ} ctg)))
--   LEtup-to-LEtupDense evIn ev+ (Etup-to-LEtupDense ((DSem4 {Etup Pr Γ} {σ :* (Etup Pr Γ)} tempG a ∘ DSem4 {σ :* (Etup Pr Γ)} {τ} tempF ({!   !}) ) (to-LinRepDense {D2τ' τ} ctg)))
--   ≡⟨ {!   !} ⟩ 
--   LEtup-to-LEtupDense evIn ev+ (Etup-to-LEtupDense ((DSem4 ((λ env → interp (Etup-to-val {Pr} {σ ∷ Γ} env) body) ∘ (λ env → (interp (Etup-to-val {Pr} {Γ} env) rhs , env))) a) (to-LinRepDense {D2τ' τ} ctg)))
--   ≡⟨⟩
--   LEtup-to-LEtupDense evIn ev+ (Etup-to-LEtupDense (DSem4 (λ env → interp (push (interp (Etup-to-val env) rhs) (Etup-to-val env)) body) a (to-LinRepDense {D2τ' τ} ctg)))
--   ≡⟨⟩
--   LEtup-to-LEtupDense evIn ev+ (Etup-to-LEtupDense (DSem4 ((λ env → interp (push (interp env rhs) env) body ) ∘ Etup-to-val) a (to-LinRepDense {D2τ' τ} ctg)))
--   ≡⟨⟩
--   LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem4 (flip interp (let' rhs body) ∘ Etup-to-val) a (to-LinRepDense {D2τ' τ} ctg))
--   ∎  
-- chad-equiv-DSem4 a evIn ctg t = {!   !}   