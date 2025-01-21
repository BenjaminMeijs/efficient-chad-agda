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
open LACM using (LACM)

postulate
    DSem4 :  {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep (D1τ σ)) 
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

DSem4-ctg-zero' : {σ τ : Typ Pr} → { f : Rep σ  →  Rep τ } → { a : Rep (D1τ σ) } → { ctg : LinRepDense (D2τ' τ) } → {{ctg ≡ zerovDense (D2τ' τ)}} → DSem4 {σ} {τ} f a ctg ≡ zerovDense (D2τ' σ)
DSem4-ctg-zero' {σ} {τ} {f} {a} {ctg} {{w}} = DSem4-ctg-zero f a ctg w

DSem4-ctg-zeroLEnv' : {Γ : Env Pr} {τ : Typ Pr}
                  → let σ = Etup Pr Γ in { f : Rep σ  →  Rep τ } 
                  → { a : Rep (D1τ σ) } → { ctg : LinRepDense (D2τ' τ) } 
                  → {{ ctg ≡ zerovDense (D2τ' τ) }} 
                  → Etup-to-LEtupDense (DSem4 {σ} {τ} f a ctg) ≡ (zero-LEnvDense Γ)
DSem4-ctg-zeroLEnv' {σ} {τ} {f} {a} {ctg} {{w}} = trans (cong Etup-to-LEtupDense DSem4-ctg-zero') zerovDense-on-Etup-is-zeroLEnv2

chad-equiv-DSem4 : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep (D1τ σ))
                  (evIn : LEtup LΓ )
                  (ctg : LinRep (D2τ' τ))            -- ctg, some arbitrary (gradient) input
                  (t : Term Pr Γ τ)            -- f(ctg), the original program
                → LEtup-to-LEtupDense {LΓ} (LACMexec (interp (D1Etup-to-val a) (chad t) .snd ctg .fst ) evIn)
                  ≡ LEtup-to-LEtupDense {LΓ} evIn ev+ Etup-to-LEtupDense {Γ} (DSem4 {σ} {τ}  (flip interp t ∘ Etup-to-val) a (to-LinRepDense (D2τ' τ) ctg))
chad-equiv-DSem4 {Γ = Γ} a evIn ctg unit =
  begin
  LEtup-to-LEtupDense { map D2τ' Γ } (LACMexec (interp (D1Etup-to-val a) (chad unit) .snd ctg .fst) evIn)
  ≡⟨ cong LEtup-to-LEtupDense (LACMexec-pure tt evIn) ⟩
  LEtup-to-LEtupDense evIn
  ≡⟨ sym (ev+zeroR' DSem4-ctg-zeroLEnv') ⟩
  (LEtup-to-LEtupDense { map D2τ' Γ } evIn ev+
     Etup-to-LEtupDense
     (DSem4 (flip (interp {Γ = Γ}) unit ∘ Etup-to-val) a
      (to-LinRepDense (D2τ' Un) ctg)))
  ∎
chad-equiv-DSem4 {Γ = Γ} a evIn ctg@(just (ctgL , ctgR)) (pair {σ = σ} {τ = τ} l r) =
  let m1 = snd (interp (D1Etup-to-val a) (chad l)) _ .fst
      m2 = snd (interp (D1Etup-to-val a) (chad r)) _ .fst
      ev1 = LACMexec m1 evIn
      ev2 = LACMexec m2 ev1
  in 
  --     dsemL = DSem4 (flip interp l ∘ Etup-to-val) a (to-LinRepDense _ ctgL)
  --     dsemR = DSem4 (flip interp r ∘ Etup-to-val) a (to-LinRepDense _ ctgR)
  -- in begin
  -- LEtup-to-LEtupDense (LACMexec (LACMsequence m1 m2) evIn)
  -- ≡⟨ cong LEtup-to-LEtupDense (LACMexec-sequence m1 m2 evIn) ⟩
  -- LEtup-to-LEtupDense ev2
  -- ≡⟨ chad-equiv-DSem4 a ev1 ctgR r ⟩
  -- LEtup-to-LEtupDense ev1 ev+ Etup-to-LEtupDense dsemR
  -- ≡⟨ ev+congL (chad-equiv-DSem4 a evIn ctgL l) ⟩
  -- (LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense dsemL) ev+ Etup-to-LEtupDense dsemR
  -- ≡⟨ ev+assoc _ _ _ ⟩
  -- LEtup-to-LEtupDense evIn ev+ (Etup-to-LEtupDense dsemL ev+ Etup-to-LEtupDense dsemR)
  -- ≡⟨ ev+congR (evplus-on-Etup-is-plusv dsemL dsemR) ⟩
  -- LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (plusvDense _ dsemL dsemR)
  -- ≡⟨ ev+congR (cong Etup-to-LEtupDense (sym (DSem4-pair (flip interp l ∘ Etup-to-val) (flip interp r ∘ Etup-to-val) a (to-LinRepDense _ ctgL) (to-LinRepDense _ ctgR)))) ⟩
  -- (LEtup-to-LEtupDense evIn ev+ Etup-to-LEtupDense (DSem4 (flip interp (pair l r) ∘ Etup-to-val) a (to-LinRepDense (D2τ' (σ :* τ)) ctg)))
  -- ∎
chad-equiv-DSem4 a evIn ctg t = {!   !}