module chad-equiv-DSem3 where
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

open import utility3
import utility
open import giga-chad using (D1Term)
open import spec hiding (eval)
open import eval-sink-commute
import spec as S
import spec.LACM as LACM
open LACM using (LACM)


postulate
    DSem :   {σ τ : Typ Pr} 
            → (Rep2 σ  →  Rep2 τ)
            → (Rep2 (D1τ σ) → Rep2 (D2τ τ) → Rep2 (D2τ σ))

    DSem4 :  {σ τ : Typ Pr} 
            → (Rep σ  →  Rep τ)
            → (Rep (D1τ σ) → LinRep2 (D2τ' τ) → LinRep2 (D2τ' σ))

    DSem-chain : {τ1 τ2 τ3 : Typ Pr}
                → (f : Rep2 τ2 → Rep2 τ3)
                → (g : Rep2 τ1 → Rep2 τ2)
                → (a : Rep2 τ1)
                → DSem {τ1} {τ3} (f ∘ g) (primal2 τ1 a)
                  ≡ DSem {τ1} {τ2} g (primal2 τ1 a) ∘ DSem {τ2} {τ3} f (primal2 τ2 (g a))

    DSem-identity : {σ : Typ Pr} 
            → (a : Rep2 (D1τ σ))
            → (ctg : Rep2 (D2τ σ)) 
            → DSem {σ} {σ} id a ctg ≡ ctg

    DSem-ctg-zero : {σ τ : Typ Pr} 
            → (f : Rep2 σ  →  Rep2 τ)
            → (a : Rep2 (D1τ σ))
            → (ctg : Rep2 (D2τ τ)) 
            → ctg ≡ zerov2 (D2τ' τ)
            → DSem {σ} {τ} f a ctg ≡ zerov2 (D2τ' σ)

    DSem-pair : {σ τ1 τ2 : Typ Pr}
            → (f : Rep2 σ →  Rep2 τ1) 
            → (g : Rep2 σ →  Rep2 τ2) 
            → (a : Rep2 (D1τ σ))
            → (ctg-f : Rep2 (D2τ τ1))
            → (ctg-g : Rep2 (D2τ τ2))
            → let dsem-f = DSem {σ} {τ1} f a ctg-f
                  dsem-g = DSem {σ} {τ2} g a ctg-g
                  h : Rep2 σ → Rep2 (τ1 :* τ2)
                  h e = (f e , g e)
                  ctg : LinRep2 (D2τ' (τ1 :* τ2))
                  ctg = (ctg-f , ctg-g)
              in DSem {σ} {τ1 :* τ2} h a ctg
                 ≡ plusv2 (D2τ' σ) dsem-f dsem-g

DSem-ctg-zero' : {σ τ : Typ Pr} → { f : Rep2 σ  →  Rep2 τ } → { a : Rep2 (D1τ σ) } → { ctg : Rep2 (D2τ τ) } → {{ ctg ≡ zerov2 (D2τ' τ) }} 
                  → DSem {σ} {τ} f a ctg ≡ zerov2 (D2τ' σ)
DSem-ctg-zero' {σ} {τ} {f} {a} {ctg} {{w}} = DSem-ctg-zero f a ctg w

DSem-ctg-zeroLEnv' : {Γ : Env Pr} {τ : Typ Pr} → let σ = Etup Pr Γ in { f : Rep2 σ  →  Rep2 τ } → { a : Rep2 (D1τ σ) } → { ctg : Rep2 (D2τ τ) } → {{ ctg ≡ zerov2 (D2τ' τ) }} 
                  → Etup-to-LEtup2 (DSem {σ} {τ} f a ctg) ≡ zero-LEnv2 Γ
DSem-ctg-zeroLEnv' {σ} {τ} {f} {a} {ctg} {{w}} = trans (cong Etup-to-LEtup2 DSem-ctg-zero') zerov2-on-Etup-is-zeroLEnv2 

etup1-toLEtup2 : {Γ : Env Pr} → LinRep2 (D2τ' (utility.Etup Pr Γ)) → LEtup2 (map D2τ' Γ)
etup1-toLEtup2 x = {!   !}
-- etup1-toLEtup2 {τ ∷ Γ} (x , xs) = x , Etup-to-LEtup2 xs 

chad-equiv-DSem4 : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = utility.Etup Pr Γ 
                        LΓ = map D2τ' Γ in
                  (a : Rep (D1τ σ))
                  (evIn : LEtup LΓ )
                  (ctg : LinRep (D2τ' τ))            -- ctg, some arbitrary (gradient) input
                  (t : Term Pr Γ τ)            -- f(ctg), the original program
                → to-LEtup2 LΓ (LACMexec (utility.interp (utility.D1Etup-to-val a) (chad t) .snd ctg .fst ) evIn)
                  ≡ to-LEtup2 LΓ evIn ev+ etup1-toLEtup2 {Γ} (DSem4 {σ} {τ}  (flip utility.interp t ∘ utility.Etup-to-val) a (to-LinRep2 (D2τ' τ) ctg))
chad-equiv-DSem4 a evIn ctg unit =
  begin
  {!   !}
  ≡⟨ {!   !} ⟩
  {!   !}
  ∎
chad-equiv-DSem4 a evIn ctg t = {!   !}

chad-equiv-DSem : {Γ : Env Pr} {τ : Typ Pr} 
                  → let σ  = Etup Pr Γ
                        LΓ = (map D2τ' Γ) in
                  (a : Rep2 (D1τ σ))
                  (evIn : LEtup2 LΓ )
                  (ctg : Rep2 (D2τ τ))            -- ctg, some arbitrary (gradient) input
                  (t : Term Pr Γ τ)            -- f(ctg), the original program
                → LACMexec2 (interp (D1Etup-to-val2 a) (chad t) .snd ctg ) evIn
                  ≡ evIn ev+ (Etup-to-LEtup2 (DSem (flip interp t ∘ Etup-to-val2) a ctg))            -- f'(ctg) according to DSem
chad-equiv-DSem {Γ = Γ} a evIn ctg unit = 
  begin  
  LACMexec2 (interp (D1Etup-to-val2 a) (snd' $ chad unit) ctg) evIn
  ≡⟨ trans (LACMexec-map2 _ evIn) (LACMexec-pure2 tt evIn) ⟩
  evIn
  ≡⟨ sym (ev+zeroR' DSem-ctg-zeroLEnv')  ⟩     
  evIn ev+ Etup-to-LEtup2 (DSem (flip (interp {Γ = Γ}) unit ∘ Etup-to-val2) a ctg)  
  ∎             
chad-equiv-DSem {Γ = Γ} a evIn ctg@(ctgL , ctgR) (pair l r) = 
  let m1 = snd (interp (D1Etup-to-val2 a) (chad l)) ctgL
      m2 = snd (interp (D1Etup-to-val2 a) (chad r)) ctgR
  in begin
  LACMexec2 (interp (D1Etup-to-val2 a) (chad (pair l r)) .snd ctg) evIn
  ≡⟨ LACMexec-map2 _ evIn ⟩
  {!   !}
  -- LACMexec2
    -- (spec.eval (D1Etup-to-val2 a) (chad (pair l r)) .fst .snd
    --  (from-Rep2 (D2τ (σ :* τ)) (ctgL , ctgR)) .fst)
    -- evIn
  ≡⟨ {!   !} ⟩
  (evIn ev+ Etup-to-LEtup2 (DSem (flip interp (pair l r) ∘ Etup-to-val2) a ctg))
  ∎
chad-equiv-DSem {Γ = Γ} a evIn ctg t = {!   !}