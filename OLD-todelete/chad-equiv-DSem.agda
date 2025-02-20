module chad-equiv-DSem where
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

open import utility
open import giga-chad using (D1Term)
open import spec hiding (eval)
open import eval-sink-commute
import spec as S
import spec.LACM as LACM
open LACM using (LACM)


postulate
    DSem3 :   {σ τ : Typ Pr} 
            → (Rep σ  →  Rep τ)
            → (Rep (D1τ σ) → Rep (D2τ τ) → Rep (D2τ σ))
    
    DSem3-not-maybe : {Γ : Env Pr} {τ ρ : Typ Pr} 
            → let σ = Etup Pr (ρ ∷ Γ) in
              ( f : Rep σ  →  Rep τ )
            → ( a : Rep (D1τ σ) ) → ( ctg : Rep (D2τ τ) )
            → DSem3 {σ} {τ} f a ctg ≡ nothing
            → ⊥

    DSem3-chain : {τ1 τ2 τ3 : Typ Pr}
                → (f : Rep τ2 → Rep τ3)
                → (g : Rep τ1 → Rep τ2)
                → (a : Rep τ1)
                → DSem3 {τ1} {τ3} (f ∘ g) (primal τ1 a)
                  ≡ DSem3 {τ1} {τ2} g (primal τ1 a) ∘ DSem3 {τ2} {τ3} f (primal τ2 (g a))

    DSem3-identity : {σ : Typ Pr} 
            → (a : Rep (D1τ σ))
            → (ctg : Rep (D2τ σ)) 
            → DSem3 {σ} {σ} id a ctg ≡ ctg

    DSem3-ctg-zero : {σ τ : Typ Pr} 
            → (f : Rep σ  →  Rep τ)
            → (a : Rep (D1τ σ))
            → (ctg : Rep (D2τ τ)) 
            → sparse-normal-form ctg ≡ sparse-normal-form (fst (zerov (D2τ' τ)))
            → DSem3 {σ} {τ} f a ctg ≡ fst (zerov (D2τ' σ))

    DSem3-pair : {σ τ1 τ2 : Typ Pr}
            → (f : Rep σ →  Rep τ1) 
            → (g : Rep σ →  Rep τ2) 
            → (a : Rep (D1τ σ))
            → (ctg-f : Rep (D2τ τ1))
            → (ctg-g : Rep (D2τ τ2))
            → let dsem-f = DSem3 {σ} {τ1} f a ctg-f
                  dsem-g = DSem3 {σ} {τ2} g a ctg-g
                  h : Rep σ → Rep (τ1 :* τ2)
                  h e = (f e , g e)
                  ctg : LinRep (D2τ' (τ1 :* τ2))
                  ctg = just (ctg-f , ctg-g)
              in DSem3 {σ} {τ1 :* τ2} h a ctg
                 ≡ fst (plusv (D2τ' σ) dsem-f dsem-g)

    DSem3-var : {Γ : Env Pr} {τ : Typ Pr}
              → (x : Idx Γ τ)
              → (a : Rep (D1τ (Etup Pr Γ)))
              → (ctg : Rep (D2τ τ))
              → Etup-to-LEtup (DSem3 (flip valprj x ∘ Etup-to-val) a ctg)
                ≡ onehot-LEnv (convIdx D2τ' x) ctg

    DSem : {Γ : Env Pr} {τ : Typ Pr} 
            → (Val Pr Γ →  Rep τ)                                 -- f(x)
            → (Val Du (D1Γ Γ) → Rep (D2τ τ) → LEtup (map D2τ' Γ)) -- f'(x)
    
    -- In essence: When the incoming cotangent is zero, the outgoing cotangent is zero
    DSem-ctg-zero : {Γ : Env Pr} {τ : Typ Pr}
            → (f : Val Pr Γ →  Rep τ) 
            → (env : Val Du (D1Γ Γ)) → (ctg : Rep (D2τ τ))
            → ctg ≡ fst (zerov (D2τ' τ))
            → DSem f env ctg ≡ zero-LEnv Γ

    DSem-ctg-zero-normalized : {Γ : Env Pr} {τ : Typ Pr}
            → (f : Val Pr Γ →  Rep τ) 
            → (env : Val Du (D1Γ Γ)) → (ctg : Rep (D2τ τ))
            → sparse-normal-form ctg ≡ sparse-normal-form (fst (zerov (D2τ' τ)))
            → DSem f env ctg ≡ zero-LEnv Γ

    DSem-pair : {Γ : Env Pr} {τ σ : Typ Pr}
            → (f : Val Pr Γ →  Rep σ) 
            → (g : Val Pr Γ →  Rep τ) 
            → (env : Val Du (D1Γ Γ))
            → (ctg-f : Rep (D2τ σ))
            → (ctg-g : Rep (D2τ τ))
            → let h : Val Pr Γ → Rep (σ :* τ)
                  h e = (f e , g e)
                  ctg : LinRep (D2τ' (σ :* τ))
                  ctg = just (ctg-f , ctg-g)
              in DSem {τ = σ :* τ} h env ctg
                 ≡ (DSem f env ctg-f) ev+ (DSem g env ctg-g)

    DSem-inj₁ : {Γ : Env Pr} {σ ρ : Typ Pr}
            → (f : Val Pr Γ → Rep σ)
            → (env : Val Du (D1Γ Γ))
            → (ctg : Rep (D2τ σ))
            → let g : Val Pr Γ → Rep σ ⊎ Rep ρ
                  g = inj₁ ∘ f
              in DSem f env ctg 
                 ≡ DSem {τ = σ :+ ρ} g env (just (inj₁ ctg))

    DSem-inj₂ : {Γ : Env Pr} {σ ρ : Typ Pr}
            → (f : Val Pr Γ → Rep σ)
            → (env : Val Du (D1Γ Γ))
            → (ctg : Rep (D2τ σ))
            → let g : Val Pr Γ → Rep ρ ⊎ Rep σ
                  g = inj₂ ∘ f
              in DSem f env ctg 
                 ≡ DSem {τ = ρ :+ σ} g env (just (inj₂ ctg))
    
    DSem-chain-env : {Γ : Env Pr} {τ σ : Typ Pr}
            → (f : Val Pr Γ → Rep τ)
            → (g : Val Pr (τ ∷ Γ)  → Rep σ)
            → (envPr : Val Pr Γ)
            → (ctg : Rep (D2τ σ))
            → let envDu = primalVal envPr
                  h env' = g (push (f env') env')
                  dsemg = DSem g (push (primal τ (f envPr)) envDu) ctg
                  dsemf = DSem f envDu (dsemg .fst)
              in DSem h envDu ctg
                 ≡ dsemg .snd ev+ dsemf
    
    DSem-var : {Γ : Env Pr} {τ : Typ Pr} 
              → (x : Idx Γ τ)
              → (env : Val Du (D1Γ Γ))
              → (ctg : Rep (D2τ τ))
              → DSem (flip valprj x) env ctg
                ≡ onehot-LEnv (convIdx D2τ' x) ctg

-- Same as DSem-ctg-zero, but more arguments are left implicit for convenient usage.
DSem-ctg-zero' : {Γ : Env Pr} {τ : Typ Pr} → { f : Val Pr Γ →  Rep τ } → { env : Val Du (D1Γ Γ) } → { ctg : Rep (D2τ τ) }
  → {{ctg ≡ fst (zerov (D2τ' τ))}} → DSem f env ctg ≡ zero-LEnv Γ
DSem-ctg-zero' {Γ} {τ} {f} {env} {ctg} {{w}} = DSem-ctg-zero f env ctg w
-- Same as DSem-ctg-zero-normalized, but more arguments are left implicit for convenient usage.
DSem-ctg-zero-normalized' : {Γ : Env Pr} {τ : Typ Pr} → { f : Val Pr Γ →  Rep τ } → { env : Val Du (D1Γ Γ) } → { ctg : Rep (D2τ τ) }
  → {{sparse-normal-form ctg ≡ sparse-normal-form (fst (zerov (D2τ' τ))) }} → DSem f env ctg ≡ zero-LEnv Γ
DSem-ctg-zero-normalized' {Γ} {τ} {f} {env} {ctg} {{w}} = DSem-ctg-zero-normalized f env ctg w

DSem3-ctg-zero' : {σ τ : Typ Pr} → { f : Rep σ  →  Rep τ } → { a : Rep (D1τ σ) } → { ctg : Rep (D2τ τ) } → {{ sparse-normal-form ctg ≡ sparse-normal-form (fst (zerov (D2τ' τ))) }} 
                  → DSem3 {σ} {τ} f a ctg ≡ fst (zerov (D2τ' σ))
DSem3-ctg-zero' {σ} {τ} {f} {a} {ctg} {{w}} = DSem3-ctg-zero f a ctg w

DSem3-ctg-zeroLEnv' : {Γ : Env Pr} {τ : Typ Pr} → let σ = Etup Pr Γ in { f : Rep σ  →  Rep τ } → { a : Rep (D1τ σ) } → { ctg : Rep (D2τ τ) } → {{ sparse-normal-form ctg ≡ sparse-normal-form (fst (zerov (D2τ' τ))) }} 
                  → Etup-to-LEtup (DSem3 {σ} {τ} f a ctg) ≡ zero-LEnv Γ
DSem3-ctg-zeroLEnv' {σ} {τ} {f} {a} {ctg} {{w}} = trans (cong Etup-to-LEtup DSem3-ctg-zero') zerov-on-Etup-is-zeroLEnv

chad-equiv-DSem3 : {Γ : Env Pr} {τ : Typ Pr} 
                → let σ = Etup Pr Γ in
                  (a : Rep (D1τ σ))
                  (evIn : LEtup (map D2τ' Γ))
                  (ctg : Rep (D2τ τ))            -- ctg, some arbitrary (gradient) input
                  (t : Term Pr Γ τ)            -- f(ctg), the original program
                → LACMexec (interp (D1Etup-to-val a) (chad t) .snd ctg .fst) evIn -- f'(ctg) according to CHAD
                  ≡ evIn ev+ (Etup-to-LEtup (DSem3 (flip interp t ∘ Etup-to-val) a ctg))            -- f'(ctg) according to DSem
chad-equiv-DSem3 {Γ = Γ} a evIn ctg unit = 
  begin
  LACMexec (fst (interp (D1Etup-to-val a) (snd' $ chad unit) ctg)) evIn 
  ≡⟨ LACMexec-pure _ evIn ⟩
  evIn
  ≡⟨ sym (ev+zeroR' DSem3-ctg-zeroLEnv')  ⟩
  evIn ev+ (Etup-to-LEtup (DSem3 (flip (interp {Γ = Γ}) unit ∘ Etup-to-val) a ctg)) 
  ∎
chad-equiv-DSem3 {Γ = Γ} a evIn nothing (pair l r) = 
  let m1 = snd (interp (D1Etup-to-val a) (chad l)) _ .fst
      m2 = snd (interp (D1Etup-to-val a) (chad r)) _ .fst
      ihl = chad-equiv-DSem3 a evIn _ l
      ihr = chad-equiv-DSem3 a evIn _ r
      ihl' = trans ihl (ev+zeroR' DSem3-ctg-zeroLEnv')
      ihr' = trans ihr (ev+zeroR' DSem3-ctg-zeroLEnv')
  in begin
      LACMexec (LACMsequence m1 m2) evIn
      ≡⟨ LACMexec-sequence-unchanged m1 m2 evIn ihl' ⟩
      LACMexec m2 evIn
      ≡⟨ ihr' ⟩
      evIn
      ≡⟨ sym (ev+zeroR' DSem3-ctg-zeroLEnv') ⟩
      evIn ev+ Etup-to-LEtup (DSem3 (flip interp (pair l r) ∘ Etup-to-val) a nothing)
      ∎
chad-equiv-DSem3 {Γ = Γ} a evIn ctg@(just (ctgL , ctgR)) (pair l r) = 
  let m1 = snd (interp (D1Etup-to-val a) (chad l)) ctgL .fst
      m2 = snd (interp (D1Etup-to-val a) (chad r)) ctgR .fst
      evL  = LACMexec m1 evIn
      evLR = LACMexec m2 evL
      dsemL = DSem3 (flip interp l ∘ Etup-to-val) a ctgL
      dsemR = DSem3 (flip interp r ∘ Etup-to-val) a ctgR
  in begin
      LACMexec (LACMsequence m1 m2) evIn
      ≡⟨ LACMexec-sequence m1 m2 evIn ⟩
      evLR
      ≡⟨ chad-equiv-DSem3 a evL ctgR r ⟩
      evL ev+ Etup-to-LEtup dsemR
      ≡⟨ ev+congL (chad-equiv-DSem3 a evIn ctgL l)⟩ 
      (evIn ev+ Etup-to-LEtup dsemL) ev+ Etup-to-LEtup dsemR
      ≡⟨ ev+assoc evIn (Etup-to-LEtup dsemL) (Etup-to-LEtup dsemR) ⟩ 
      evIn ev+ (Etup-to-LEtup dsemL ev+ Etup-to-LEtup dsemR)
      ≡⟨ ev+congR (ev+-onEtup-is-plusv dsemL dsemR) ⟩ 
      evIn ev+ Etup-to-LEtup (plusv _ dsemL dsemR .fst)
      ≡⟨ ev+congR (cong Etup-to-LEtup (sym $ DSem3-pair (flip interp l ∘ Etup-to-val) (flip interp r ∘ Etup-to-val) a ctgL ctgR)) ⟩
      evIn ev+ Etup-to-LEtup (DSem3 (flip interp (pair l r) ∘ Etup-to-val) a (just (ctgL , ctgR)))
      ∎
chad-equiv-DSem3 {Γ = Γ} {τ = τ} a evIn ctg (fst' t) =
  let zeroR = zerov (D2τ' _) .fst
      ctg' = just (ctg , zeroR)
      f = flip interp (fst' t) ∘ Etup-to-val
      g = flip interp (snd' t) ∘ Etup-to-val
      dsemL = DSem3 f a ctg
      dsemR = DSem3 g a zeroR
  in begin
  LACMexec (fst (interp (D1Etup-to-val a) (snd' $ chad (fst' t)) ctg)) evIn
  ≡⟨ cong (λ x →  LACMexec (interp (D1Etup-to-val a) (chad t) .snd (just (ctg , x)) .fst) evIn ) (interp-zerot≡zerov _) ⟩
  LACMexec (interp (D1Etup-to-val a) (chad t) .snd ctg' .fst) evIn
  ≡⟨ chad-equiv-DSem3 a evIn ctg' t ⟩
  evIn ev+ Etup-to-LEtup (DSem3 (flip interp t ∘ Etup-to-val) a ctg')
  ≡⟨ ev+congR (trans (cong Etup-to-LEtup (DSem3-pair f g a ctg zeroR)) (sym (ev+-onEtup-is-plusv dsemL dsemR))) ⟩
  evIn ev+ (Etup-to-LEtup dsemL ev+ Etup-to-LEtup dsemR)
  ≡⟨ ev+congR (ev+zeroR' DSem3-ctg-zeroLEnv') ⟩
  evIn ev+ Etup-to-LEtup dsemL
  ∎
chad-equiv-DSem3 {Γ = Γ} {τ = τ} a evIn ctg (snd' t) =
  let zeroL = zerov (D2τ' _) .fst
      ctg' = just (zeroL , ctg)
      f = flip interp (fst' t) ∘ Etup-to-val
      g = flip interp (snd' t) ∘ Etup-to-val
      dsemL = DSem3 f a zeroL
      dsemR = DSem3 g a ctg
  in begin
  LACMexec (fst (interp (D1Etup-to-val a) (snd' $ chad (snd' t)) ctg)) evIn
  ≡⟨ cong (λ x →  LACMexec (interp (D1Etup-to-val a) (chad t) .snd (just (x , ctg)) .fst) evIn ) (interp-zerot≡zerov _) ⟩
  LACMexec (interp (D1Etup-to-val a) (chad t) .snd ctg' .fst) evIn
  ≡⟨ chad-equiv-DSem3 a evIn ctg' t ⟩
  evIn ev+ Etup-to-LEtup (DSem3 (flip interp t ∘ Etup-to-val) a ctg')
  ≡⟨ ev+congR (trans (cong Etup-to-LEtup (DSem3-pair f g a zeroL ctg)) (sym (ev+-onEtup-is-plusv dsemL dsemR))) ⟩
  evIn ev+ (Etup-to-LEtup dsemL ev+ Etup-to-LEtup dsemR)
  ≡⟨ ev+congR (ev+zeroL' DSem3-ctg-zeroLEnv') ⟩
  evIn ev+ Etup-to-LEtup dsemR
  ∎
chad-equiv-DSem3 {Γ = Γ} a evIn ctg (var x) = 
  let idx = convIdx D2τ' x
  in begin
  LACMexec (LACM.add idx ctg) evIn
  ≡⟨ LACMexec-add idx ctg evIn ⟩
  addLEτ idx ctg evIn
  ≡⟨ addLEτ-to-onehot idx ctg evIn ⟩
  evIn ev+ onehot-LEnv (convIdx D2τ' x) ctg
  ≡⟨ ev+congR (sym (DSem3-var x a ctg)) ⟩ 
  evIn ev+ Etup-to-LEtup (DSem3 (flip interp (var x) ∘ Etup-to-val) a ctg)
  ∎
chad-equiv-DSem3 {Γ = Γ} a evIn ctg (let' {σ = σ} {τ = τ} e t) = 
  let e-interp = interp (D1Etup-to-val a) (chad e)
      t-interp-verbose = (interp
              (push (fst e-interp) (push e-interp (D1Etup-to-val a)))
              (sink (WCopy (WSkip WEnd)) (chad t)))
      -- t-interp = interp (push (fst e-interp) (D1Etup-to-val a)) (chad t)
      t-interp = interp (D1Etup-to-val (fst e-interp  , a)) (chad t)
      t-interp-equiv-verbose = (interp-sink-commute-Copy-Skip-End (fst e-interp) (D1Etup-to-val a) (chad t))
      zeroV-verbose = interp (push ctg (push t-interp-verbose (push e-interp empty))) (zerot σ)
      chad-t-verbose = snd t-interp-verbose ctg .fst
      zeroV = zerov (D2τ' σ) .fst
      chad-t = snd t-interp ctg .fst
      m1 = LACM.scope zeroV chad-t
      m2 = (λ x → snd e-interp (fst x) .fst , ℤ.pos 5 Data.Integer.+ snd e-interp (fst x) .snd)
      (outval-s1 , _) , ev-zeroV , _ = LACM.run (LACM.scope zeroV chad-t) evIn
      (outval-s2 , ev-chad-t) = LACMexec chad-t (zeroV , evIn)

      dsemt = Etup-to-LEtup {σ ∷ Γ} $ DSem3 {Etup Pr (σ ∷ Γ)} {τ} (flip interp t ∘ Etup-to-val) (fst e-interp , a) ctg
      dseme = Etup-to-LEtup {Γ} $ DSem3 {Etup Pr Γ} {σ} (flip interp e ∘ Etup-to-val) a (dsemt .fst )
      iht : LACMexec chad-t (zeroV , evIn) ≡ (dsemt .fst , evIn ev+ (dsemt .snd))
      -- iht = trans (chad-equiv-DSem3 (push (fst e-interp) a) (zeroV , evIn) ctg t) 
                  -- (cong₂ (_,_) plusv-zeroL' refl)
      iht = trans (chad-equiv-DSem3 (fst e-interp , a) (zeroV , evIn) ctg t)
                    (cong₂ (_,_) {!   !} {!   !}) 
      ev-m2-a = LACMexec (m2 (outval-s1 , tt) .fst) ev-zeroV
      ev-m2-b = LACMexec (m2 (outval-s2 , tt) .fst) ev-chad-t
      ev-m2-c = LACMexec (m2 ({!   !} , tt) .fst) (evIn ev+ {!   !})
      ev-m2-equiv = cong₂ (λ α β → LACMexec (m2 (α , tt) .fst) β)
  in begin
  LACMexec (LACM.bind (LACM.scope zeroV-verbose chad-t-verbose) m2) evIn
  ≡⟨ cong₂ (λ α β → LACMexec (LACM.bind (LACM.scope α β) m2) evIn) (interp-zerot≡zerov σ) (cong (λ α → snd α ctg .fst) t-interp-equiv-verbose) ⟩
  LACMexec (LACM.bind (LACM.scope zeroV chad-t) m2) evIn
  ≡⟨ LACM.run-bind m1 m2 evIn .fst ⟩
  ev-m2-a
  ≡⟨ (let (_ , α , β) = (LACMexec-scope chad-t zeroV evIn) in ev-m2-equiv β α) ⟩
  ev-m2-b
  ≡⟨ ev-m2-equiv (cong fst iht) (cong snd iht) ⟩
  ev-m2-c
  ≡⟨⟩
  LACMexec (e-interp .snd ({!   !}) .fst) (evIn ev+ {!   !})
  ≡⟨ chad-equiv-DSem3 a (evIn ev+ {!   !}) ({!   !}) e ⟩
  (evIn ev+ {!   !}) ev+ {!   !}
  ≡⟨ ev+assoc evIn ({!   !}) {!   !} ⟩
  evIn ev+ ({!   !})
  ≡⟨ {!   !} ⟩
  evIn ev+ Etup-to-LEtup (DSem3 (flip interp (let' e t) ∘ Etup-to-val) a ctg)
  ∎
chad-equiv-DSem3 {Γ = Γ} a evIn ctg t = {!   !}

chad-equiv-DSem : {Γ : Env Pr} {τ : Typ Pr} 
                  (env : Val Du (D1Γ Γ))       -- the typing environment
                  (evIn : LEtup (map D2τ' Γ))
                  (ctg : Rep (D2τ τ))            -- ctg, some arbitrary (gradient) input
                  (t : Term Pr Γ τ)            -- f(ctg), the original program
                → LACMexec (interp env (chad t) .snd ctg .fst) evIn -- f'(ctg) according to CHAD
                  ≡ evIn ev+ (DSem (flip interp t) env ctg)            -- f'(ctg) according to DSem
chad-equiv-DSem {Γ = Γ} env evIn ctg unit = 
  begin
  LACMexec (fst (interp env (snd' $ chad unit) ctg)) evIn 
  ≡⟨ LACMexec-pure _ evIn ⟩
  evIn
  ≡⟨ sym (ev+zeroR' DSem-ctg-zero') ⟩
  evIn ev+ (DSem (flip interp unit) env ctg) 
  ∎
chad-equiv-DSem {Γ = Γ} env evIn nothing (pair l r) = 
  let m1 = snd (interp env (chad l)) _ .fst
      m2 = snd (interp env (chad r)) _ .fst
      ihl = chad-equiv-DSem env evIn _ l
      ihr = chad-equiv-DSem env evIn _ r
      ihl' = trans ihl (ev+zeroR' DSem-ctg-zero')
      ihr' = trans ihr (ev+zeroR' DSem-ctg-zero')
  in begin
      LACMexec (LACMsequence m1 m2) evIn
      ≡⟨ LACMexec-sequence-unchanged m1 m2 evIn ihl' ⟩
      LACMexec m2 evIn
      ≡⟨ ihr' ⟩
      evIn
      ≡⟨ sym (ev+zeroR' DSem-ctg-zero') ⟩
      evIn ev+ DSem (flip interp (pair l r)) env nothing 
      ∎
chad-equiv-DSem {Γ = Γ} env evIn ctg@(just (ctgL , ctgR)) (pair l r) = 
  let m1 = snd (interp env (chad l)) ctgL .fst
      m2 = snd (interp env (chad r)) ctgR .fst
      evL  = LACMexec m1 evIn
      evLR = LACMexec m2 evL
      dsemL = DSem (flip interp l) env ctgL
      dsemR = DSem (flip interp r) env ctgR
  in begin
      LACMexec (LACMsequence m1 m2) evIn
      ≡⟨ LACMexec-sequence m1 m2 evIn ⟩
      evLR
      ≡⟨ chad-equiv-DSem env evL ctgR r ⟩
      evL ev+ dsemR
      ≡⟨ cong₂ _ev+_ (chad-equiv-DSem env evIn ctgL l) refl ⟩ 
      (evIn ev+ dsemL) ev+ dsemR
      ≡⟨ ev+assoc evIn dsemL dsemR ⟩ 
      evIn ev+ (dsemL ev+ dsemR)
      ≡⟨ cong₂ _ev+_ refl (sym (DSem-pair (flip interp l) (flip interp r) env ctgL ctgR)) ⟩
      evIn ev+ (DSem (flip interp (pair l r)) env (just (ctgL , ctgR)))
      ∎
chad-equiv-DSem {Γ = Γ} {τ = τ} env evIn ctg (fst' t) =
  let zeroR = zerov (D2τ' _) .fst
      ctg' = just (ctg , zeroR)
      f = flip interp (fst' t)
      g = flip interp (snd' t)
      dsemL = DSem f env ctg
      dsemR = DSem g env zeroR
  in begin
  LACMexec (fst (interp env (snd' $ chad (fst' t)) ctg)) evIn
  ≡⟨ cong (λ x →  LACMexec (interp env (chad t) .snd (just (ctg , x)) .fst) evIn ) (interp-zerot≡zerov _) ⟩
  LACMexec (interp env (chad t) .snd ctg' .fst) evIn
  ≡⟨ chad-equiv-DSem env evIn ctg' t ⟩
  evIn ev+ DSem (flip interp t) env ctg'
  ≡⟨ cong₂ _ev+_ refl (DSem-pair f g env ctg zeroR) ⟩
  (evIn ev+ (dsemL ev+ dsemR))
  ≡⟨ cong₂ _ev+_ refl (ev+zeroR' DSem-ctg-zero') ⟩
  evIn ev+ dsemL
  ∎
chad-equiv-DSem {Γ = Γ} env evIn ctg (snd' t) =
  let zeroL = zerov (D2τ' _) .fst
      ctg' = just (zeroL , ctg)
      f = flip interp (fst' t)
      g = flip interp (snd' t)
      dsemL = DSem f env zeroL
      dsemR = DSem g env ctg
  in begin
  LACMexec (fst (interp env (snd' $ chad (snd' t)) ctg)) evIn
  ≡⟨ cong (λ x →  LACMexec (interp env (chad t) .snd (just (x , ctg)) .fst) evIn ) (interp-zerot≡zerov _) ⟩
  LACMexec (interp env (chad t) .snd ctg' .fst) evIn
  ≡⟨ chad-equiv-DSem env evIn ctg' t ⟩
  evIn ev+ DSem (flip interp t) env ctg'
  ≡⟨ cong₂ _ev+_ refl (DSem-pair f g env zeroL ctg) ⟩
  (evIn ev+ (dsemL ev+ dsemR))
  ≡⟨ cong₂ _ev+_ refl (ev+zeroL' DSem-ctg-zero') ⟩
  evIn ev+ dsemR
  ∎
chad-equiv-DSem {Γ = Γ} env evIn ctg (var x) = 
  let idx = convIdx D2τ' x
  in begin
  LACMexec (LACM.add idx ctg) evIn
  ≡⟨ LACMexec-add idx ctg evIn ⟩
  addLEτ idx ctg evIn
  ≡⟨ addLEτ-to-onehot idx ctg evIn ⟩
  evIn ev+ onehot-LEnv (convIdx D2τ' x) ctg
  ≡⟨ cong₂ _ev+_ refl (sym (DSem-var x env ctg)) ⟩ 
  evIn ev+ DSem (flip valprj x) env ctg
  ∎
chad-equiv-DSem {Γ = Γ} env evIn ctg (let' {σ = σ} {τ = τ} e t) = 
  let e-interp = interp env (chad e)
      t-interp-verbose = (interp
              (push (fst e-interp) (push e-interp env))
              (sink (WCopy (WSkip WEnd)) (chad t)))
      t-interp = interp (push (fst e-interp) env) (chad t)
      t-interp-equiv-verbose = interp-sink-commute-Copy-Skip-End (fst e-interp) env (chad t)
      zeroV-verbose = interp (push ctg (push t-interp-verbose (push e-interp empty))) (zerot σ)
      chad-t-verbose = snd t-interp-verbose ctg .fst
      zeroV = zerov (D2τ' σ) .fst
      chad-t = snd t-interp ctg .fst
      m1 = LACM.scope zeroV chad-t
      m2 = (λ x → snd e-interp (fst x) .fst , ℤ.pos 5 Data.Integer.+ snd e-interp (fst x) .snd)
      (outval-s1 , _) , ev-zeroV , _ = LACM.run (LACM.scope zeroV chad-t) evIn
      (outval-s2 , ev-chad-t) = LACMexec chad-t (zeroV , evIn)

      dsemt = DSem (flip interp t) (push (fst e-interp) env) ctg
      dseme = DSem (flip interp e) env (dsemt .fst)
      iht : LACMexec chad-t (zeroV , evIn) ≡ (dsemt .fst , evIn ev+ dsemt .snd)
      iht = trans (chad-equiv-DSem (push (fst e-interp) env) (zeroV , evIn) ctg t) 
                  (cong₂ (_,_) plusv-zeroL' refl)
      -- ev-m2-a ≡ ev-m2-b ≡ ev-m2-c is proven below
      ev-m2-a = LACMexec (m2 (outval-s1 , tt) .fst) ev-zeroV
      ev-m2-b = LACMexec (m2 (outval-s2 , tt) .fst) ev-chad-t
      ev-m2-c = LACMexec (m2 (dsemt .fst , tt) .fst) (evIn ev+ dsemt .snd)
      ev-m2-equiv = cong₂ (λ α β → LACMexec (m2 (α , tt) .fst) β)
  in begin
  LACMexec (LACM.bind (LACM.scope zeroV-verbose chad-t-verbose) m2) evIn
  ≡⟨ cong₂ (λ α β → LACMexec (LACM.bind (LACM.scope α β) m2) evIn) (interp-zerot≡zerov σ) (cong (λ α → snd α ctg .fst) t-interp-equiv-verbose) ⟩
  LACMexec (LACM.bind (LACM.scope zeroV chad-t) m2) evIn
  ≡⟨ LACM.run-bind m1 m2 evIn .fst ⟩
  ev-m2-a
  ≡⟨ (let (_ , α , β) = (LACMexec-scope chad-t zeroV evIn) in ev-m2-equiv β α) ⟩
  ev-m2-b
  ≡⟨ ev-m2-equiv (cong fst iht) (cong snd iht) ⟩
  ev-m2-c
  ≡⟨⟩
  LACMexec (e-interp .snd (dsemt .fst) .fst) (evIn ev+ dsemt .snd)
  ≡⟨ chad-equiv-DSem env (evIn ev+ dsemt .snd) (dsemt .fst) e ⟩
  (evIn ev+ dsemt .snd) ev+ dseme
  ≡⟨ ev+assoc evIn (dsemt .snd) dseme ⟩
  evIn ev+ (dsemt .snd ev+ dseme)
  ≡⟨ cong₂ _ev+_ refl ({! DSem-chain-env ? ? ? ?  !}) ⟩
  evIn ev+ DSem (λ x → interp (push (interp x e) x) t) env ctg
  ∎
chad-equiv-DSem {Γ = Γ} env evIn ctg (prim op t) =
  let chad-t = interp env (chad t)
      d-op-env-verbose = push ctg (push (fst chad-t) (push ctg (push chad-t empty)))
      d-op-verbose = interp d-op-env-verbose (sink (WCopy (WCopy WCut)) (dprim' op))
      d-op-env = push ctg (push (fst chad-t) empty) -- TODO: Probably need to convert fst chad-t to the original function using chad-preserves-primal.
      d-op = interp d-op-env (dprim' op) 
  in begin
  LACMexec (chad-t .snd d-op-verbose .fst) evIn
  ≡⟨ cong (λ α → LACMexec (chad-t .snd α .fst) evIn) (interp-sink-commute-Copy-Copy-Cut ctg (fst chad-t) ((push ctg (push chad-t empty))) (dprim' op)) ⟩
  LACMexec (chad-t .snd d-op .fst) evIn
  ≡⟨ chad-equiv-DSem env evIn d-op t ⟩
  evIn ev+ DSem (flip interp t) env d-op
  ≡⟨ cong₂ _ev+_ refl {!   !} ⟩
  evIn ev+ DSem (flip interp (prim op t)) env ctg
  ∎
chad-equiv-DSem {Γ = Γ} env evIn nothing (inl t) =
  let zero-σ = zerov (D2τ' _) .fst
  in begin
  LACMexec (interp env (chad t) .snd zero-σ .fst) evIn
  ≡⟨ chad-equiv-DSem env evIn zero-σ t ⟩
  evIn ev+ DSem (flip interp t) env zero-σ
  ≡⟨ cong₂ _ev+_ refl DSem-ctg-zero-normalized' ⟩
  evIn ev+ zero-LEnv Γ
  ≡⟨ cong₂ _ev+_ refl (sym DSem-ctg-zero') ⟩
  evIn ev+ DSem (inj₁ ∘ flip interp t) env nothing
  ∎
chad-equiv-DSem {Γ = Γ} env evIn (just (inj₁ ctg)) (inl t) =
  begin
  LACMexec (interp env (chad t) .snd ctg .fst) evIn
  ≡⟨ chad-equiv-DSem env evIn ctg t ⟩
  evIn ev+ DSem (flip interp t) env ctg
  ≡⟨ cong₂ _ev+_ refl (DSem-inj₁ (flip interp t) env ctg) ⟩
  evIn ev+ DSem (inj₁ ∘ flip interp  t) env (just (inj₁ ctg))
  ∎
-- I believe this is a case that is not valid
chad-equiv-DSem {Γ = Γ} env evIn (just (inj₂ ctg)) (inl t) = {! inl t  !}
chad-equiv-DSem {Γ = Γ} env evIn nothing (inr t) =
  let zero-σ = zerov (D2τ' _) .fst
  in begin
  LACMexec (interp env (chad t) .snd zero-σ .fst) evIn
  ≡⟨ chad-equiv-DSem env evIn zero-σ t ⟩
  evIn ev+ DSem (flip interp t) env zero-σ
  ≡⟨ cong₂ _ev+_ refl DSem-ctg-zero-normalized' ⟩
  evIn ev+ zero-LEnv Γ
  ≡⟨ cong₂ _ev+_ refl (sym DSem-ctg-zero') ⟩
  evIn ev+ DSem (inj₂ ∘ flip interp t) env nothing
  ∎
chad-equiv-DSem {Γ = Γ} env evIn (just (inj₁ ctg)) (inr t) = {!   !}
chad-equiv-DSem {Γ = Γ} env evIn (just (inj₂ ctg)) (inr t) =
  begin
  LACMexec (interp env (chad t) .snd ctg .fst) evIn
  ≡⟨ chad-equiv-DSem env evIn ctg t ⟩
  evIn ev+ DSem (flip interp t) env ctg
  ≡⟨ cong₂ _ev+_ refl (DSem-inj₂ (flip interp t) env ctg) ⟩
  evIn ev+ DSem (inj₂ ∘ flip interp  t) env (just (inj₂ ctg))
  ∎
-- TODO: perhaps rewrite this to use a case distinction
chad-equiv-DSem {Γ = Γ} env evIn ctg (case' {σ = σ} {ρ = ρ} c l r) with (interp env (chad c) .fst) | inspect fst (interp env (chad c))
... | inj₁ c' | [ w ] = 
  let interp-chad-c = interp env (chad c)
      w' : fst (interp-chad-c) ≡ inj₁ c'
      w' = w
      cost x = ℤ.pos 6 Data.Integer.+ snd interp-chad-c (just (inj₁ (fst x))) .snd
      zero-σ-verbose = (interp (push ctg (push (interp (push c' (push interp-chad-c env)) (sink (WCopy (WSkip WEnd)) (chad l))) (push interp-chad-c empty))) (zerot σ))
      interp-chad-l-verbose = (interp (push c' (push interp-chad-c env)) (sink (WCopy (WSkip WEnd)) (chad l)))
      zero-σ = zerov (D2τ' σ) .fst
      interp-chad-l = interp (push c' env) (chad l)
      m2 = (λ x → interp-chad-c .snd (just (inj₁ (fst x))) .fst , cost x)

      (outval-s1 , tt) , ev-s1 , _ = LACM.run (LACM.scope zero-σ (interp-chad-l .snd ctg .fst)) evIn
      tt , (outval-s2 , ev-s2) , _ = LACM.run (interp-chad-l .snd ctg .fst) (zero-σ , evIn)
      lemma-equiv = cong₂ (λ α β → LACMexec (m2 (α , tt) . fst) β)

      dseml = DSem (flip interp l) (push c' env) ctg
      ihl : LACMexec (interp-chad-l .snd ctg .fst) (zero-σ , evIn) ≡ (dseml .fst , evIn ev+ dseml .snd)
      ihl = trans (chad-equiv-DSem (push c' env) ( zero-σ , evIn) ctg l)
                   (cong₂ (_,_) plusv-zeroL' refl)

      foo = {! ihl  !}
  in begin
  LACMexec (LACM.bind (LACM.scope zero-σ-verbose (interp-chad-l-verbose .snd ctg .fst)) m2) evIn
  ≡⟨ cong₂ (λ α β → LACMexec (LACM.bind (LACM.scope α (β .snd ctg .fst)) m2) evIn)
           (interp-zerot≡zerov σ) (interp-sink-commute-Copy-Skip-End c' env (chad l)) ⟩
  LACMexec (LACM.bind (LACM.scope zero-σ (interp-chad-l .snd ctg .fst)) m2) evIn
  ≡⟨ LACM.run-bind (LACM.scope zero-σ (interp-chad-l .snd ctg .fst)) m2 evIn .fst ⟩
  LACMexec (m2 (outval-s1 , tt) . fst) ev-s1
  ≡⟨ (let _ , a , b , _ = LACM.run-scope (interp-chad-l .snd ctg .fst) zero-σ evIn in lemma-equiv a b) ⟩
  LACMexec (m2 (outval-s2 , tt) . fst) ev-s2
  ≡⟨ lemma-equiv (cong fst ihl) (cong snd ihl) ⟩
  LACMexec (m2 (dseml .fst , tt) . fst) (evIn ev+ dseml .snd)
  ≡⟨⟩
  LACMexec (interp-chad-c .snd (just (inj₁ (dseml .fst))) .fst) (evIn ev+ dseml .snd)
  ≡⟨ chad-equiv-DSem env (evIn ev+ dseml .snd) (just (inj₁ ((dseml .fst)))) c ⟩
  (evIn ev+ dseml .snd) ev+ DSem (flip interp c) env (just (inj₁ (dseml .fst))) 
  ≡⟨ ev+assoc evIn (dseml .snd) _ ⟩
  evIn ev+ (dseml .snd ev+ DSem (flip interp c) env (just (inj₁ (dseml .fst))))
  ≡⟨ {! dseml   !} ⟩
  (evIn ev+
      DSem (λ x → ((λ { (inj₁ y) → interp (push y x) l ; (inj₂ y) → interp (push y x) r }) (interp x c))) env ctg)
  ∎
... | inj₂ c' | [ w ] = {! w  !}

