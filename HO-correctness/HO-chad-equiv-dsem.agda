module HO-correctness.HO-chad-equiv-dsem where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)
open import Level using (Level)

open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; map; _∷_; []; foldr; foldl; zipWith)
open import Function.Base using (id; _$_; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; dcong₂; subst; trans; cong; cong₂; _≗_)

open import spec hiding (LR)
open import spec.LACM as LACM
open import spec.HL

open import HO-correctness.dsem
open import HO-correctness.lemmas.LinRepDense-is-comm-monoid
open import HO-correctness.dense-rep
open import HO-correctness.logical-relation
open import HO-correctness.lemmas.trivial-equivalences
open import HO-correctness.lemmas.projection-in-relation
open import HO-correctness.lemmas.basics-relation
open import HO-correctness.fundamental-lemma

LR-chad : {Γ : Env Pr} {τ : Typ Pr}
    → let σ = ET Pr Γ 
          LΓ = map D2τ' Γ
    in (isRd : Is-ℝᵈ σ)
    → (t : Term Pr Γ τ)
    → (evIn : LETs LΓ)
    → Rep (D1τ σ) → Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))
LR-chad {Γ = Γ} isRd t evIn x = 
    let val = ET-to-val (ET-D1τ-distr₁ Γ x)
        (a , b) = interp (chad t) val
    in a , (λ ctg → LETd-to-ET (LETs2d {map D2τ' Γ} (LACM.exec (b ctg .fst) evIn)))

ValIdProjections :  (Γ : Env Pr) → (q : Is-ℝᵈ (ET Pr Γ)) 
    → (G : Env Pr) → Lens (ET Pr Γ) (ET Pr G) q
    → HL G (λ τ → Lens (ET Pr Γ) τ q)
ValIdProjections Γ q [] l = tt
ValIdProjections Γ q (τ ∷ G) l = lensTakeFst l , ValIdProjections Γ q G (lensTakeSnd l)

IdProjectionToPrecond : { Γ : Env Pr } → (isRd : Is-ℝᵈ (ET Pr Γ) )
    → (τ : Typ Pr) → (L : Lens (ET Pr Γ) τ isRd )
    → precond isRd τ
IdProjectionToPrecond {Γ} isRd τ l = 
    ((project l) , (project'LR l)) , (projectInLR (ET Pr Γ) τ isRd l)

identityPrecond : (Γ : Env Pr) → (isRd : Is-ℝᵈ (ET Pr Γ) ) → HL Γ (precond isRd)
identityPrecond Γ isRd =
    let lenses =  ValIdProjections Γ isRd Γ (LensId (ET Pr Γ) isRd)
    in HL-map (IdProjectionToPrecond isRd) lenses

chad-in-LR : {σ τ : Typ Pr}
    → let Γ = (σ ∷ [])
      in (isRd : Is-ℝᵈ (ET Pr Γ))
    → (t : Term Pr Γ τ)
    → LR (ET Pr Γ) isRd τ (interp t ∘ ET-to-val) (LR-chad isRd t (zero-LETs Γ))
chad-in-LR {σ} {τ} isRd t = 
    let Γ = σ ∷ []
        input = identityPrecond Γ isRd
        funLemma = fundamental-lemma Γ τ isRd input t
        equiv = (λ x → refl) , (λ x → equiv₁ x , (λ ctg → equiv₂ x ctg))
        ext = LR-extensionality isRd (FL-f isRd input t) (FL-f' isRd input t) (interp t ∘ ET-to-val) (LR-chad isRd t (zero-LETs Γ)) equiv funLemma
    in ext
    where equiv₁ : (x : Rep (D1τ σ) × ⊤) → _
          equiv₁ (x , tt) = cong (λ a → interp (chad t) (push a empty) .fst) (lemma-primal₂ (fst isRd) x)
          equiv₂ : (x : Rep (D1τ σ) × ⊤) → (ctg : LinRep (D2τ' τ)) → _
          equiv₂ (x , tt) ctg = cong₂ _,_ 
                                (trans plusvDense-zeroR' 
                                    (cong (λ a → sparse2dense (LACM.exec (interp (chad t) (push a empty) .snd ctg .fst) (zerov (D2τ' σ) .fst , tt) .fst)) 
                                        (lemma-primal₂ (fst isRd) x))) refl

LR-chad-equiv-DSem : {σ τ : Typ Pr } 
    → let Γ = σ ∷ []
    in (q1 : Is-ℝᵈ σ) (q2 : Is-ℝᵈ τ)
    → (t : Term Pr Γ τ)
    → (x : Rep σ)
    → (ctg : LinRep (D2τ' τ))
    → (df : Is-just (DSemᵀ {ET Pr Γ} {τ} (interp t ∘ ET-to-val) (x , tt)))
    → LR-chad (q1 , tt) t (zero-LETs Γ) (to-primal q1 x , tt) .snd ctg
      ≡ to-witness df (sparse2dense ctg) 
LR-chad-equiv-DSem {σ} {τ} q1 q2 t x ctg df =
   let inP = chad-in-LR  (q1 , tt) t
   in sym (inLR-implies-equiv-DSem (q1 , tt) q2 _ _ inP (x , tt) ctg df)

HO-chad-equiv-DSem : {σ τ : Typ Pr } 
    → let Γ = σ ∷ []
    in (q1 : Is-ℝᵈ σ) (q2 : Is-ℝᵈ τ)
    → (t : Term Pr Γ τ)
    → (x : Rep σ)
    → (ctg : LinRep (D2τ' τ))
    → (df : Is-just (DSemᵀ {ET Pr Γ} {τ} (interp t ∘ ET-to-val) (x , tt)))
    → let evIn = zerov (D2τ' σ) .fst , tt
          val = to-primal q1 x , tt
      in sparse2dense (LACM.exec (interp (chad t) (ET-to-val val) .snd ctg .fst) evIn .fst)
         ≡ to-witness df (sparse2dense ctg) .fst
HO-chad-equiv-DSem {σ} {τ} q1 q2 t x ctg df
  = cong fst (LR-chad-equiv-DSem q1 q2 t x ctg df)