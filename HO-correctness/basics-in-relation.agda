module HO-correctness.basics-in-relation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)

open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Function.Base using (id; _$_; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)

open import spec
open import correctness.spec
open import correctness.dsem
open import correctness.lemmas
open import HO-correctness.logical-relation
open import HO-correctness.lemmas
open import HO-correctness.projection


identityInP7 : (σ : Typ Pr) → (isRd : Is-ℝᵈ σ)
            → P7 σ isRd σ id λ x → (x , sparse2dense)
identityInP7 Un isRd = (λ _ → refl) , (λ _ → refl , λ _ → refl)
identityInP7 R isRd = λ x → refl , ans x
  where ans : (x : Float) → (dsem : Is-just (DSemᵀ id x)) → (ctg : Float) → _
        ans x dsem ctg = let (d-id , rule) = DSemᵀ-identity x ctg
                     in sym (trans (DSemᵀ-extensionality id id (λ _ → refl) x dsem d-id ctg) rule)
identityInP7 (σ :* τ) isRd = (l , r , (l' , r')) , (Pσ , Pτ) , (λ _ → refl) 
  ,  λ x → cong₂ _,_ (sym (lemma-primal₂ (fst isRd) (fst x)))
                     (sym (lemma-primal₂ (snd isRd) (snd x))) 
  , ans
  where l  = project (LensFst σ τ σ isRd (LensId σ (fst isRd)))
        r  = project (LensSnd σ τ τ isRd (LensId τ (snd isRd)))
        l' = project'P7 (LensFst σ τ σ isRd (LensId σ (fst isRd)))
        r' = project'P7 (LensSnd σ τ τ isRd (LensId τ (snd isRd)))
        Pσ = projectInP7 (σ :* τ) σ isRd (LensFst σ τ σ isRd (LensId σ (fst isRd)))
        Pτ = projectInP7 (σ :* τ) τ isRd (LensSnd σ τ τ isRd (LensId τ (snd isRd)))
        ans : (ctg : Maybe (LinRep (D2τ' σ) × LinRep (D2τ' τ))) → _
        ans (just ctg) = cong₂ _,_ (sym plusvDense-zeroR') (sym plusvDense-zeroL')
        ans nothing    = refl
