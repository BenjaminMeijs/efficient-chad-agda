{-# OPTIONS --allow-unsolved-metas #-}
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

private
    trans₂ : {A : Set} {x y a b : A} → x ≡ y → x ≡ a → y ≡ b → a ≡ b
    trans₂ refl refl refl = refl

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


P7-ctg-zero : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → P7 σ isRd τ f f'
    → (x : Rep (D1τ σ)) → (ctg : LinRep (D2τ' τ))
    → (sparse2dense ctg ≡ zerovDense (D2τ' τ))
    → f' x .snd ctg ≡ zerovDense (D2τ' σ)
P7-ctg-zero σ Un isRd f f' p x ctg w = p .snd x .snd tt
P7-ctg-zero σ Inte isRd f f' p x ctg w = p .snd x .snd tt
P7-ctg-zero σ R isRd f f' p x ctg w
  = {! p (un-primal isRd x) .snd ? ctg  !} -- HOLDS based on postulations of dsem
P7-ctg-zero σ (τ1 :* τ2) isRd f f' ((l , r , l' , r') , (pl , pr) , p) x (just ctg) w 
  = trans (p .snd x .snd (just ctg)) 
    (trans (plusvDense-zeroL' {{P7-ctg-zero σ τ1 isRd l l' pl x (ctg .fst) (cong fst w)}}) 
    (P7-ctg-zero σ τ2 isRd r r' pr x (ctg .snd) (cong snd w)))
P7-ctg-zero σ (τ1 :* τ2) isRd f f' ((l , r , l' , r') , (pl , pr) , p) x nothing w 
  = p .snd x .snd nothing
P7-ctg-zero σ (τ1 :+ τ2) isRd f f' p x ctg w = {!   !}
P7-ctg-zero σ (τ1 :-> τ2) isRd F F' ((f , f') , p) x nothing w
  = let g  = {!   !}
        g' = {!   !}
        pg = {!   !}
        (ph , (_ , p')) = p g g' pg
        ih-g = P7-ctg-zero σ τ1 isRd g g' pg
        ih-h = P7-ctg-zero σ τ2 isRd _ _ ph
        v1 = g' x .fst
        ctg2 = zerov (D2τ' τ2) .fst -- Deze weet ik niet zeker
        ctg1 = f' x .fst v1 .snd ctg2 .snd
        ih-f : (f' x .fst v1 .snd ctg2 .fst ≡ nothing) 
               × (sparse2dense ctg1 ≡ zerovDense (D2τ' τ1))
        ih-f = let a = p' x v1 .snd .snd ctg2
                   b = sym (p' x v1 .snd .fst)
               in {! p' x v1 .snd .snd ctg2  !} , {!   !}
              --  trans (cong fst a) {! a  !} , 
                  -- trans (cong (sparse2dense ∘ snd) a) {!   !}
        baz = {! p' x v1 .snd .snd  !}
        bar = {! ih-h  !}
        f'-is-zero : f' x .snd nothing ≡ zerovDense (D2τ' σ)
        f'-is-zero =  trans₂
                        (trans₂ (ih-h x ctg2 (zerov-equiv-zerovDense (D2τ' τ2))) 
                                (plusvDense-zeroR' {{ih-g x ctg1 (snd ih-f)}}) refl) 
                        (cong (f' x .snd) (fst ih-f)) refl
    in trans (sym (p' x v1 .fst nothing )) 
              f'-is-zero
P7-ctg-zero σ (τ1 :-> τ2) isRd F F' ((f , f') , p) x (just ctg) w
  = {! ctg  !}



-- Nested composition
P7∘ : { τ1 τ2 τ3 : Typ Pr } → { isRd : Is-ℝᵈ (τ1 :* τ2)  }
    → (f' : Rep (D1τ τ2) → ( Rep (D1τ τ3) × (LinRep (D2τ' τ3) → LinRepDense (D2τ' τ2))))
    → (g' : Rep (D1τ τ1) → ( Rep (D1τ τ2) × (LinRep (D2τ' τ2) → LinRepDense (D2τ' τ1))))
    → (Rep (D1τ τ1) → ( Rep (D1τ τ3) × (LinRep (D2τ' τ3) → LinRepDense (D2τ' τ1))))
P7∘ {τ1} {τ2} {τ3} {isRd} f' g' 
  = λ x → let a = f' (g' x .fst) 
          in (fst a) , (λ ctg → let b = dense2sparse (snd isRd) (a .snd ctg) 
                                in g' x .snd b)

P7-chain-rule : { τ1 τ2 τ3 : Typ Pr } → { isRd : Is-ℝᵈ (τ1 :* τ2) }
    → (f : Rep τ2 → Rep τ3)
    → (g : Rep τ1 → Rep τ2)
    → (f' : Rep (D1τ τ2) → ( Rep (D1τ τ3) × (LinRep (D2τ' τ3) → LinRepDense (D2τ' τ2))))
    → (g' : Rep (D1τ τ1) → ( Rep (D1τ τ2) × (LinRep (D2τ' τ2) → LinRepDense (D2τ' τ1))))
    → P7 τ2 (snd isRd) τ3 f f'
    → P7 τ1 (fst isRd) τ2 g g'
    → P7 τ1 (fst isRd) τ3 (f ∘ g) (P7∘ {isRd = isRd} f' g')
P7-chain-rule {τ1} {τ2} {Un} {isRd} f g f' g' pf pg
  = (λ _ → refl) , (λ x → refl , λ _ → ans x  )
  where ans : (x : Rep (D1τ τ1)) → _
  -- g' x .snd (dense2sparse (snd isRd) (f' (g' x .fst) .snd tt)) ≡ zerovDense (D2τ' τ1)
        ans x
          rewrite pf .snd (g' x .fst) .snd tt
          = {! pg  !}
P7-chain-rule {τ1} {τ2} {Inte} {isRd} f g f' g' pf pg
  = (λ x → pf .fst (g x)) , (λ x → {!   !} , (λ ctg → {!   !}))
P7-chain-rule {τ1} {τ2} {R} {isRd} f g f' g' pf pg
  = {!   !}
P7-chain-rule {τ1} {τ2} {τ3 :* τ4} {isRd} f g f' g' pf pg
  = {!   !}
P7-chain-rule {τ1} {τ2} {τ3 :+ τ4} {isRd} f g f' g' pf pg = {!   !}
P7-chain-rule {τ1} {τ2} {τ3 :-> τ4} {isRd} f g f' g' pf pg
  = {!   !}