module HO-correctness.projection where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)

open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Function.Base using (id; _$_; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)

open import spec hiding (LR)
open import correctness.spec
open import correctness.dsem
open import correctness.lemmas
open import HO-correctness.logical-relation
open import HO-correctness.lemmas

-- Since we generalized ℝᵈ to nested tuples of reals and unit,
-- we need to generalize the concept of projection.

-- Without this generalization, we cannot (or only with great difficulty) proof that:
-- fst, snd and id are in the logical relation.

-- These functions are a specific kind of projection.
-- When trying to directly prove that they belong in the relation,
-- the induction hypthesis will not be strong enough.
-- Ergo, we need to generalize fst, snd and id into projections to proof they belong in the logical-relation.

-- We defunctionalize projection.
-- All projections we require can be described by a Lens
-- Using this, we can do induction on all projections.
data Lens : ∀ {tag} → (σ τ : Typ tag) → (Is-ℝᵈ σ) → Set where
  LensFst : ∀ {tag} → (σ1 σ2 τ : Typ tag) → (q : Is-ℝᵈ (σ1 :* σ2)) → Lens σ1 τ (fst q) → Lens (σ1 :* σ2) τ q
  LensSnd : ∀ {tag} → (σ1 σ2 τ : Typ tag) → (q : Is-ℝᵈ (σ1 :* σ2)) → Lens σ2 τ (snd q) → Lens (σ1 :* σ2) τ q
  LensId  : ∀ {tag} → (σ : Typ tag ) → (q : Is-ℝᵈ σ) → Lens σ σ q

project : ∀ {tag} { σ τ : Typ tag } → { q : Is-ℝᵈ σ } → Lens σ τ q → Rep σ → Rep τ
project {tag} {σ} {τ} {q} (LensFst σ1 σ2 .τ .q proj) x = project {tag} {σ1} {τ} { fst q } proj (fst x)
project {tag} {σ} {τ} {q} (LensSnd σ1 σ2 .τ .q proj) x = project {tag} {σ2} {τ} { snd q } proj (snd x)
project {tag} {σ} {τ} {q} (LensId .σ .q) x = x

-- Agda needs some convincing that for all Lenses,
--    which describe a projection on ℝᵈ,
--    the resulting value is also in ℝᵈ
Lens-preserves-ℝᵈ : ∀ {tag} → { σ τ : Typ tag } → { q : Is-ℝᵈ σ } → Lens σ τ q → Is-ℝᵈ τ
Lens-preserves-ℝᵈ {_} {σ} {τ} {q} (LensFst σ1 σ2 .τ .q proj) = Lens-preserves-ℝᵈ proj
Lens-preserves-ℝᵈ {_} {σ} {τ} {q} (LensSnd σ1 σ2 .τ .q proj) = Lens-preserves-ℝᵈ proj
Lens-preserves-ℝᵈ {_} {σ} {τ} {q} (LensId .σ .q) = q

-- We can put a fst or snd into a lens:
--  i.e. apply fst/snd to the result,
--  (instead of adding extra data to the input)
lensTakeFst : ∀ {tag} → { σ τ1 τ2 : Typ tag } → { q : Is-ℝᵈ σ } → Lens σ (τ1 :* τ2) q → Lens σ τ1 q
lensTakeFst {_} {σ} {τ1} {τ2} {q} (LensFst σ1 σ2 .(τ1 :* τ2) .q proj) = LensFst σ1 σ2 τ1 q (lensTakeFst proj)
lensTakeFst {_} {σ} {τ1} {τ2} {q} (LensSnd σ1 σ2 .(τ1 :* τ2) .q proj) = LensSnd σ1 σ2 τ1 q (lensTakeFst proj)
lensTakeFst {_} {σ} {τ1} {τ2} {q} (LensId .(τ1 :* τ2) .q) = LensFst τ1 τ2 τ1 q (LensId τ1 (fst q))

lensTakeSnd : ∀ {tag} → { σ τ1 τ2 : Typ tag } → { q : Is-ℝᵈ σ } → Lens σ (τ1 :* τ2) q → Lens σ τ2 q
lensTakeSnd {_} {σ} {τ1} {τ2} {q} (LensFst σ1 σ2 .(τ1 :* τ2) .q proj) = LensFst σ1 σ2 τ2 q (lensTakeSnd proj)
lensTakeSnd {_} {σ} {τ1} {τ2} {q} (LensSnd σ1 σ2 .(τ1 :* τ2) .q proj) = LensSnd σ1 σ2 τ2 q (lensTakeSnd proj)
lensTakeSnd {_} {σ} {τ1} {τ2} {q} (LensId .(τ1 :* τ2) .q) = LensSnd τ1 τ2 τ2 q (LensId τ2 (snd q))

-- Proofs that applying a fst/snd to the result via lensTakeFst/lensTakeSnd
-- is equivalent to just applying fst/snd to the result.
lensTakeFst-lemma : ∀ {tag} → { σ τ1 τ2 : Typ tag } → { q : Is-ℝᵈ σ } → ( proj : Lens σ (τ1 :* τ2) q )
    → (x : Rep σ) → project proj x .fst ≡ project (lensTakeFst proj) x
lensTakeFst-lemma (LensFst σ1 σ2 .(_ :* _) _ proj) x = lensTakeFst-lemma proj (fst x)
lensTakeFst-lemma (LensSnd σ1 σ2 .(_ :* _) _ proj) x = lensTakeFst-lemma proj (snd x)
lensTakeFst-lemma (LensId .(_ :* _) _) x = refl

lensTakeSnd-lemma : ∀ {tag} → { σ τ1 τ2 : Typ tag } → { q : Is-ℝᵈ σ } → ( proj : Lens σ (τ1 :* τ2) q )
    → (x : Rep σ) → project proj x .snd ≡ project (lensTakeSnd proj) x
lensTakeSnd-lemma (LensFst σ1 σ2 .(_ :* _) _ proj) x = lensTakeSnd-lemma proj (fst x)
lensTakeSnd-lemma (LensSnd σ1 σ2 .(_ :* _) _ proj) x = lensTakeSnd-lemma proj (snd x)
lensTakeSnd-lemma (LensId .(_ :* _) _) x = refl

lens-primal : {σ τ : Typ Pr} → {q : Is-ℝᵈ σ} → (L : Lens σ τ q) → (Lens (D1τ σ) (D1τ τ) (primal-Is-ℝᵈ q))
lens-primal {σ} {τ} {q} (LensFst σ1 σ2 _ _ L) = LensFst (D1τ σ1) (D1τ σ2) (D1τ τ) (primal-Is-ℝᵈ q) (lens-primal L)
lens-primal {σ} {τ} {q} (LensSnd σ1 σ2 _ _ L) = LensSnd (D1τ σ1) (D1τ σ2) (D1τ τ) (primal-Is-ℝᵈ q) (lens-primal L)
lens-primal {σ} {τ} {q} (LensId _ _) = LensId (D1τ σ) (primal-Is-ℝᵈ q)

lens-primal-lemma : {σ τ : Typ Pr} → {q : Is-ℝᵈ σ} 
    → { q2 : Is-ℝᵈ τ }
    → (L : Lens σ τ q) 
    → (x : Rep (D1τ σ))
    → project (lens-primal L) x
    ≡ to-primal q2 (project L (un-primal q x))
lens-primal-lemma (LensFst σ1 σ2 _ _ L) xs = lens-primal-lemma L (fst xs)
lens-primal-lemma (LensSnd σ1 σ2 _ _ L) xs = lens-primal-lemma L (snd xs)
lens-primal-lemma {q = q} {q2 = q2} (LensId _ _) xs = 
  sym (trans (cong (λ w → to-primal w (un-primal q xs)) (Is-ℝᵈ-irrel q2 q)) 
             (lemma-primal₂ q xs) )
    

-- The transposed derivative of project
-- Note that this is a 'onehot' encoding,
-- all entries are zero,
--    except for the entry corresponding to projected entry,
--    which gets the value of the cotangent.
project' : { σ τ : Typ Pr } → { q : Is-ℝᵈ σ } → Lens σ τ q
          → (ctg : LinRep (D2τ' τ)) → LinRepDense (D2τ' σ)
project' {σ} {τ} {q} (LensFst σ1 σ2 .τ .q proj) ctg = project' proj ctg , (zerovDense (D2τ' σ2))
project' {σ} {τ} {q} (LensSnd σ1 σ2 .τ .q proj) ctg = (zerovDense (D2τ' σ1)) , project' proj ctg
project' {σ} {τ} {q} (LensId .σ .q) ctg = sparse2dense ctg

-- When the cotangent is zero, the derivative of the projection is also zero
project'-zero-lemma : {σ τ : Typ Pr} → {isRd : Is-ℝᵈ σ} → (proj : Lens σ τ isRd)
    → (ctg : LinRep (D2τ' τ)) → sparse2dense ctg ≡ zerovDense (D2τ' τ) 
    → project' proj ctg ≡ zerovDense (D2τ' σ)
project'-zero-lemma (LensFst σ1 σ2 _ _ proj) x w = cong₂ _,_ (project'-zero-lemma proj x w) refl
project'-zero-lemma (LensSnd σ1 σ2 _ _ proj) x w = cong₂ _,_ refl (project'-zero-lemma proj x w)
project'-zero-lemma (LensId _ _) x w = w

-- The derivative of a projection for a pair is the addition of the derivatives of its subparts.
project'-plus-lemma : {σ τ1 τ2 : Typ Pr} → {isRd : Is-ℝᵈ σ} → (proj : Lens σ (τ1 :* τ2) isRd) 
    → (x : LinRep (D2τ' τ1) × LinRep (D2τ' τ2))
    → project' proj (just x) ≡ plusvDense (D2τ' σ) (project' (lensTakeFst proj) (fst x)) 
                                                   (project' (lensTakeSnd proj) (snd x))
project'-plus-lemma (LensFst σ1 σ2 .(_ :* _) _ proj) x 
  = cong₂ _,_ (project'-plus-lemma proj x) (sym plusvDense-zeroL')
project'-plus-lemma (LensSnd σ1 σ2 .(_ :* _) _ proj) x 
  = cong₂ _,_ (sym plusvDense-zeroL') (project'-plus-lemma proj x)
project'-plus-lemma (LensId .(_ :* _) _) x 
  = cong₂ _,_ (sym plusvDense-zeroR') (sym plusvDense-zeroL')

-- Proof that our given derivative for projection is equivalent to semantic differentiation.
-- Additionally, a proof that projection is always differentiable.
project'-equiv-dsem : {σ τ : Typ Pr} → {isRd : Is-ℝᵈ σ}
    → (proj : Lens σ τ isRd)
    → (x : Rep σ) → (ctg : LinRep (D2τ' τ))
    → Σ (Is-just (DSemᵀ {σ} {τ} (project proj) x))
        (λ df → to-witness df (sparse2dense ctg) ≡ project' proj ctg)
project'-equiv-dsem {τ = τ} (LensFst σ1 σ2 _ _ proj) x ctg
  = let (d-proj  , rule-proj ) = project'-equiv-dsem proj (fst x) ctg
        (d-fst   , rule-fst  ) = DSemᵀ-fst {σ1} {σ2} x (to-witness d-proj (sparse2dense ctg))
        (d-chain , rule-chain) = DSemᵀ-chain {σ1 :* σ2} {σ1} {τ} (project proj) fst x d-proj d-fst (sparse2dense ctg)
    in d-chain , trans rule-chain (trans rule-fst (cong₂ _,_ rule-proj refl))
project'-equiv-dsem {τ = τ} (LensSnd σ1 σ2 _ _ proj) x ctg 
  = let (d-proj  , rule-proj ) = project'-equiv-dsem proj (snd x) ctg
        (d-snd   , rule-snd  ) = DSemᵀ-snd {σ1} {σ2} x (to-witness d-proj (sparse2dense ctg))
        (d-chain , rule-chain) = DSemᵀ-chain {σ1 :* σ2} {σ2} {τ} (project proj) snd x d-proj d-snd (sparse2dense ctg)
    in d-chain , trans rule-chain (trans rule-snd (cong₂ _,_ refl rule-proj))
project'-equiv-dsem (LensId _ _) x ctg 
  = DSemᵀ-identity x (sparse2dense ctg) 

-- Transforming project'-equiv-dsem into a lemma directly usable for the proof that projection is in the logical relation.
project'-dsem-lemma : {σ τ : Typ Pr} → {isRd : Is-ℝᵈ σ} → (proj : Lens σ τ isRd) 
    → (x : Rep σ)
    → Σ (Is-just (DSemᵀ {σ} {τ} (project proj) x))
        (λ dsem  → (ctg : LinRep (D2τ' τ)) 
            → project' proj ctg ≡ to-witness dsem (sparse2dense ctg))
project'-dsem-lemma {τ = τ} proj x
  = let (d-proj , _) = project'-equiv-dsem proj x (zerov (D2τ' τ) .fst)
    in d-proj , (λ ctg →
      let (df , rule) = project'-equiv-dsem proj x ctg
          ext = DSemᵀ-extensionality (project proj) (project proj) (λ _ → refl) x df d-proj (sparse2dense ctg)
      in trans (sym rule) ext)

-- Wrapping the derivative of project to fit in the logical relation
project'LR : { σ τ : Typ Pr } → { q : Is-ℝᵈ σ } → Lens σ τ q
  → Rep (D1τ σ) → Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))
project'LR {σ} {τ} {q} proj x 
  = (to-primal (Lens-preserves-ℝᵈ proj) (project proj (un-primal q x)))
    , project' proj


projectInLR : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ) 
    → (proj : Lens σ τ isRd)
    → LR σ isRd τ (project proj) (project'LR proj)
projectInLR σ τ isRd proj
  with Lens-preserves-ℝᵈ proj -- needed to convince agda that the non-Rd cases are impossible
-- First
projectInLR (σ1 :* σ2) Un isRd (LensFst .σ1 .σ2 .Un .isRd proj) | _ 
  = (λ x → refl) , (λ _ → refl , λ ctg → cong₂ _,_ (project'-zero-lemma proj tt refl) refl)
projectInLR (σ1 :* σ2) R isRd PROJ@(LensFst .σ1 .σ2 .R .isRd proj) | _ 
  = λ x → cong (project proj) (sym (lemma-primal₁ (isRd .fst) (x .fst))) 
    , project'-dsem-lemma PROJ x
projectInLR (σ1 :* σ2) (τ1 :* τ2) isRd PROJ@(LensFst .σ1 .σ2 .(τ1 :* τ2) .isRd proj) | _ 
  = (l , (r , (l' , r'))) , ((pl , pr) 
  , (λ x → cong₂ _,_ (lensTakeFst-lemma proj (fst x)) (lensTakeSnd-lemma proj (fst x))) , 
  λ y → cong₂ _,_ (cong-to-primal (lensTakeFst-lemma proj (un-primal (fst isRd) (fst y)))) 
                  (cong-to-primal (lensTakeSnd-lemma proj (un-primal (fst isRd) (fst y)))) 
        , ans y )
  where l  = project {_} {σ1 :* σ2} {τ1} {isRd} (lensTakeFst PROJ)
        l' = project'LR  {σ1 :* σ2} {τ1} {isRd} (lensTakeFst PROJ)
        pl = projectInLR (σ1 :* σ2)  τ1   isRd  (lensTakeFst PROJ)
        r  = project {_} {σ1 :* σ2} {τ2} {isRd} (lensTakeSnd PROJ)
        r' = project'LR  {σ1 :* σ2} {τ2} {isRd} (lensTakeSnd PROJ)
        pr = projectInLR (σ1 :* σ2)  τ2   isRd  (lensTakeSnd PROJ)
        ans : (y : Rep (D1τ σ1) × Rep (D1τ σ2)) → (ctg : Maybe (LinRep (D2τ' τ1) × LinRep (D2τ' τ2))) → _
        ans y (just ctg) = cong₂ _,_ (project'-plus-lemma proj ctg) (sym plusvDense-zeroL')
        ans y nothing = cong₂ _,_ (project'-zero-lemma proj nothing refl) refl 
-- Second
projectInLR (σ1 :* σ2) Un isRd (LensSnd .σ1 .σ2 .Un .isRd proj) | _ 
  = (λ x → refl) , (λ _ → refl , (λ ctg → cong₂ _,_ refl (project'-zero-lemma proj tt refl)))
projectInLR (σ1 :* σ2) R isRd PROJ@(LensSnd .σ1 .σ2 .R .isRd proj) | _ 
  = λ x → cong (project proj) (sym (lemma-primal₁ (snd isRd) (snd x))) 
    , project'-dsem-lemma PROJ x
projectInLR (σ1 :* σ2) (τ1 :* τ2) isRd PROJ@(LensSnd .σ1 .σ2 .(τ1 :* τ2) .isRd proj) | _ 
  = (l , (r , (l' , r'))) , (pl , pr) , 
    ((λ x → cong₂ _,_ (lensTakeFst-lemma proj (snd x)) (lensTakeSnd-lemma proj (snd x))) 
    , λ y → (cong₂ _,_ (cong-to-primal (lensTakeFst-lemma proj (un-primal (isRd .snd) (snd y)))) 
                       (cong-to-primal (lensTakeSnd-lemma proj (un-primal (isRd .snd) (snd y))))) ,
    ans y)
  where l  = project {_} {σ1 :* σ2} {τ1} {isRd} (lensTakeFst PROJ)
        l' = project'LR  {σ1 :* σ2} {τ1} {isRd} (lensTakeFst PROJ)
        pl = projectInLR (σ1 :* σ2)  τ1   isRd  (lensTakeFst PROJ)
        r  = project {_} {σ1 :* σ2} {τ2} {isRd} (lensTakeSnd PROJ)
        r' = project'LR  {σ1 :* σ2} {τ2} {isRd} (lensTakeSnd PROJ)
        pr = projectInLR (σ1 :* σ2)  τ2   isRd  (lensTakeSnd PROJ)
        ans : (y : Rep (D1τ σ1) × Rep (D1τ σ2)) → (ctg : Maybe (LinRep (D2τ' τ1) × LinRep (D2τ' τ2))) → _
        ans y (just ctg) = cong₂ _,_ (sym plusvDense-zeroL') (project'-plus-lemma proj ctg)
        ans y nothing = cong₂ _,_ refl (project'-zero-lemma proj nothing refl)
-- Identity 
projectInLR Un Un isRd (LensId .Un tt) | _ 
  = (λ _ → refl) , (λ _ → refl , (λ _ → refl))
projectInLR R R isRd (LensId .R tt) | _ 
  = λ x → refl , project'-dsem-lemma (LensId R tt) x
projectInLR (σ1 :* σ2) (τ1 :* τ2) isRd (LensId .(σ1 :* σ2) .isRd) | _ 
  = (l , (r , (l' , r'))) , ((pl , pr) , 
    ((λ x → refl) , λ x → cong₂ _,_ (cong-to-primal {isRd2 = fst isRd} refl) (cong-to-primal {isRd2 = snd isRd} refl) 
      , ans x))
  where l  = project {_} {σ1 :* σ2} {σ1} {isRd} (LensFst σ1 σ2 σ1 isRd (LensId σ1 (fst isRd)))
        l' = project'LR  {σ1 :* σ2} {τ1} {isRd} (LensFst σ1 σ2 σ1 isRd (LensId σ1 (fst isRd)))
        pl = projectInLR (σ1 :* σ2)  τ1   isRd  (LensFst σ1 σ2 σ1 isRd (LensId σ1 (fst isRd)))
        r  = project {_} {σ1 :* σ2} {τ2} {isRd} (LensSnd σ1 σ2 σ2 isRd (LensId σ2 (snd isRd)))
        r' = project'LR  {σ1 :* σ2} {τ2} {isRd} (LensSnd σ1 σ2 σ2 isRd (LensId σ2 (snd isRd)))
        pr = projectInLR (σ1 :* σ2)  τ2   isRd  (LensSnd σ1 σ2 σ2 isRd (LensId σ2 (snd isRd)))
        ans : (x : Rep (D1τ σ1) × Rep (D1τ σ2)) → (ctg : Maybe (LinRep (D2τ' σ1) × LinRep (D2τ' σ2))) → _
        ans x (just ctg) = cong₂ _,_ (sym plusvDense-zeroR') (sym plusvDense-zeroL')
        ans x nothing = refl