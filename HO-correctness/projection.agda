module HO-correctness.projection where
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

-- Since we generalized ℝᵈ to nested tuples of reals and unit,
-- we need to generalize the concept of projection.

-- Without this generalization, we cannot (or only with great difficulty) proof that:
-- fst, snd and id are in the logical relation.

-- These functions are a specific kind of projection.
-- When trying to directly prove that they belong in the relation,
-- the induction hypthesis will not be strong enough.
-- Ergo, we need to generalize fst, snd and id into projections to proof they belong in the logical-relation.

data Projecting : (σ τ : Typ Pr) → (Is-ℝᵈ σ) → Set where
  ProjectFst : (σ1 σ2 τ : Typ Pr) → (q : Is-ℝᵈ (σ1 :* σ2)) → Projecting σ1 τ (fst q) → Projecting (σ1 :* σ2) τ q
  ProjectSnd : (σ1 σ2 τ : Typ Pr) → (q : Is-ℝᵈ (σ1 :* σ2)) → Projecting σ2 τ (snd q) → Projecting (σ1 :* σ2) τ q
  ProjectDone : ( σ : Typ Pr ) → (q : Is-ℝᵈ σ) → Projecting σ σ q

projecting-preserves-Rd : { σ τ : Typ Pr } → { q : Is-ℝᵈ σ } → Projecting σ τ q → Is-ℝᵈ τ
projecting-preserves-Rd {σ} {τ} {q} (ProjectFst σ1 σ2 .τ .q proj) = projecting-preserves-Rd proj
projecting-preserves-Rd {σ} {τ} {q} (ProjectSnd σ1 σ2 .τ .q proj) = projecting-preserves-Rd proj
projecting-preserves-Rd {σ} {τ} {q} (ProjectDone .σ .q) = q

projectingTakeFst : { σ τ1 τ2 : Typ Pr } → { q : Is-ℝᵈ σ } → Projecting σ (τ1 :* τ2) q → Projecting σ τ1 q
projectingTakeFst {σ} {τ1} {τ2} {q} (ProjectFst σ1 σ2 .(τ1 :* τ2) .q proj) = ProjectFst σ1 σ2 τ1 q (projectingTakeFst proj)
projectingTakeFst {σ} {τ1} {τ2} {q} (ProjectSnd σ1 σ2 .(τ1 :* τ2) .q proj) = ProjectSnd σ1 σ2 τ1 q (projectingTakeFst proj)
projectingTakeFst {σ} {τ1} {τ2} {q} (ProjectDone .(τ1 :* τ2) .q) = ProjectFst τ1 τ2 τ1 q (ProjectDone τ1 (fst q))

projectingTakeSnd : { σ τ1 τ2 : Typ Pr } → { q : Is-ℝᵈ σ } → Projecting σ (τ1 :* τ2) q → Projecting σ τ2 q
projectingTakeSnd {σ} {τ1} {τ2} {q} (ProjectFst σ1 σ2 .(τ1 :* τ2) .q proj) = ProjectFst σ1 σ2 τ2 q (projectingTakeSnd proj)
projectingTakeSnd {σ} {τ1} {τ2} {q} (ProjectSnd σ1 σ2 .(τ1 :* τ2) .q proj) = ProjectSnd σ1 σ2 τ2 q (projectingTakeSnd proj)
projectingTakeSnd {σ} {τ1} {τ2} {q} (ProjectDone .(τ1 :* τ2) .q) = ProjectSnd τ1 τ2 τ2 q (ProjectDone τ2 (snd q))

project : { σ τ : Typ Pr } → { q : Is-ℝᵈ σ } → Projecting σ τ q → Rep σ → Rep τ
project {σ} {τ} {q} (ProjectFst σ1 σ2 .τ .q proj) x = project {σ1} {τ} { fst q } proj (fst x)
project {σ} {τ} {q} (ProjectSnd σ1 σ2 .τ .q proj) x = project {σ2} {τ} { snd q } proj (snd x)
project {σ} {τ} {q} (ProjectDone .σ .q) x = x

projectingTakeFst-lemma : { σ τ1 τ2 : Typ Pr } → { q : Is-ℝᵈ σ } → ( proj : Projecting σ (τ1 :* τ2) q )
                          → (x : Rep σ) → project proj x .fst ≡ project (projectingTakeFst proj) x
projectingTakeFst-lemma (ProjectFst σ1 σ2 .(_ :* _) _ proj) x = projectingTakeFst-lemma proj (fst x)
projectingTakeFst-lemma (ProjectSnd σ1 σ2 .(_ :* _) _ proj) x = projectingTakeFst-lemma proj (snd x)
projectingTakeFst-lemma (ProjectDone .(_ :* _) _) x = refl

projectingTakeSnd-lemma : { σ τ1 τ2 : Typ Pr } → { q : Is-ℝᵈ σ } → ( proj : Projecting σ (τ1 :* τ2) q )
                          → (x : Rep σ) → project proj x .snd ≡ project (projectingTakeSnd proj) x
projectingTakeSnd-lemma (ProjectFst σ1 σ2 .(_ :* _) _ proj) x = projectingTakeSnd-lemma proj (fst x)
projectingTakeSnd-lemma (ProjectSnd σ1 σ2 .(_ :* _) _ proj) x = projectingTakeSnd-lemma proj (snd x)
projectingTakeSnd-lemma (ProjectDone .(_ :* _) _) x = refl

project' : { σ τ : Typ Pr } → { q : Is-ℝᵈ σ } → Projecting σ τ q
          → (ctg : LinRep (D2τ' τ)) → LinRepDense (D2τ' σ)
project' {σ} {τ} {q} (ProjectFst σ1 σ2 .τ .q proj) ctg = project' proj ctg , (zerovDense (D2τ' σ2))
project' {σ} {τ} {q} (ProjectSnd σ1 σ2 .τ .q proj) ctg = (zerovDense (D2τ' σ1)) , project' proj ctg
project' {σ} {τ} {q} (ProjectDone .σ .q) ctg = sparse2dense ctg


project'P7 : { σ τ : Typ Pr } → { q : Is-ℝᵈ σ } → Projecting σ τ q → Rep σ 
    → Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))
project'P7 {σ} {τ} {q} proj x = (primal τ (project proj x)) , project' proj

project'-zero-lemma : {σ τ : Typ Pr} → {isRd : Is-ℝᵈ σ} → (proj : Projecting σ τ isRd)
    → (x : LinRep (D2τ' τ)) → sparse2dense x ≡ zerovDense (D2τ' τ) → project' proj x ≡ zerovDense (D2τ' σ)
project'-zero-lemma (ProjectFst σ1 σ2 _ _ proj) x w = cong₂ _,_ (project'-zero-lemma proj x w) refl
project'-zero-lemma (ProjectSnd σ1 σ2 _ _ proj) x w = cong₂ _,_ refl (project'-zero-lemma proj x w)
project'-zero-lemma (ProjectDone _ _) x w = w

project'-plus-lemma : {σ τ1 τ2 : Typ Pr} → {isRd : Is-ℝᵈ σ} → (proj : Projecting σ (τ1 :* τ2) isRd) 
    → (x : LinRep (D2τ' τ1) × LinRep (D2τ' τ2))
    → project' proj (just x) ≡ plusvDense (D2τ' σ) (project' (projectingTakeFst proj) (fst x)) 
                                                   (project' (projectingTakeSnd proj) (snd x))
project'-plus-lemma (ProjectFst σ1 σ2 .(_ :* _) _ proj) x 
  = cong₂ _,_ (project'-plus-lemma proj x) (sym plusvDense-zeroL')
project'-plus-lemma (ProjectSnd σ1 σ2 .(_ :* _) _ proj) x 
  = cong₂ _,_ (sym plusvDense-zeroL') (project'-plus-lemma proj x)
project'-plus-lemma (ProjectDone .(_ :* _) _) x 
  = cong₂ _,_ (sym plusvDense-zeroR') (sym plusvDense-zeroL')

project-dsem : {σ τ : Typ Pr} → {isRd : Is-ℝᵈ σ}
    → (proj : Projecting σ τ isRd)
    → (x : Rep σ) → (ctg : LinRep (D2τ' τ))
    → Σ (Is-just (DSemᵀ {σ} {τ} (project proj) x))
        (λ df → to-witness df (sparse2dense ctg) ≡ project' proj ctg)
project-dsem {τ = τ} (ProjectFst σ1 σ2 _ _ proj) x ctg
  = let (d-proj  , rule-proj ) = project-dsem proj (fst x) ctg
        (d-fst   , rule-fst  ) = DSemᵀ-fst {σ1} {σ2} x (to-witness d-proj (sparse2dense ctg))
        (d-chain , rule-chain) = DSemᵀ-chain {σ1 :* σ2} {σ1} {τ} (project proj) fst x d-proj d-fst (sparse2dense ctg)
    in d-chain , trans rule-chain (trans rule-fst (cong₂ _,_ rule-proj refl))
project-dsem {τ = τ} (ProjectSnd σ1 σ2 _ _ proj) x ctg 
  = let (d-proj  , rule-proj ) = project-dsem proj (snd x) ctg
        (d-snd   , rule-snd  ) = DSemᵀ-snd {σ1} {σ2} x (to-witness d-proj (sparse2dense ctg))
        (d-chain , rule-chain) = DSemᵀ-chain {σ1 :* σ2} {σ2} {τ} (project proj) snd x d-proj d-snd (sparse2dense ctg)
    in d-chain , trans rule-chain (trans rule-snd (cong₂ _,_ refl rule-proj))
project-dsem (ProjectDone _ _) x ctg 
  = DSemᵀ-identity x (sparse2dense ctg) 

project-dsem-lemma : {σ τ : Typ Pr} → {isRd : Is-ℝᵈ σ} → (proj : Projecting σ τ isRd) 
    → (x : Rep σ)
    → (dsem : Is-just (DSemᵀ {σ} {τ} (project proj) x))
    → (ctg : LinRep (D2τ' τ))
    →  project' proj ctg ≡ to-witness dsem (sparse2dense ctg)
project-dsem-lemma proj x dsem ctg
  = let (d-proj , rule) = project-dsem proj x ctg
        ext = DSemᵀ-extensionality (project proj) (project proj) (λ _ → refl) x dsem d-proj (sparse2dense ctg)
    in trans (sym rule) (sym ext)


-- projectInP7 : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ) 
--     → (proj : Projecting σ τ isRd)
--     → P7 σ isRd τ (project proj) (project'P7 proj)
-- projectInP7 σ τ isRd proj
--   with projecting-preserves-Rd proj -- needed to convince agda that the non-Rd cases are impossible
-- -- First
-- projectInP7 (σ1 :* σ2) Un isRd (ProjectFst .σ1 .σ2 .Un .isRd proj) | _ 
--   = (λ x → refl) , (λ _ → refl , λ ctg → cong₂ _,_ (project'-zero-lemma proj tt refl) refl)
-- projectInP7 (σ1 :* σ2) R isRd PROJ@(ProjectFst .σ1 .σ2 .R .isRd proj) | _ 
--   = λ x → refl , λ dsem → λ ctg → project-dsem-lemma PROJ x dsem ctg
-- projectInP7 (σ1 :* σ2) (τ1 :* τ2) isRd PROJ@(ProjectFst .σ1 .σ2 .(τ1 :* τ2) .isRd proj) | _ 
--   = (l , (r , (l' , r'))) , ((pl , pr) 
--   , (λ x → cong₂ _,_ (projectingTakeFst-lemma proj (fst x)) (projectingTakeSnd-lemma proj (fst x))) , 
--   λ y → (cong₂ _,_ (cong (primal τ1) (projectingTakeFst-lemma proj (fst y))) 
--                      (cong (primal τ2) (projectingTakeSnd-lemma proj (fst y)))) , 
--   ans y)
--   where l  = project     {σ1 :* σ2} {τ1} {isRd} (projectingTakeFst PROJ)
--         l' = project'P7  {σ1 :* σ2} {τ1} {isRd} (projectingTakeFst PROJ)
--         pl = projectInP7 (σ1 :* σ2)  τ1   isRd  (projectingTakeFst PROJ)
--         r  = project     {σ1 :* σ2} {τ2} {isRd} (projectingTakeSnd PROJ)
--         r' = project'P7  {σ1 :* σ2} {τ2} {isRd} (projectingTakeSnd PROJ)
--         pr = projectInP7 (σ1 :* σ2)  τ2   isRd  (projectingTakeSnd PROJ)
--         ans : (y : Rep σ1 × Rep σ2) → (ctg : Maybe (LinRep (D2τ' τ1) × LinRep (D2τ' τ2))) → _
--         ans y (just ctg) = cong₂ _,_ (project'-plus-lemma proj ctg) (sym plusvDense-zeroL')
--         ans y nothing = cong₂ _,_ (project'-zero-lemma proj nothing refl) refl
-- -- Second
-- projectInP7 (σ1 :* σ2) Un isRd (ProjectSnd .σ1 .σ2 .Un .isRd proj) | _ 
--   = (λ x → refl) , (λ _ → refl , (λ ctg → cong₂ _,_ refl (project'-zero-lemma proj tt refl)))
-- projectInP7 (σ1 :* σ2) R isRd PROJ@(ProjectSnd .σ1 .σ2 .R .isRd proj) | _ 
--   = λ x → refl , (λ dsem → λ ctg → project-dsem-lemma PROJ x dsem ctg)
-- projectInP7 (σ1 :* σ2) (τ1 :* τ2) isRd PROJ@(ProjectSnd .σ1 .σ2 .(τ1 :* τ2) .isRd proj) | _ 
--   = (l , (r , (l' , r'))) , (pl , pr) , 
--     ((λ x → cong₂ _,_ (projectingTakeFst-lemma proj (snd x)) (projectingTakeSnd-lemma proj (snd x))) 
--     , λ y → (cong₂ _,_ (cong (primal τ1) (projectingTakeFst-lemma proj (snd y))) 
--                          (cong (primal τ2) (projectingTakeSnd-lemma proj (snd y)))) ,
--     ans y)
--   where l  = project     {σ1 :* σ2} {τ1} {isRd} (projectingTakeFst PROJ)
--         l' = project'P7  {σ1 :* σ2} {τ1} {isRd} (projectingTakeFst PROJ)
--         pl = projectInP7 (σ1 :* σ2)  τ1   isRd  (projectingTakeFst PROJ)
--         r  = project     {σ1 :* σ2} {τ2} {isRd} (projectingTakeSnd PROJ)
--         r' = project'P7  {σ1 :* σ2} {τ2} {isRd} (projectingTakeSnd PROJ)
--         pr = projectInP7 (σ1 :* σ2)  τ2   isRd  (projectingTakeSnd PROJ)
--         ans : (y : Rep σ1 × Rep σ2) → (ctg : Maybe (LinRep (D2τ' τ1) × LinRep (D2τ' τ2))) → _
--         ans y (just ctg) = cong₂ _,_ (sym plusvDense-zeroL') (project'-plus-lemma proj ctg)
--         ans y nothing = cong₂ _,_ refl (project'-zero-lemma proj nothing refl)
-- -- Identity 
-- projectInP7 Un Un isRd (ProjectDone .Un tt) | _ 
--   = (λ _ → refl) , (λ _ → refl , (λ _ → refl))
-- projectInP7 R R isRd (ProjectDone .R tt) | _ 
--   = λ x → refl , λ dsem → λ ctg → project-dsem-lemma (ProjectDone R tt) x dsem ctg -- HOLDS via identity postulation
-- projectInP7 (σ1 :* σ2) (τ1 :* τ2) isRd (ProjectDone .(σ1 :* σ2) .isRd) | _ 
--   = (l , (r , (l' , r'))) , ((pl , pr) , 
--     ((λ x → refl) , λ x → refl , ans x))
--   where l  = project     {σ1 :* σ2} {σ1} {isRd} (ProjectFst σ1 σ2 σ1 isRd (ProjectDone σ1 (fst isRd)))
--         l' = project'P7  {σ1 :* σ2} {τ1} {isRd} (ProjectFst σ1 σ2 σ1 isRd (ProjectDone σ1 (fst isRd)))
--         pl = projectInP7 (σ1 :* σ2)  τ1   isRd  (ProjectFst σ1 σ2 σ1 isRd (ProjectDone σ1 (fst isRd)))
--         r  = project     {σ1 :* σ2} {τ2} {isRd} (ProjectSnd σ1 σ2 σ2 isRd (ProjectDone σ2 (snd isRd)))
--         r' = project'P7  {σ1 :* σ2} {τ2} {isRd} (ProjectSnd σ1 σ2 σ2 isRd (ProjectDone σ2 (snd isRd)))
--         pr = projectInP7 (σ1 :* σ2)  τ2   isRd  (ProjectSnd σ1 σ2 σ2 isRd (ProjectDone σ2 (snd isRd)))
--         ans : (x : Rep σ1 × Rep σ2) → (ctg : Maybe (LinRep (D2τ' σ1) × LinRep (D2τ' σ2))) → _
--         ans x (just ctg) = cong₂ _,_ (sym plusvDense-zeroR') (sym plusvDense-zeroL')
--         ans x nothing = refl