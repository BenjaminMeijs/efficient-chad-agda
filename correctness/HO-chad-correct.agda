module correctness.HO-chad-correct where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)

open import Data.Empty using (⊥)
open import Data.List using (_∷_; map; [])
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_]; isInj₁; isInj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Function.Base using (id; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_)

open import spec
open import correctness.spec
open import correctness.dsyn-defined
open import correctness.chad-ctg-zero
open import correctness.lemmas
open import correctness.dsem

-- τ is a nested tuple of Rs
Is-ℝᵈ : ( τ : Typ Pr ) → Set
Is-ℝᵈ Un = ⊤
Is-ℝᵈ Inte = ⊥
Is-ℝᵈ R = ⊤
Is-ℝᵈ (σ :* τ) = Is-ℝᵈ σ × Is-ℝᵈ τ
Is-ℝᵈ (σ :+ τ) = ⊥
Is-ℝᵈ (σ :-> τ) = ⊥

-- Nested and combined extensional equality
-- f is equivalent to g and f' is equivalent to g'
P7≡ : ( σ : Typ Pr ) → ( isRd : Is-ℝᵈ σ  ) → ( τ : Typ Pr )
    → (f : Rep σ → Rep τ)
    → (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (g : Rep σ → Rep τ)
    → (g' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
P7≡ σ _ _ f f' g g' = f ≗ g 
  × ((x : Rep σ) → let (f1 , f2) = f' x
                       (g1 , g2) = g' x
                   in f1 ≡ g1 × f2 ≗ g2)

P7 : ( σ : Typ Pr ) → ( Is-ℝᵈ σ )
    → (τ : Typ Pr)
    → (f : Rep σ → Rep τ)
    → (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → Set
P7 ρ isRd Un f f' = 
  -- f f' is equivalent to the corresponding (zero) functions
  P7≡ ρ isRd Un f f' (const tt) (const (tt , const (zerovDense (D2τ' ρ))))
P7 ρ isRd Inte f f' = P7≡ ρ isRd Inte f f' f (λ x → (f x , const (zerovDense (D2τ' ρ))))
P7 ρ isRd R f f' =
  -- Forall possible inputs of f' ...
  ( x : Rep ρ ) → 
  -- ... the first element of the tuple produced by f'
  -- is equivalent to f ...
  (f x ≡ f' x .fst) 
--   -- ... and the second element of the tuple produced by f'
--   -- is equivalent to the transposed derivative of f.
  × ((dsem : Is-just (DSemᵀ {ρ} {R} f x))
     → f' x .snd ≗ (to-witness dsem))
P7 ρ isRd (σ :* τ) f f' =
  -- There exists some l l' and r r' ...
  Σ ((Rep ρ → Rep σ) × (Rep ρ → Rep τ)
      × (Rep ρ → ( Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
      × (Rep ρ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' ρ)))))
  λ (l , r , l' , r' )
  -- ... that are in P7 ...
  → Σ (P7 ρ isRd σ l l' 
     × P7 ρ isRd τ r r')
  (λ _ → 
  -- ... and combined show that f f' is in P6.
    let h  = λ x → (l x , r x )
        h' = λ x → (l' x .fst , r' x .fst) 
                , (λ ctg → case ctg of
                   maybe′ (λ (ctgL , ctgR) → plusvDense _ (l' x .snd ctgL) (r' x .snd ctgR)) 
                          (zerovDense (D2τ' ρ)))
    in P7≡ ρ isRd (σ :* τ) f f' h h'
  )
P7 ρ isRd (σ :+ τ) f f' = {!   !}
P7 ρ isRd (σ :-> τ) F F' =
-- There exists some f f' ...  (Without EVM types)
  Σ ((Rep ρ → Rep σ → Rep τ)
    × (Rep ρ → (Rep (D1τ σ) → Rep (D1τ τ) × (Rep (D2τ τ) → Rep (Lin Dyn) × Rep (D2τ σ))) × (LinRep Dyn → LinRepDense (D2τ' ρ))))
  λ (f , f')
-- ... such that for all g g' ...
  → (g : Rep ρ → Rep σ) 
  → (g' : Rep ρ → (Rep (D1τ σ) × (LinRep (D2τ' σ) → LinRepDense (D2τ' ρ))))
-- ... where g g' is in P7 ...
  → P7 ρ isRd σ g g'
-- ... g g' applied to f f' is shown to be in P7 ... 
  → (let h  = λ x → f x (g x) 
         h' = λ x → let (f1 , f2) = f' x
                        (g1 , g2) = g' x
                        (h1 , h2) = f1 g1
                     in h1 , (λ y → let (d , z) = h2 y in plusvDense (D2τ' ρ) (f2 d) (g2 z))
     in P7 ρ isRd τ h h')
-- ... and f f' is equivalent to F F' .
-- [Note, this is not just extentional equality, but semantic equality of executing an EVM]
  × ((x : Rep ρ) (y : Rep σ) → f x y ≡ F x y .fst) 
  × ((x : Rep ρ) (y : Rep (D1τ σ)) → 
        let (f1 , f2) = f' x 
            (f3 , f4) = f1 y
            (F1 , F2) = F' x
            ((F3 , F4) , _) = F1 y
            F4' = λ ctg → let (a , b , _) = LACMexec (F4 ctg .fst) (nothing , ((zerov (D2τ' σ) .fst) , tt))
                          in a , b
        in f2 ≗ F2 × f3 ≡ F3 × f4 ≗ F4')


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


projectInP7 : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ) 
    → (proj : Projecting σ τ isRd)
    → P7 σ isRd τ (project proj) (project'P7 proj)
projectInP7 σ τ isRd proj
  with projecting-preserves-Rd proj -- needed to convince agda that the non-Rd cases are impossible
-- First
projectInP7 (σ1 :* σ2) Un isRd (ProjectFst .σ1 .σ2 .Un .isRd proj) | _ 
  = (λ x → refl) , (λ _ → refl , λ ctg → cong₂ _,_ (project'-zero-lemma proj tt refl) refl)
projectInP7 (σ1 :* σ2) R isRd PROJ@(ProjectFst .σ1 .σ2 .R .isRd proj) | _ 
  = λ x → refl , λ dsem → λ ctg → project-dsem-lemma PROJ x dsem ctg
projectInP7 (σ1 :* σ2) (τ1 :* τ2) isRd PROJ@(ProjectFst .σ1 .σ2 .(τ1 :* τ2) .isRd proj) | _ 
  = (l , (r , (l' , r'))) , ((pl , pr) 
  , (λ x → cong₂ _,_ (projectingTakeFst-lemma proj (fst x)) (projectingTakeSnd-lemma proj (fst x))) , 
  λ y → (cong₂ _,_ (cong (primal τ1) (projectingTakeFst-lemma proj (fst y))) 
                     (cong (primal τ2) (projectingTakeSnd-lemma proj (fst y)))) , 
  ans y)
  where l  = project     {σ1 :* σ2} {τ1} {isRd} (projectingTakeFst PROJ)
        l' = project'P7  {σ1 :* σ2} {τ1} {isRd} (projectingTakeFst PROJ)
        pl = projectInP7 (σ1 :* σ2)  τ1   isRd  (projectingTakeFst PROJ)
        r  = project     {σ1 :* σ2} {τ2} {isRd} (projectingTakeSnd PROJ)
        r' = project'P7  {σ1 :* σ2} {τ2} {isRd} (projectingTakeSnd PROJ)
        pr = projectInP7 (σ1 :* σ2)  τ2   isRd  (projectingTakeSnd PROJ)
        ans : (y : Rep σ1 × Rep σ2) → (ctg : Maybe (LinRep (D2τ' τ1) × LinRep (D2τ' τ2))) → _
        ans y (just ctg) = cong₂ _,_ (project'-plus-lemma proj ctg) (sym plusvDense-zeroL')
        ans y nothing = cong₂ _,_ (project'-zero-lemma proj nothing refl) refl
-- Second
projectInP7 (σ1 :* σ2) Un isRd (ProjectSnd .σ1 .σ2 .Un .isRd proj) | _ 
  = (λ x → refl) , (λ _ → refl , (λ ctg → cong₂ _,_ refl (project'-zero-lemma proj tt refl)))
projectInP7 (σ1 :* σ2) R isRd PROJ@(ProjectSnd .σ1 .σ2 .R .isRd proj) | _ 
  = λ x → refl , (λ dsem → λ ctg → project-dsem-lemma PROJ x dsem ctg)
projectInP7 (σ1 :* σ2) (τ1 :* τ2) isRd PROJ@(ProjectSnd .σ1 .σ2 .(τ1 :* τ2) .isRd proj) | _ 
  = (l , (r , (l' , r'))) , (pl , pr) , 
    ((λ x → cong₂ _,_ (projectingTakeFst-lemma proj (snd x)) (projectingTakeSnd-lemma proj (snd x))) 
    , λ y → (cong₂ _,_ (cong (primal τ1) (projectingTakeFst-lemma proj (snd y))) 
                         (cong (primal τ2) (projectingTakeSnd-lemma proj (snd y)))) ,
    ans y)
  where l  = project     {σ1 :* σ2} {τ1} {isRd} (projectingTakeFst PROJ)
        l' = project'P7  {σ1 :* σ2} {τ1} {isRd} (projectingTakeFst PROJ)
        pl = projectInP7 (σ1 :* σ2)  τ1   isRd  (projectingTakeFst PROJ)
        r  = project     {σ1 :* σ2} {τ2} {isRd} (projectingTakeSnd PROJ)
        r' = project'P7  {σ1 :* σ2} {τ2} {isRd} (projectingTakeSnd PROJ)
        pr = projectInP7 (σ1 :* σ2)  τ2   isRd  (projectingTakeSnd PROJ)
        ans : (y : Rep σ1 × Rep σ2) → (ctg : Maybe (LinRep (D2τ' τ1) × LinRep (D2τ' τ2))) → _
        ans y (just ctg) = cong₂ _,_ (sym plusvDense-zeroL') (project'-plus-lemma proj ctg)
        ans y nothing = cong₂ _,_ refl (project'-zero-lemma proj nothing refl)
-- Identity 
projectInP7 Un Un isRd (ProjectDone .Un tt) | _ 
  = (λ _ → refl) , (λ _ → refl , (λ _ → refl))
projectInP7 R R isRd (ProjectDone .R tt) | _ 
  = λ x → refl , λ dsem → λ ctg → project-dsem-lemma (ProjectDone R tt) x dsem ctg -- HOLDS via identity postulation
projectInP7 (σ1 :* σ2) (τ1 :* τ2) isRd (ProjectDone .(σ1 :* σ2) .isRd) | _ 
  = (l , (r , (l' , r'))) , ((pl , pr) , 
    ((λ x → refl) , λ x → refl , ans x))
  where l  = project     {σ1 :* σ2} {σ1} {isRd} (ProjectFst σ1 σ2 σ1 isRd (ProjectDone σ1 (fst isRd)))
        l' = project'P7  {σ1 :* σ2} {τ1} {isRd} (ProjectFst σ1 σ2 σ1 isRd (ProjectDone σ1 (fst isRd)))
        pl = projectInP7 (σ1 :* σ2)  τ1   isRd  (ProjectFst σ1 σ2 σ1 isRd (ProjectDone σ1 (fst isRd)))
        r  = project     {σ1 :* σ2} {τ2} {isRd} (ProjectSnd σ1 σ2 σ2 isRd (ProjectDone σ2 (snd isRd)))
        r' = project'P7  {σ1 :* σ2} {τ2} {isRd} (ProjectSnd σ1 σ2 σ2 isRd (ProjectDone σ2 (snd isRd)))
        pr = projectInP7 (σ1 :* σ2)  τ2   isRd  (ProjectSnd σ1 σ2 σ2 isRd (ProjectDone σ2 (snd isRd)))
        ans : (x : Rep σ1 × Rep σ2) → (ctg : Maybe (LinRep (D2τ' σ1) × LinRep (D2τ' σ2))) → _
        ans x (just ctg) = cong₂ _,_ (sym plusvDense-zeroR') (sym plusvDense-zeroL')
        ans x nothing = refl
  

fst'P7 : { σ τ1 τ2 : Typ Pr } 
    → (f' : Rep σ → ( Rep (D1τ (τ1 :* τ2)) × (LinRep (D2τ' (τ1 :* τ2)) → LinRepDense (D2τ' σ))))
    → Rep σ → (Rep (D1τ τ1) × (LinRep (D2τ' τ1) → LinRepDense (D2τ' σ)))
fst'P7 {σ} {τ1} {τ2} f  = λ x → (f x .fst .fst) 
  , (λ ctg → f x .snd (just (ctg , zerov (D2τ' τ2) .fst)))

-- snd'P7 : { σ τ : Typ Pr } → Rep σ × Rep τ 
--     → Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ) × LinRepDense (D2τ' τ))
-- snd'P7 {σ} {τ} x = primal τ (snd x) , λ ctg → (zerovDense (D2τ' σ)) , (sparse2dense ctg)

fstInP7 : (σ τ1 τ2 : Typ Pr) → (isRd : Is-ℝᵈ (σ :* (τ1 :* τ2)))
    → (f : Rep σ → Rep (τ1 :* τ2))
    → (f' : Rep σ → ( Rep (D1τ (τ1 :* τ2)) × (LinRep (D2τ' (τ1 :* τ2)) → LinRepDense (D2τ' σ))))
    → P7 σ (fst isRd) (τ1 :* τ2) f f'
    → P7 σ (fst isRd) τ1 (fst ∘ f) (fst'P7 f')
fstInP7 σ Un τ2 isRd f f' ( (l , (r , (l' , r'))) , ( (pl , pr) , (p1 , p2) ))
  = (λ _ → refl) , (λ x → refl ,
  (λ ctg → {!   !} -- trans (p .snd .snd .snd x .snd (just (ctg , zerov _ .fst)))
                --  (trans (cong₂ (plusvDense (D2τ' σ)) {!   !} {!   !}) 
                 ))
fstInP7 σ R τ2 isRd f f' p = {!   !}
fstInP7 σ (τ1 :* τ3) τ2 isRd f f' p = {!   !}
-- sndInP7 : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ (σ :* τ))
--             → P7 (σ :* τ) isRd τ snd snd'P7

-- fstInP7 Un τ isRd = (λ _ → refl) , (λ {_} → refl , (λ _ → refl))
-- fstInP7 R τ isRd = λ x → refl , ans x
--   where ans : (x : Float × Rep τ) → _
--         ans = {!   !} -- HOLDS (by postulation on dsem)
-- fstInP7 (σ1 :* σ2) τ isRd = (l , (r , (l' , r'))) , ((pl , pr) 
--   , {!   !})
--   where l  = λ x → fst (fst x)
--         r  = λ x → snd (fst x)
--         l' = λ x → (primal σ1 (fst (fst x))) , (λ ctg → ((sparse2dense ctg) , (zerovDense (D2τ' σ2))) , (zerovDense (D2τ' τ)))
--         r' = {!   !}
--         pl = {! fstInP7 (σ1 :* σ2) τ     !}
--         pr = {!   !}
-- sndInP7 = {!   !}

identityInP7 : (σ : Typ Pr) → (isRd : Is-ℝᵈ σ)
            → P7 σ isRd σ id (λ x → (primal σ x , λ ctg → sparse2dense ctg))
identityInP7 Un isRd = (λ _ → refl) , (λ _ → refl , λ _ → refl)
identityInP7 R isRd = λ x → refl , ans x
  where ans : (x : Float) → (dsem : Is-just (DSemᵀ id x)) → (ctg : Float) → _
        ans x dsem ctg = let (d-id , rule) = DSemᵀ-identity x ctg
                     in sym (trans (DSemᵀ-extensionality id id _ x dsem d-id ctg) rule)
identityInP7 (σ :* τ) isRd = (l , r , (l' , r')) , (Pσ , Pτ) , {!   !} 
  ,  λ x → {!   !} , {!   !}
  where l  = project (ProjectFst σ τ σ isRd (ProjectDone σ (fst isRd)))
        r  = project (ProjectSnd σ τ τ isRd (ProjectDone τ (snd isRd)))
        l' = {!   !}
        r' = {!   !}
        Pσ = {!   !}
        Pτ = {!   !}
        ans : (ctg : Maybe (LinRep (D2τ' σ) × LinRep (D2τ' τ))) → _
        ans (just ctg) = {!   !}
        ans nothing    = {!   !}

-- P7equivImpliesInP7 : ( σ τ : Typ Pr ) ( isRd : Is-ℝᵈ (σ :* τ) )
--     → (f : Rep σ → Rep τ)
--     → (f' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
--     → (g : Rep σ → Rep τ)
--     → (g' : Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
--     → (P7≡ σ (fst isRd) τ f f' g g')
--     → P7 σ (fst isRd) τ f f'
--     → P7 σ (fst isRd) τ g g'
-- P7equivImpliesInP7 = ?

Fdsem : {σ τ : Typ Pr}
      → (f : Rep σ → Rep τ ) 
      → (Rep σ → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
Fdsem {σ} {τ} f = λ x → primal τ (f x) , λ ctg → maybe′ (λ dsem → dsem (sparse2dense ctg)) (zerovDense (D2τ' σ)) (DSemᵀ {σ} {τ} f x)

dsemInP7 : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ)
            → (f : Rep σ → Rep τ ) 
            → P7 σ isRd τ f (Fdsem f)
dsemInP7 ρ Un isRd f = (λ x → refl) , λ _ → refl , (λ y → ans)
  where ans : { x : Rep ρ } → { y : ⊤ } → Fdsem {ρ} {Un} f x .snd y ≡ const (tt , const (zerovDense (D2τ' ρ))) x .snd y
        ans {x} {tt} with DSemᵀ {ρ} {Un} f x
        ... | just d = {!   !} -- HOLDS (dsem-ctg-zero)
        ... | nothing = refl
dsemInP7 ρ Inte isRd f = {!   !}
dsemInP7 ρ R isRd f = λ x → refl , {!   !}
  where ans : ∀ {x} → maybe′ (_≗_ (Fdsem {ρ} {R} f x .snd)) ⊤ (DSemᵀ {ρ} {R} f x)
        ans {x} with DSemᵀ {ρ} {R} f x
        ... | just d = λ _ → refl
        ... | nothing = tt
dsemInP7 ρ (σ :* τ) isRd f = 
  ( l , ( r , (l' , r'))) , ((pσ , pτ) , (λ x → refl) , (λ _ → refl , (λ ctg → {!   !})))
  where l  = λ x → f x .fst
        r  = λ x → f x .snd
        l' = Fdsem l
        r' = Fdsem r
        pσ = dsemInP7 ρ σ isRd l
        pτ = dsemInP7 ρ τ isRd r
        h' = λ x → λ ctg → maybe′ (λ (ctgL , ctgR) → plusvDense _ (l' x .snd ctgL) (r' x .snd ctgR)) (zerovDense (D2τ' ρ)) ctg
        ans : {x : Rep ρ} → {ctg : Maybe (LinRep (D2τ' σ) × LinRep (D2τ' τ))} 
              → Fdsem {ρ} {σ :* τ} f x .snd ctg ≡ h' x ctg
        ans {x} {just ctg} 
          with DSemᵀ {ρ} {σ :* τ} f x
          with DSemᵀ {ρ} {σ} l x
          with DSemᵀ {ρ} {τ} r x
        ... | just d1 | just d2 | just d3 = {!   !} -- HOLDS (dsem-pair)
        ... | _ | _ | _ = {!   !} -- Outside of domain of definition
        ans {x} {nothing} = {!   !} -- HOLDS (dsem-ctg-zero)
dsemInP7 ρ (σ :+ τ) isRd f x 
  with f x | Fdsem {ρ} {σ :+ τ} f x | DSemᵀ {ρ} {σ :+ τ} f x
... | _ | _ | nothing = {!   !} -- Outside of domain of definition
... | inj₁ a | inj₁ b , c | just d = 
  (l , l') , pσ , (refl , (refl , ans))
  where l  = {! f x  !}
        l' = Fdsem l
        pσ = dsemInP7 ρ σ isRd l
        ans : (ctg : Maybe (LinRep (D2τ' σ) ⊎ LinRep (D2τ' τ))) → _ 
        ans (just (inj₁ ctg))
          with (DSemᵀ {ρ} {σ} (λ _ → a) x)
        ... | just d2 = {!   !}
        ... | nothing  = {!  !}
        ans (just (inj₂ _)) = tt
        ans nothing = {!   !}
... | inj₂ a | inj₂ b , c | just d = {!   !}
... | inj₁ a | inj₂ b , c | just d = {!   !}
... | inj₂ a | inj₁ b , c | just d = {!   !}
dsemInP7 ρ (σ :-> τ) isRd F = 
  -- (f , f') , (λ g g' Pg → Pf g g' Pg , ( {! f∼F !} , f'∼F'))
  (f , f') , q1
  where f  = {!   !}
        f' = {!   !}
        q1 : (g : _) (g' : _) (Pg : _) → _
        q1 g g' Pg = {! dsemInP7 ρ τ isRd ?   !} , {!   !}

        -- Pf : (g : _) → (g' : _) → (Pg : _) →  P7 ρ isRd τ (λ x → f x (g x)) _
        -- Pf = {! (g : _) → (g' : _) → (Pg : _) →  P7 ρ isRd τ (λ x → f x (g x)) _ !}
        -- f∼F = {!   !}
        -- f'∼F' = {!  !}

interp-chad : {Γ : Env Pr} {τ : Typ Pr} 
                  (t : Term Pr Γ τ)
                  (a : Val Pr Γ)
                  (evIn : LEtup (map D2τ' Γ) ) -- incoming LEtup
                → (ctg : LinRep (D2τ' τ))
                → (Rep (D1τ τ) × LEtup (map D2τ' Γ) )
interp-chad t a evIn ctg = let (x , y) = interp (chad t) (primalVal a)
                        in x , LACMexec (y ctg .fst) evIn 