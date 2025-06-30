{-# OPTIONS --allow-unsolved-metas #-}
module HO-correctness.lemmas.basics-relation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float; primFloatPlus)
open import Data.Integer using (ℤ)

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Data.Sum using (inj₁)
open import Function.Base using (id; _$_; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ; swap)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_; subst)
open import Relation.Nullary.Decidable using (Dec; dec⇒maybe; yes; no)

open import spec renaming (LR to LTyp-LR)
open import HO-correctness.dense-rep
open import HO-correctness.dsem
open import HO-correctness.logical-relation
open import HO-correctness.lemmas.dsem-lemmas
open import HO-correctness.lemmas.projection-in-relation
open import HO-correctness.lemmas.LinRepDense-is-comm-monoid
open import HO-correctness.lemmas.trivial-equivalences

private
    trans₂ : {A : Set} {x y a b : A} → x ≡ y → x ≡ a → y ≡ b → a ≡ b
    trans₂ refl refl refl = refl

identityInLR : (σ : Typ Pr) → (isRd : Is-ℝᵈ σ)
            → LR σ isRd σ id (λ x → (x , sparse2dense))
identityInLR Un isRd = (λ _ → refl) , (λ _ → refl , λ _ → refl)
identityInLR R isRd = λ x → refl , ans x 
  where ans : (x : Float) → _
        ans x = let (d-id1 , rule1) = DSemᵀ-identity {R} x (zerovDense LTyp-LR) 
                in d-id1 , (λ ctg → 
                  let (d-id2 , rule2) = DSemᵀ-identity {R} x ctg 
                  in trans (sym rule2) (DSemᵀ-extensionality id id (λ _ → refl) x d-id2 d-id1 ctg))
identityInLR (σ :* τ) isRd = (l , r , (l' , r')) , (Pσ , Pτ) , (λ _ → refl) 
  ,  λ x → cong₂ _,_ (sym (lemma-primal₂ (fst isRd) (fst x)))
                     (sym (lemma-primal₂ (snd isRd) (snd x))) 
  , ans
  where l  = project (LensFst σ τ σ isRd (LensId σ (fst isRd)))
        r  = project (LensSnd σ τ τ isRd (LensId τ (snd isRd)))
        l' = project'LR (LensFst σ τ σ isRd (LensId σ (fst isRd)))
        r' = project'LR (LensSnd σ τ τ isRd (LensId τ (snd isRd)))
        Pσ = projectInLR (σ :* τ) σ isRd (LensFst σ τ σ isRd (LensId σ (fst isRd)))
        Pτ = projectInLR (σ :* τ) τ isRd (LensSnd σ τ τ isRd (LensId τ (snd isRd)))
        ans : (ctg : Maybe (LinRep (D2τ' σ) × LinRep (D2τ' τ))) → _
        ans (just ctg) = cong₂ _,_ (sym plusvDense-zeroR') (sym plusvDense-zeroL')
        ans nothing    = refl

LR-extensionality : { σ τ : Typ Pr } → ( isRd : Is-ℝᵈ σ  ) 
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → (g : Rep σ → Rep τ)
    → (g' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → LR≡ f f' g g'
    → LR σ isRd τ f f'
    → LR σ isRd τ g g'
LR-extensionality {σ} {Un} isRd f f' g g' eq p = 
  (λ x → refl) , (λ x → refl , (λ ctg → trans (sym (eq .snd x .snd ctg)) (p .snd x .snd tt)))
LR-extensionality {σ} {Inte} isRd f f' g g' eq p
  = (λ x → refl) 
    , (λ x → (trans₂ (p .snd x .fst) (eq .snd x .fst) (eq .fst (un-primal isRd x))) 
    , (λ ctg → trans (sym (eq .snd x .snd ctg)) (p .snd x .snd tt)))
LR-extensionality {σ} {R} isRd f f' g g' eq p
  = λ x → (trans₂ (p x .fst) (eq .fst x) (eq .snd (to-primal isRd x) .fst)) 
    , let df = p x .snd .fst
          dg = DSemᵀ-exists-extensionality f g (eq .fst) x df
      in dg , λ ctg → trans (sym $ eq .snd (to-primal isRd x) .snd ctg) 
                     (trans (p x .snd .snd ctg) 
                     (DSemᵀ-extensionality f g (eq .fst) x df dg ctg))
LR-extensionality {σ} {τ1 :* τ2} isRd f f' g g' eq p 
  = ((p .fst .fst) , ((p .fst .snd .fst) , ((p .fst .snd .snd .fst) , (p .fst .snd .snd .snd)))) 
  , (((p .snd .fst .fst) , (p .snd .fst .snd)) 
  , ((λ x → trans (sym (eq .fst x)) (p .snd .snd .fst x)) 
  , λ x → (trans (sym (eq .snd x .fst)) (p .snd .snd .snd x .fst)) 
  , (λ ctg → trans (sym (eq .snd x .snd  ctg)) (p .snd .snd .snd x .snd ctg))))
LR-extensionality {σ} {τ1 :+ τ2} isRd f f' g g' eq p = {!   !}
LR-extensionality {σ} {τ1 :-> τ2} isRd F F' G G' eq ((f , f') , p)
  = (f , f') 
  , λ g g' a → let P = p g g' a
  in (fst P) 
  , (λ x y → trans (P .snd .fst x y) (cong (λ q → q y .fst) (eq .fst x))) 
  , λ x y → (λ ctg → trans ((P .snd .snd x y .fst ctg  )) (eq .snd x .snd ctg)) 
  , (trans (P .snd .snd x y .snd .fst) (cong (λ q → q y .fst .fst) (eq .snd x .fst)) 
  , ((λ ctg → trans (P .snd .snd x y .snd .snd .fst ctg) 
                let eq2 = (cong (λ q → q y .fst .snd ctg .fst) (eq .snd x .fst))
                in cong (maybe′ swap (nothing , zerov (D2τ' τ1) .fst)) eq2 ) 
  , p g g' a .snd .snd x y .snd .snd .snd))

inLR-implies-equiv-DSem : { σ τ : Typ Pr } 
    → (q1 : Is-ℝᵈ σ) (q2 : Is-ℝᵈ τ)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → LR σ q1 τ f f'
    → (x : Rep σ)
    → (ctg : LinRep (D2τ' τ))
    → (df : Is-just (DSemᵀ {σ} {τ} f x))
    → to-witness df (sparse2dense ctg) 
      ≡ f' (to-primal q1 x) .snd ctg
inLR-implies-equiv-DSem {σ} {Un} q1 q2 f f' p x ctg df
  = trans (DSemᵀ-ctg-zero f x df) 
          (sym (p .snd (to-primal q1 x) .snd ctg))
inLR-implies-equiv-DSem {σ} {R} q1 q2 f f' p x ctg df
  = let (dg , rule) = p x .snd 
    in trans (DSemᵀ-extensionality f f (λ _ → refl) x df dg ctg) (sym (rule ctg))
inLR-implies-equiv-DSem {σ} {τ1 :* τ2} q1 q2 f f' p x (just ctg) df
  = let d0 = DSemᵀ-exists-extensionality f _ (p .snd .snd .fst) x df
        (d1 , d2) = DSemᵀ-exists-lemma-pair₁ (p .fst .fst) (p .fst .snd .fst) x d0
        ihl = inLR-implies-equiv-DSem {σ} {τ1} q1 (fst q2) (p .fst .fst) (p .fst .snd .snd .fst) (p .snd .fst .fst) x (fst ctg) d1
        ihr = inLR-implies-equiv-DSem {σ} {τ2} q1 (snd q2) (p .fst .snd .fst) (p .fst .snd .snd .snd) (p .snd .fst .snd) x (snd ctg) d2
        df-to-d0 = DSemᵀ-extensionality f _ (p .snd .snd .fst) x df d0 (sparse2dense {D2τ' τ1 :*! D2τ' τ2} (just ctg))
        d0-to-d12 = DSemᵀ-pair (p .fst .fst) (p .fst .snd .fst) x d0 d1 d2 (sparse2dense $ fst ctg) (sparse2dense $ snd ctg)
        d12-to-ih = cong₂ (plusvDense (D2τ' σ)) ihl ihr
        ih-to-pre = sym (p .snd .snd .snd (to-primal q1 x) .snd (just ctg))
    in trans df-to-d0 (trans d0-to-d12 (trans d12-to-ih ih-to-pre))
inLR-implies-equiv-DSem {σ} {τ1 :* τ2} q1 q2 f f' p x nothing df
  =  let a = DSemᵀ-ctg-zero f x df
         b = p .snd .snd .snd (to-primal q1 x) .snd nothing
     in trans a (sym b)  

constZeroRep' : {σ τ : Typ Pr} 
    → Rep (D1τ σ)
    →  Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))
constZeroRep' {σ} {Un} _ = tt , const (zerovDense (D2τ' σ))
constZeroRep' {σ} {Inte} _ = ℤ.pos 0 , const (zerovDense (D2τ' σ))
constZeroRep' {σ} {R} _ = 0.0 , const (zerovDense (D2τ' σ))
constZeroRep' {σ} {τ1 :* τ2} x =
  let a = constZeroRep' {σ} {τ1} x
      b = constZeroRep' {σ} {τ2} x
  in ((a .fst) , b .fst) , const (zerovDense (D2τ' σ))
constZeroRep' {σ} {τ1 :+ τ2} x =
  let a = constZeroRep' {σ} {τ1} x
  in (inj₁ (a .fst)) , const (zerovDense (D2τ' σ))
constZeroRep' {σ} {τ1 :-> τ2} x = 
  let a = constZeroRep' {σ} {τ2} x
  in (λ _ → (a .fst , (λ _ → nothing , (ℤ.pos 0))) , (ℤ.pos 0)) 
     , const (zerovDense (D2τ' σ))

sndConstZeroRep≡zerovDense : {σ τ : Typ Pr}
  → (x : Rep (D1τ σ))
  → (ctg : LinRep (D2τ' τ))
  → constZeroRep' x .snd ctg ≡ zerovDense (D2τ' σ)
sndConstZeroRep≡zerovDense {σ} {Un} x ctg = refl
sndConstZeroRep≡zerovDense {σ} {Inte} x ctg = refl
sndConstZeroRep≡zerovDense {σ} {R} x ctg = refl
sndConstZeroRep≡zerovDense {σ} {τ :* τ₁} x ctg = refl
sndConstZeroRep≡zerovDense {σ} {τ :+ τ₁} x ctg = refl
sndConstZeroRep≡zerovDense {σ} {τ :-> τ₁} x ctg = refl

constZeroRep'-equiv-dsem : {σ τ : Typ Pr}
    → (isRd : Is-ℝᵈ σ)
    → (x : Rep σ)
    → Σ (Is-just (DSemᵀ {σ} {τ} (const (zeroRep τ)) x))
        (λ df → (ctg : LinRep (D2τ' τ)) 
              → constZeroRep' {σ} {τ} (to-primal isRd x) .snd ctg ≡ to-witness df (sparse2dense ctg))
constZeroRep'-equiv-dsem {σ} {τ} isRd x = 
  let rule = DSemᵀ-lemma-const₂ {w = λ _ → refl} {a = x}
  in (rule .fst) , λ ctg →
        trans (sndConstZeroRep≡zerovDense (to-primal isRd x) ctg)
              (sym (rule .snd (sparse2dense {D2τ' τ} ctg)))


-- We need these functions to be mutually recursive.
-- In the higher-order case of the linearity proof ctg-zero,
--    we must provide an `example` of a function pair in the logical relation for all sigma (isRd) to all tau.
-- This funtion is the constant function.
-- However, for the higher-order case of proving const is in the logical relation, we need the linearity proof ctg-zero.
-- This of course works out, because this mutual recursion is on the function g of the higher order case.
-- Luckily, we dont have to worry about this, as the termination checker does this for us.
const-zeroRep-inLR : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ)
    → LR σ isRd τ (const (zeroRep τ)) constZeroRep'

LR-ctg-zero : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → LR σ isRd τ f f'
    → (x : Rep (D1τ σ)) → (ctg : LinRep (D2τ' τ))
    → (sparse2dense ctg ≡ zerovDense (D2τ' τ))
    → f' x .snd ctg ≡ zerovDense (D2τ' σ)

const-zeroRep-inLR σ Un isRd = (λ x → refl) , (λ x → refl , (λ x₁ → refl))
const-zeroRep-inLR σ Inte isRd = (λ x → refl) , (λ x → refl , (λ x₁ → refl))
const-zeroRep-inLR σ R isRd = 
  λ x → refl , 
  let (dsem , rule) = constZeroRep'-equiv-dsem {σ} {R} isRd x
  in dsem , rule
const-zeroRep-inLR σ (τ1 :* τ2) isRd =
  (l , (r , l' , r')) , (pl , pr) , (λ _ → refl) , λ x → refl , ans x
    where l  = const (zeroRep τ1)
          r  = const (zeroRep τ2)
          l' = constZeroRep'
          r' = constZeroRep'
          pl = const-zeroRep-inLR σ τ1 isRd
          pr = const-zeroRep-inLR σ τ2 isRd
          ans : (x : Rep (D1τ σ)) → (ctg : Maybe (LinRep (D2τ' τ1) × LinRep (D2τ' τ2))) → _
          ans x (just ctg) = 
            sym (trans (plusvDense-zeroL' {{sndConstZeroRep≡zerovDense x (fst ctg)}}) (sndConstZeroRep≡zerovDense x (snd ctg)))
          ans x nothing = refl
const-zeroRep-inLR σ (τ1 :+ τ2) isRd = {!   !}
const-zeroRep-inLR σ (τ1 :-> τ2) isRd =
  (f , f') , ans
  where 
    f = λ _ _ → zeroRep τ2
    f' = λ x → (λ y → constZeroRep' {σ} {τ2} x .fst , λ ctg → nothing , zerov (D2τ' τ1) .fst) , (const (zerovDense (D2τ' σ)))
    ans : (g : Rep σ → Rep τ1)
        → (g' : Rep (D1τ σ) → Rep (D1τ τ1) × (LinRep (D2τ' τ1) → LinRepDense (D2τ' σ)))
        → (pg : LR σ isRd τ1 g g')
        → _
    ans g g' pg = ph , f-equiv-F , f'-equiv-F'
      where 
        -- ph
        ih = const-zeroRep-inLR σ τ2 isRd
        h = (λ x → f x (g x))
        h' = (λ x → f' x .fst (g' x .fst) .fst , (λ y → plusvDense (D2τ' σ) (f' x .snd (f' x .fst (g' x .fst) .snd y .fst)) (g' x .snd (f' x .fst (g' x .fst) .snd y .snd))))
        g-isLin : (x : Rep (D1τ σ)) → g' x .snd (zerov (D2τ' τ1) .fst) ≡ zerovDense (D2τ' σ)
        g-isLin x = LR-ctg-zero σ τ1 isRd g g' pg x (zerov (D2τ' τ1) .fst) (zerov-equiv-zerovDense (D2τ' τ1))
        h-equiv-constZero = (λ x → refl) , (λ x → refl , (λ ctg → trans (sndConstZeroRep≡zerovDense x ctg) (sym (plusvDense-zeroR' {{g-isLin x}}))))
        ph = LR-extensionality isRd (const (zeroRep τ2)) constZeroRep' h h' h-equiv-constZero ih
        -- equivs
        f-equiv-F = λ x y → refl
        f'-equiv-F' = λ x y → (λ _ → refl) , (refl , ((λ ctg → refl) 
                    , (λ ctg0 w → (λ τ3 → refl) , (zerov-equiv-zerovDense (D2τ' τ1)))
                    , (λ ctg1 ctg2 x₁ → refl , (sym (plusvSparse-zeroL (D2τ' τ1) (zerov (D2τ' τ1) .fst))))))

LR-ctg-zero σ Un isRd f f' p x ctg w = p .snd x .snd tt
LR-ctg-zero σ Inte isRd f f' p x ctg w = p .snd x .snd tt
LR-ctg-zero σ R isRd f f' p x ctg refl
  = let (df , rule) = p (un-primal isRd x) .snd 
    in trans (cong (λ α → f' α .snd 0.0) (sym $ lemma-primal₂ isRd x)) 
       (trans (rule 0.0) (DSemᵀ-ctg-zero f (un-primal isRd x) df))
LR-ctg-zero σ (τ1 :* τ2) isRd f f' ((l , r , l' , r') , (pl , pr) , p) x (just ctg) w 
  = trans (p .snd x .snd (just ctg)) 
    (trans (plusvDense-zeroL' {{LR-ctg-zero σ τ1 isRd l l' pl x (ctg .fst) (cong fst w)}}) 
    (LR-ctg-zero σ τ2 isRd r r' pr x (ctg .snd) (cong snd w)))
LR-ctg-zero σ (τ1 :* τ2) isRd f f' ((l , r , l' , r') , (pl , pr) , p) x nothing w 
  = p .snd x .snd nothing
LR-ctg-zero σ (τ1 :+ τ2) isRd f f' p x ctg w = {!   !}
LR-ctg-zero σ (τ1 :-> τ2) isRd F F' ((f , f') , p) x ctg w
  = let g  = const (zeroRep τ1)
        g' = constZeroRep' {σ} {τ1}
        pg = const-zeroRep-inLR σ τ1 isRd
        (ph , (_ , p')) = p g g' pg
        ih-g = LR-ctg-zero σ τ1 isRd g g' pg
        ih-h = LR-ctg-zero σ τ2 isRd _ _ ph
        v1 = g' x .fst
        ctg2 = zerov (D2τ' τ2) .fst
        ctg1 = f' x .fst v1 .snd ctg2 .snd
        -- foo : (f' x .snd ctg) ≡ zerovDense (D2τ' σ)
        -- foo = {! f' x .snd    !}
        -- biz : f' x .snd (f' x .fst v1 .snd ctg2 .fst) ≡ zerovDense (D2τ' σ)
        -- biz = trans (sym (plusvDense-zeroR' {{sndConstZeroRep≡zerovDense x ctg1}})) 
        --       (ih-h x ctg2 (zerov-equiv-zerovDense (D2τ' τ2)))
        -- f'-is-zero : (c : Maybe (Σ LTyp LinRep)) → (w : {!   !}) 
        --       → f' x .snd c ≡ zerovDense (D2τ' σ)
        -- f'-is-zero =  {!   !}
          -- sym (trans (sym (ih-h x ctg2 (zerov-equiv-zerovDense (D2τ' τ2)))) 
                          -- (trans (plusvDense-zeroR' {{sndConstZeroRep≡zerovDense x ctg1}}) 
                          -- (trans₂ refl (sym biz) (sym foo))))
        f'-is-lin : (c : Maybe (Σ LTyp LinRep)) → ((t : LTyp) → sparse2dense {Dyn} c t ≡ zerovDense Dyn t)
              → (f' x .snd c ≡ zerovDense (D2τ' σ))
        f'-is-lin = λ c w → {! ih-h  !}
    in trans (sym (p' x v1 .fst ctg)) {! ih-h x ctg2    !}
-- LR-ctg-zero σ (τ1 :-> τ2) isRd F F' ((f , f') , p) x (just (τ3 , ctg)) w
--   = let g  = const (zeroRep τ1)
--         g' = constZeroRep' {σ} {τ1}
--         pg = const-zeroRep-inLR σ τ1 isRd
--         (ph , (_ , p')) = p g g' pg
--         ih-g = LR-ctg-zero σ τ1 isRd g g' pg
--         ih-h = LR-ctg-zero σ τ2 isRd _ _ ph
--     in ?
    -- trans (sym (p' x v1 .fst ctg)) {!   !}

LR-ctg-plus : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → LR σ isRd τ f f'
    → (x : Rep (D1τ σ)) 
    → (ctg1 : LinRep (D2τ' τ))
    → (ctg2 : LinRep (D2τ' τ))
    -- → Compatible-LinReps ctg1 ctg2  -- Not needed, we dont use co-products
    → f' x .snd (plusv _ ctg1 ctg2 .fst) 
      ≡ plusvDense _ (f' x .snd ctg1) (f' x .snd ctg2)
LR-ctg-plus σ Un isRd f f' p x tt tt 
  = let w = LR-ctg-zero σ Un isRd f f' p x tt refl
    in trans w (sym (trans (plusvDense-zeroR' {{w}}) w))
LR-ctg-plus σ Inte isRd f f' p x tt tt 
  = let w = LR-ctg-zero σ Inte isRd f f' p x tt refl
    in trans w (sym (trans (plusvDense-zeroR' {{w}}) w))
LR-ctg-plus σ R isRd f f' p x ctg1 ctg2 
  = {!    !} -- holds by postualtion on Dsem (is is equivalent to the derivative, ergo it is linear)
LR-ctg-plus σ (τ1 :* τ2) isRd f f' P@((l , (r , (l' , r'))) , ((pl , pr), (_ , p))) x (just ctg1) (just ctg2)
  = let ctg = (just (plusv (D2τ' τ1) (ctg1 .fst) (ctg2 .fst) .fst ,
                        plusv (D2τ' τ2) (ctg1 .snd) (ctg2 .snd) .fst))
        ih-l = LR-ctg-plus σ τ1 isRd l l' pl x (fst ctg1) (fst ctg2)
        ih-r = LR-ctg-plus σ τ2 isRd r r' pr x (snd ctg1) (snd ctg2)
        -- If only we could have used a tactic for this part. Its not complex, just tedious
        plus = plusvDense (D2τ' σ); assoc = plusvDense-assoc (D2τ' σ); comm = plusvDense-comm (D2τ' σ)
        a = (l' x .snd (fst ctg1)); b = (l' x .snd (fst ctg2)); c = (r' x .snd (snd ctg1)); d = (r' x .snd (snd ctg2))
        lemma-assoc : plus (plus a b) (plus c d)
                    ≡ plus (plus a c) (plus b d)
        lemma-assoc = trans (assoc a b (plus c d)) 
                     (trans (cong (plus a) (cong (plus b) (comm c d))) 
                     (trans (cong (plus a) (sym (assoc b d c))) 
                     (trans (cong (plus a) (comm (plus b d) c)) 
                     (sym (assoc a c (plus b d))))))
    in trans (p x .snd ctg) 
       (trans (cong₂ (plusvDense (D2τ' σ)) ih-l ih-r) 
        (trans lemma-assoc (cong₂ (plusvDense (D2τ' σ)) (sym (p x .snd (just ctg1))) (sym (p x .snd (just ctg2))))))
LR-ctg-plus σ (τ1 :* τ2) isRd f f' P@((l , (r , (l' , r'))) , ((pl , pr), (_ , p))) x (just ctg1) nothing
  = sym (plusvDense-zeroR' {{p x .snd nothing}})
LR-ctg-plus σ (τ1 :* τ2) isRd f f' P@((l , (r , (l' , r'))) , ((pl , pr), (_ , p))) x nothing (just ctg2)
  = sym (plusvDense-zeroL' {{p x .snd nothing}})
LR-ctg-plus σ (τ1 :* τ2) isRd f f' P@((l , (r , (l' , r'))) , ((pl , pr), (_ , p))) x nothing nothing
  = sym (plusvDense-zeroL' {{p x .snd nothing}})
LR-ctg-plus σ (τ1 :+ τ2) isRd f f' p x ctg1 ctg2 = {!   !}
LR-ctg-plus σ (τ1 :-> τ2) isRd F F' P@((f , f') , p) x nothing nothing
  = let F'-zero = LR-ctg-zero σ (τ1 :-> τ2) isRd F F' P x nothing refl
    in sym (plusvDense-zeroL' {{F'-zero}})
LR-ctg-plus σ (τ1 :-> τ2) isRd F F' P@((f , f') , p) x (just c1) nothing 
  = let F-zero = LR-ctg-zero σ (τ1 :-> τ2) isRd F F' P x nothing refl
    in sym (plusvDense-zeroR' {{ F-zero}})
LR-ctg-plus σ (τ1 :-> τ2) isRd F F' P@((f , f') , p) x nothing (just c2)
  = let F-zero = LR-ctg-zero σ (τ1 :-> τ2) isRd F F' P x nothing refl
    in sym (plusvDense-zeroL' {{ F-zero}})
LR-ctg-plus σ (τ1 :-> τ2) isRd F F' P@((f , f') , p) x (just c1) (just c2) 
  = let g  = const (zeroRep τ1)
        g' = constZeroRep' {σ} {τ1}
        pg = const-zeroRep-inLR σ τ1 isRd
        (ph , (_ , p')) = p g g' pg
        -- y = {!   !}



        ctg1L = {!   !}
        ctg1R = {!   !}
        ctg2L = {!   !}
        ctg2R = {!   !}
        ih-g = LR-ctg-plus σ τ1 isRd g g' pg x ctg1L ctg1R
        ih-h = LR-ctg-plus σ τ2 isRd _ _ ph x ctg2L ctg2R
        -- v1 = g' x .fst
        -- ctg2 = zerov (D2τ' τ2) .fst
        -- ctg1 = f' x .fst v1 .snd ctg2 .snd
        -- lin-f : (f' x .fst v1 .snd ctg2 .fst ≡ nothing) 
        --        × (sparse2dense ctg1 ≡ zerovDense (D2τ' τ1))
        -- lin-f = let isLin = p' x v1 .snd .snd .snd
        --         in isLin .fst ctg2 (zerov-equiv-zerovDense (D2τ' τ2))
        -- f'-is-zero : f' x .snd nothing ≡ zerovDense (D2τ' σ)
        -- f'-is-zero =  trans₂
        --                 (trans₂ (ih-h x ctg2 (zerov-equiv-zerovDense (D2τ' τ2))) 
        --                         (plusvDense-zeroR' {{ih-g x ctg1 (snd lin-f)}}) refl) 
        --                 (cong (f' x .snd) (fst lin-f)) refl
    in {! p' x y   !}
  --   -- trans (sym (p' x v1 .fst nothing )) 
  --             -- f'-is-zero  