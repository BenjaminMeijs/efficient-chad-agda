{-# OPTIONS --allow-unsolved-metas #-}
module HO-correctness.basics-about-relation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float; primFloatPlus)
open import Data.Integer using (ℤ)

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Data.Sum using (inj₁)
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

inP7-implies-equiv-DSem : { σ τ : Typ Pr } 
    → (q1 : Is-ℝᵈ σ) (q2 : Is-ℝᵈ τ)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → P7 σ q1 τ f f'
    → (x : Rep σ)
    → (ctg : LinRep (D2τ' τ))
    → (df : Is-just (DSemᵀ {σ} {τ} f x))
    → to-witness df (sparse2dense ctg) 
      ≡ f' (to-primal q1 x) .snd ctg
inP7-implies-equiv-DSem {σ} {Un} q1 q2 f f' p x ctg df
  = trans (DSemᵀ-ctg-zero f x df) 
          (sym (p .snd (to-primal q1 x) .snd ctg))
inP7-implies-equiv-DSem {σ} {R} q1 q2 f f' p x ctg df
  = sym (p x .snd df ctg)
inP7-implies-equiv-DSem {σ} {τ1 :* τ2} q1 q2 f f' p x (just ctg) df
  = let d0 = DSemᵀ-exists-extensionality f _ (p .snd .snd .fst) x df
        (d1 , d2) = DSemᵀ-exists-lemma-pair₁ (p .fst .fst) (p .fst .snd .fst) x d0
        ihl = inP7-implies-equiv-DSem {σ} {τ1} q1 (fst q2) (p .fst .fst) (p .fst .snd .snd .fst) (p .snd .fst .fst) x (fst ctg) d1
        ihr = inP7-implies-equiv-DSem {σ} {τ2} q1 (snd q2) (p .fst .snd .fst) (p .fst .snd .snd .snd) (p .snd .fst .snd) x (snd ctg) d2
        df-to-d0 = DSemᵀ-extensionality f _ (p .snd .snd .fst) x df d0 (sparse2dense {D2τ' τ1 :*! D2τ' τ2} (just ctg))
        d0-to-d12 = DSemᵀ-pair (p .fst .fst) (p .fst .snd .fst) x d0 d1 d2 (sparse2dense $ fst ctg) (sparse2dense $ snd ctg)
        d12-to-ih = cong₂ (plusvDense (D2τ' σ)) ihl ihr
        ih-to-pre = sym (p .snd .snd .snd (to-primal q1 x) .snd (just ctg))
    in trans df-to-d0 (trans d0-to-d12 (trans d12-to-ih ih-to-pre))
inP7-implies-equiv-DSem {σ} {τ1 :* τ2} q1 q2 f f' p x nothing df
  =  let a = DSemᵀ-ctg-zero f x df
         b = p .snd .snd .snd (to-primal q1 x) .snd nothing
     in trans a (sym b)  

constZeroRep' : {σ τ : Typ Pr} 
    → Rep (D1τ σ)
    →  Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))
constZeroRep' {σ} {τ} _ = primal τ (zeroRep τ) , const (zerovDense (D2τ' σ))

constZeroRep'-equiv-dsem : {σ τ : Typ Pr}
    → (isRd : Is-ℝᵈ σ)
    → (x : Rep σ)
    → (ctg : LinRep (D2τ' τ))
    → Σ (Is-just (DSemᵀ {σ} {τ} (const (zeroRep τ)) x))
        (λ df → constZeroRep' {σ} {τ} (to-primal isRd x) .snd ctg ≡ to-witness df (sparse2dense ctg))
constZeroRep'-equiv-dsem {σ} {τ} isRd x ctg = {!   !} -- holds by postulation on Dsem

-- We need these functions to be mutually recursive.
-- In the higher-order case of the linearity proof ctg-zero,
--    we must provide an `example` of a function pair in the logical relation for all sigma (isRd) to all tau.
-- This funtion is the constant function.
-- However, for the higher-order case of proving const is in the logical relation, we need the linearity proof ctg-zero.
-- This of course works out, because this mutual recursion is on the function g of the higher order case.
-- Luckily, we dont have to worry about this, as the termination checker does this for us.
const-zeroRep-inP7` : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → P7≡ σ isRd τ f f' (const (zeroRep τ)) constZeroRep'
    → P7 σ isRd τ f f'

const-zeroRep-inP7 : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ)
    → P7 σ isRd τ (const (zeroRep τ)) constZeroRep'

P7-ctg-zero : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → P7 σ isRd τ f f'
    → (x : Rep (D1τ σ)) → (ctg : LinRep (D2τ' τ))
    → (sparse2dense ctg ≡ zerovDense (D2τ' τ))
    → f' x .snd ctg ≡ zerovDense (D2τ' σ)

const-zeroRep-inP7` σ Un isRd f f' w = w
const-zeroRep-inP7` σ Inte isRd f f' (w1 , w2) = (λ x → refl) , (λ x → trans₂ refl (sym (w2 x .fst)) (sym (w1 (un-primal isRd x))) , (λ _ → w2 x .snd tt))
const-zeroRep-inP7` σ R isRd f f' w = 
    λ x → trans₂ refl (sym (w .fst x)) (sym (w .snd (to-primal isRd x) .fst)) 
    , λ dsem ctg → trans (w .snd (to-primal isRd x) .snd ctg) 
                    let (df , rule) = constZeroRep'-equiv-dsem isRd x ctg
                        ext = DSemᵀ-extensionality f (const (zeroRep R)) (w .fst) x dsem df ctg
                    in sym (trans ext (sym rule))
const-zeroRep-inP7` σ (τ1 :* τ2) isRd f f' w =
  let l  = const (zeroRep τ1)
      r  = const (zeroRep τ2)
      l' = constZeroRep'
      r' = constZeroRep'
      pl = const-zeroRep-inP7` σ τ1 isRd l l' ((λ _ → refl) , (λ _ → refl , (λ _ → refl)))
      pr = const-zeroRep-inP7` σ τ2 isRd r r' ((λ _ → refl) , (λ _ → refl , (λ _ → refl)))
  in (l , (r , l' , r')) , (pl , pr) , (λ x → w .fst x) , (λ x → (w .snd x .fst) , ans x)
  where ans : (y : Rep (D1τ σ)) → (ctg : Maybe (LinRep (D2τ' τ1) × LinRep (D2τ' τ2))) → _
        ans y (just ctg) = trans (w .snd y .snd (just ctg)) (sym plusvDense-zeroL')
        ans y nothing = w .snd y .snd nothing
const-zeroRep-inP7` σ (τ1 :+ τ2) isRd f f' w = {!   !}
const-zeroRep-inP7` σ (τ1 :-> τ2) isRd F F' w =
  (f , f') , ans
  where 
    f = λ _ _ → zeroRep τ2
    f' = λ x → (λ y → primal τ2 (zeroRep τ2) , λ ctg → nothing , (zerov (D2τ' τ1) .fst)) 
          , (const (zerovDense (D2τ' σ)))
    ans : (g : Rep σ → Rep τ1)
        → (g' : Rep (D1τ σ) → Rep (D1τ τ1) × (LinRep (D2τ' τ1) → LinRepDense (D2τ' σ)))
        → (pg : P7 σ isRd τ1 g g')
        → _
    ans g g' pg = ph , f-equiv-F , f'-equiv-F'
      where 
        ph = const-zeroRep-inP7` σ τ2 isRd (λ x → f x (g x)) _ ((λ x → refl) , (λ x → refl , 
                (λ ctg → trans plusvDense-zeroL' 
                    let zero-g = (P7-ctg-zero σ τ1 isRd g g' pg x (f' x .fst (g' x .fst) .snd ctg .snd) (zerov-equiv-zerovDense (D2τ' τ1))) 
                    in zero-g)))
        f-equiv-F : (x : Rep σ) (y : Rep τ1) → _
        f-equiv-F x y = sym (cong (λ z → z y .fst) (w .fst x))
        f'-equiv-F' : (x : Rep (D1τ σ)) (y : Rep (D1τ τ1)) → _
        f'-equiv-F' x y = (λ z → sym (w .snd x .snd z)) , sym (cong (λ foo → foo y .fst .fst)  (w .snd x .fst)) , (eq , isLin)
          where 
            eq : (ctg : LinRep (D2τ' τ2)) → _
            eq ctg = let lemma1 = sym $ cong (λ foo → foo y .fst .snd ctg .fst) (w .snd x .fst)
                         lemma2 = sym $ LACMexec-pure {Γ = Dyn ∷ D2τ' τ1 ∷ []} tt (nothing , zerov (D2τ' τ1) .fst , tt)
                         lemma3 = trans lemma2 (cong (λ foo → LACMexec foo (nothing , ((zerov (D2τ' τ1) .fst) , tt))) lemma1)
                     in cong₂ _,_ (cong fst lemma3) (cong (fst ∘ snd) lemma3)
            isLin : _
            isLin = (λ ctg0 w2 → refl , (zerov-equiv-zerovDense (D2τ' τ1))) 
                    , λ ctg1 ctg2 comp → refl , (sym (plusvSparse-zeroL (D2τ' τ1) (f' x .fst y .snd ctg2 .snd)))
const-zeroRep-inP7 σ τ isRd = const-zeroRep-inP7` σ τ isRd (const (zeroRep τ)) constZeroRep' ((λ x → refl) , (λ x → refl , (λ x₁ → refl)))

P7-ctg-zero σ Un isRd f f' p x ctg w = p .snd x .snd tt
P7-ctg-zero σ Inte isRd f f' p x ctg w = p .snd x .snd tt
P7-ctg-zero σ R isRd f f' p x ctg refl
  rewrite sym (lemma-primal₂ isRd x)
  = let df = {!   !} -- POSTULATION: the function is differentiable
    in trans (p (un-primal isRd x) .snd df ctg) 
             (DSemᵀ-lemma-ctg-zero' df)
P7-ctg-zero σ (τ1 :* τ2) isRd f f' ((l , r , l' , r') , (pl , pr) , p) x (just ctg) w 
  = trans (p .snd x .snd (just ctg)) 
    (trans (plusvDense-zeroL' {{P7-ctg-zero σ τ1 isRd l l' pl x (ctg .fst) (cong fst w)}}) 
    (P7-ctg-zero σ τ2 isRd r r' pr x (ctg .snd) (cong snd w)))
P7-ctg-zero σ (τ1 :* τ2) isRd f f' ((l , r , l' , r') , (pl , pr) , p) x nothing w 
  = p .snd x .snd nothing
P7-ctg-zero σ (τ1 :+ τ2) isRd f f' p x ctg w = {!   !}
P7-ctg-zero σ (τ1 :-> τ2) isRd F F' ((f , f') , p) x nothing refl
  = let g  = const (zeroRep τ1)
        g' = constZeroRep' {σ} {τ1}
        pg = const-zeroRep-inP7 σ τ1 isRd
        (ph , (_ , p')) = p g g' pg
        ih-g = P7-ctg-zero σ τ1 isRd g g' pg
        ih-h = P7-ctg-zero σ τ2 isRd _ _ ph
        v1 = g' x .fst
        ctg2 = zerov (D2τ' τ2) .fst
        ctg1 = f' x .fst v1 .snd ctg2 .snd
        lin-f : (f' x .fst v1 .snd ctg2 .fst ≡ nothing) 
               × (sparse2dense ctg1 ≡ zerovDense (D2τ' τ1))
        lin-f = let isLin = p' x v1 .snd .snd .snd
                in isLin .fst ctg2 (zerov-equiv-zerovDense (D2τ' τ2))
        f'-is-zero : f' x .snd nothing ≡ zerovDense (D2τ' σ)
        f'-is-zero =  trans₂
                        (trans₂ (ih-h x ctg2 (zerov-equiv-zerovDense (D2τ' τ2))) 
                                (plusvDense-zeroR' {{ih-g x ctg1 (snd lin-f)}}) refl) 
                        (cong (f' x .snd) (fst lin-f)) refl
    in trans (sym (p' x v1 .fst nothing )) 
              f'-is-zero

P7-ctg-plus : (σ τ : Typ Pr) → (isRd : Is-ℝᵈ σ)
    → (f : Rep σ → Rep τ)
    → (f' : Rep (D1τ σ) → ( Rep (D1τ τ) × (LinRep (D2τ' τ) → LinRepDense (D2τ' σ))))
    → P7 σ isRd τ f f'
    → (x : Rep (D1τ σ)) 
    → (ctg1 : LinRep (D2τ' τ))
    → (ctg2 : LinRep (D2τ' τ))
    → Compatible-LinReps ctg1 ctg2
    → f' x .snd (plusv _ ctg1 ctg2 .fst) 
      ≡ plusvDense _ (f' x .snd ctg1) (f' x .snd ctg2)
P7-ctg-plus σ Un isRd f f' p x tt tt c 
  = let w = P7-ctg-zero σ Un isRd f f' p x tt refl
    in trans w (sym (trans (plusvDense-zeroR' {{w}}) w))
P7-ctg-plus σ Inte isRd f f' p x tt tt c
  = let w = P7-ctg-zero σ Inte isRd f f' p x tt refl
    in trans w (sym (trans (plusvDense-zeroR' {{w}}) w))
P7-ctg-plus σ R isRd f f' p x ctg1 ctg2 c
  = {!    !} -- holds by postualtion on Dsem (is is equivalent to the derivative, ergo it is linear)
P7-ctg-plus σ (τ1 :* τ2) isRd f f' P@((l , (r , (l' , r'))) , ((pl , pr), (_ , p))) x (just ctg1) (just ctg2) c
  = let ctg = (just (plusv (D2τ' τ1) (ctg1 .fst) (ctg2 .fst) .fst ,
                        plusv (D2τ' τ2) (ctg1 .snd) (ctg2 .snd) .fst))
        ih-l = P7-ctg-plus σ τ1 isRd l l' pl x (fst ctg1) (fst ctg2) (fst c)
        ih-r = P7-ctg-plus σ τ2 isRd r r' pr x (snd ctg1) (snd ctg2) (snd c)
        -- If only we could have used a tactic for this part. Its not complex, just difficult
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
P7-ctg-plus σ (τ1 :* τ2) isRd f f' P@((l , (r , (l' , r'))) , ((pl , pr), (_ , p))) x (just ctg1) nothing c
  = sym (plusvDense-zeroR' {{p x .snd nothing}})
P7-ctg-plus σ (τ1 :* τ2) isRd f f' P@((l , (r , (l' , r'))) , ((pl , pr), (_ , p))) x nothing (just ctg2) c
  = sym (plusvDense-zeroL' {{p x .snd nothing}})
P7-ctg-plus σ (τ1 :* τ2) isRd f f' P@((l , (r , (l' , r'))) , ((pl , pr), (_ , p))) x nothing nothing c
  = sym (plusvDense-zeroL' {{p x .snd nothing}})
P7-ctg-plus σ (τ1 :+ τ2) isRd f f' p x ctg1 ctg2 c = {!   !}
P7-ctg-plus σ (τ1 :-> τ2) isRd f f' p x ctg1 ctg2 c = {!   !}