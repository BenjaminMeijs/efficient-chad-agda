module HO-correctness.lemmas where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Float using (Float)
open import Level using (Level)

open import Data.List using (_∷_; map; [])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; maybe; maybe′)
open import Function.Base using (id; _$_; const; _∘_; case_of_)
open import Data.Product using (_×_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; _≗_; subst)
open import Relation.Nullary.Decidable using (yes; no)

open import spec hiding (LR)
open import correctness.spec
open import HO-correctness.logical-relation


Is-ℝᵈ-irrel : {τ : Typ Pr} → (x : Is-ℝᵈ τ) → (y : Is-ℝᵈ τ)
  → x ≡ y
Is-ℝᵈ-irrel {Un} x y = refl
Is-ℝᵈ-irrel {R} x y = refl
Is-ℝᵈ-irrel {τ1 :* τ2} (x1 , x2) (y1 , y2) = cong₂ _,_ (Is-ℝᵈ-irrel x1 y1) (Is-ℝᵈ-irrel x2 y2)

lemma-dyn : {Γ : Env Du} {τ : LTyp}
  → (t : Term Du Γ (Lin τ))   
  → (val : Val Du Γ)
  → interp (fromDyn (toDyn t)) val ≡ interp t val
lemma-dyn {Γ} {τ} t v with (τ LTyp≟ τ)
... | yes refl = refl
... | no w = ⊥-elim (w refl)

lemma-primal₁ : { τ : Typ Pr } → ( isRd : Is-ℝᵈ τ ) 
  → (x : Rep τ)
  → un-primal isRd (to-primal isRd x) ≡ x
lemma-primal₁ {Un} isRd x = refl
lemma-primal₁ {R} isRd x = refl
lemma-primal₁ {τ1 :* τ2} isRd x = cong₂ _,_ (lemma-primal₁ (isRd .fst) (x .fst))
                                            (lemma-primal₁ (isRd .snd) (x .snd))

lemma-primal₂ : { τ : Typ Pr } → ( isRd : Is-ℝᵈ τ ) 
  → (x : Rep (D1τ τ))
  → to-primal isRd (un-primal isRd x) ≡ x
lemma-primal₂ {Un} isRd x = refl
lemma-primal₂ {R} isRd x = refl
lemma-primal₂ {τ :* τ₁} isRd x = cong₂ _,_ (lemma-primal₂ (isRd .fst) (x .fst))
                                           (lemma-primal₂ (isRd .snd) (x .snd))

cong-to-primal : { τ : Typ Pr }
  → { isRd1 : Is-ℝᵈ τ } → { isRd2 : Is-ℝᵈ τ }
  → { x : Rep τ } {y : Rep τ}
  → x ≡ y
  → to-primal isRd1 x ≡ to-primal isRd2 y
cong-to-primal {Un} {q1} {q2} {x} {y} w = w
cong-to-primal {R} {q1} {q2} {x} {y} w = w
cong-to-primal {τ1 :* τ2} {q1} {q2} {x} {y} refl
  = cong₂ _,_ (cong-to-primal {τ1} {q1 .fst} {q2 .fst} {x .fst} {x .fst} refl) 
              (cong-to-primal {τ2} {q1 .snd} {q2 .snd} {x .snd} {x .snd} refl)

dense2sparse : {τ : Typ Pr} → (Is-ℝᵈ τ) → LinRepDense (D2τ' τ) → LinRep (D2τ' τ)
dense2sparse {Un} isRd x = tt
dense2sparse {R} isRd x = x
dense2sparse {τ1 :* τ2} isRd x = just (dense2sparse (isRd .fst) (x .fst) 
                                     , dense2sparse (isRd .snd) (x .snd))

lemma-dense : {τ : Typ Pr} → (isRd : Is-ℝᵈ τ) 
    → (x : LinRepDense (D2τ' τ))
    → sparse2dense (dense2sparse isRd x) ≡ x
lemma-dense {Un} isRd x = refl
lemma-dense {R} isRd x = refl
lemma-dense {τ1 :* τ2} isRd x = cong₂ _,_ (lemma-dense (isRd .fst) (x .fst))
                                          (lemma-dense (isRd .snd) (x .snd))

sub : {l : Level} {A B : Set l} → ( A ≡ B ) → ( x : A) → B
sub {l} {A} {B} w x = subst id w x

sub-× : {l : Level} {A1 A2 B1 B2 : Set l} 
    → {x : A1} {y : B1} {xs : A2} {ys : B2}
    → ( w1 : A1 ≡ B1 ) (w2 : A2 ≡ B2) (w3 : (A1 × A2) ≡ (B1 × B2))
    → (sub w1 x  ≡ y)
    → (sub w2 xs ≡ ys)
    → sub w3 (x , xs) ≡ (y , ys)
sub-× refl refl refl refl refl = refl

sub-fst : {l : Level} { A B C : Set l} 
    → (w : (C × A) ≡ (C × B) )
    → (A ≡ B)
    → (x : C × A)
    → sub w x .fst ≡ x . fst
sub-fst refl refl x = refl

sub-snd : {l : Level} { A1 B1 A2 B2 : Set l} 
    → (w0 : (A1 × A2) ≡ (B1 × B2) )
    → (w1 : A1 ≡ B1)
    → (w2 : A2 ≡ B2)
    → (x : A1 × A2)
    → (sub w0 x) .snd ≡ sub w2 (x .snd)
sub-snd refl refl refl x = refl

sub-chain : {l : Level} {A B C : Set l} 
    → {x : A}
    → ( w1 : A ≡ B ) (w2 : B ≡ C)
    → sub w2 (sub w1 x) ≡ sub (trans w1 w2) x
sub-chain refl refl = refl

sub-move : {l : Level} {A B C : Set l} 
    → {x : A} {y : B}
    → (w1 : A ≡ C) (w2 : B ≡ C)
    → x ≡ sub (trans w2 (sym w1)) y
    → sub w1 x ≡ sub w2 y
sub-move refl refl refl = refl

sub-irrel : {l : Level} {A B : Set l}
    → {w0 : A ≡ B}
    → (w1 : A ≡ B)
    → (x : A)
    → sub w0 x ≡ sub w1 x
sub-irrel {w0 = refl} refl x = refl

sub-cong : {l : Level} {A B : Set l} 
    → {x : A} {y : A}
    → ( w1 : A ≡ B ) ( w2 : A ≡ B )
    → x ≡ y
    → (sub w1 x) ≡ (sub w2 y)
sub-cong refl refl refl = refl

Etup-D1τ-distr≡ : ( Γ : Env Pr ) → (D1τ (Etup Pr Γ)) ≡ (Etup Du (map D1τ Γ))
Etup-D1τ-distr≡ ( [] ) = refl
Etup-D1τ-distr≡ ( τ ∷ Γ ) = cong₂ _:*_ refl (Etup-D1τ-distr≡ Γ)

Etup-D1τ-distr₁ : ( Γ : Env Pr ) → Rep (D1τ (Etup Pr Γ)) → Rep (Etup Du (map D1τ Γ))
Etup-D1τ-distr₁ Γ x
  = sub (cong Rep (Etup-D1τ-distr≡ Γ)) x

Etup-D1τ-distr₂ : ( Γ : Env Pr ) → Rep (Etup Du (map D1τ Γ)) → Rep (D1τ (Etup Pr Γ))
Etup-D1τ-distr₂ Γ x
  = sub (cong Rep (sym $ Etup-D1τ-distr≡ Γ)) x
