module correctness.chad-ctg-zero where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt; ⊤)
open import Agda.Builtin.Maybe using (just; nothing)
open import Data.Empty using (⊥)
open import Data.List using (map; _∷_; [])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)

open import spec
import spec.LACM as LACM
open import correctness.spec
open import correctness.lemmas
open import correctness.chad-preserves-compatibility
open import chad-preserves-primal

addLEτ-ctg-zero : {Γ : Env Pr} {τ : Typ Pr}
    → (idx : Idx Γ τ)
      (evIn : LETs (map D2τ' Γ) )
      (ctg : LinRep (D2τ' τ))
    → ( Compatible-idx-LETs (idx , ctg) evIn )
    → ( sparse2dense ctg ≡ zerovDense (D2τ' τ) )
    → LETs2d (addLEτ (convIdx D2τ' idx) ctg evIn)
      ≡ LETs2d evIn
addLEτ-ctg-zero {Γ} Z evIn ctg w≃ w = cong₂ _,_ (trans (plusv-equiv-plusvDense ctg (evIn .fst) w≃) (plusvDense-zeroL' {{w}})) refl
addLEτ-ctg-zero {Γ} (S idx) evIn ctg w≃ w = cong₂ _,_ refl (addLEτ-ctg-zero idx (evIn .snd) ctg w≃ w)

dprim'-ctg-zero : {σ τ : Typ Pr}
    → (x : Rep σ)
    → (ctg : LinRep (D2τ' τ))
    → (sparse2dense ctg ≡ zerovDense (D2τ' τ))
    → let d-op-env = (push ctg (push (primal σ x) empty)) in
        (op : Primop Pr σ τ )
    →  sparse2dense (interp (dprim' op) d-op-env)
        ≡ zerovDense (D2τ' σ)
dprim'-ctg-zero x ctg refl ADD = refl
dprim'-ctg-zero x ctg refl MUL = cong₂ _,_ (primFloatTimes-identityL (x .snd)) (primFloatTimes-identityL (x .fst))
dprim'-ctg-zero x ctg refl NEG = primFloatNegativeZero
dprim'-ctg-zero x ctg w (LIT _) = refl
dprim'-ctg-zero x ctg w IADD = refl
dprim'-ctg-zero x ctg w IMUL = refl
dprim'-ctg-zero x ctg w INEG = w
dprim'-ctg-zero x ctg w SIGN = refl

chad-ctg-zero : {Γ : Env Pr} {τ : Typ Pr} 
    →  let LΓ = map D2τ' Γ
    in (val : Val Pr Γ) -- input of function
    → (evIn : LETs LΓ ) -- incoming LETs
    → (ctg : LinRep (D2τ' τ)) -- incoming cotangent
    → (t : Term Pr Γ τ) -- primal function
    → ( ctg  ≃τ (interp t val)) -- compatible incoming cotangent
    → ( evIn ≃Γ val ) -- compatible incoming LETs
    → ( sparse2dense ctg ≡ zerovDense (D2τ' τ) ) -- a witness to the fact that the cotangent is semantically a zero value
    →   LETs2d {LΓ} (LACMexec (interp (chad t) (primalVal val) .snd ctg .fst ) evIn)
        ≡ LETs2d {LΓ} evIn
chad-ctg-zero {Γ} val evIn ctg unit _ _ _
  rewrite LACMexec-pure tt evIn
  = refl
chad-ctg-zero {Γ} val evIn ctg (var x) ~τ ~Γ w
  rewrite LACMexec-add (convIdx D2τ' x) ctg evIn
  = let ~evIn-val = ≃τ-and-≃Γ-implies-Compatible-idx-LETs x ctg evIn val ~τ ~Γ
    in addLEτ-ctg-zero x evIn ctg ~evIn-val w 
chad-ctg-zero {Γ} val evIn nothing (pair {σ = σ} {τ = τ} l r) ~τ ~Γ w
  using l' ← interp (chad l) (primalVal val) .snd (zerov (D2τ' σ) .fst) .fst
  using r' ← interp (chad r) (primalVal val) .snd (zerov (D2τ' τ) .fst) .fst
  rewrite LACMexec-sequence l' r' evIn
  rewrite chad-ctg-zero val (LACMexec l' evIn) (zerov (D2τ' τ) .fst) r (≃τ-zerov' τ ) (chad-preserves-≃Γ val evIn (zerov (D2τ' σ) .fst) l (≃τ-zerov σ (interp l val)) ~Γ) (zerov-equiv-zerovDense (D2τ' τ))
  rewrite chad-ctg-zero val evIn (zerov (D2τ' σ) .fst) l ( ≃τ-zerov' σ ) ~Γ (zerov-equiv-zerovDense (D2τ' σ))
  = refl
chad-ctg-zero {Γ} val evIn (just (ctgL , ctgR)) (pair {σ = σ} {τ = τ} l r) ~τ ~Γ w
  using l' ← interp (chad l) (primalVal val) .snd ctgL .fst
  using r' ← interp (chad r) (primalVal val) .snd ctgR .fst
  rewrite LACMexec-sequence l' r' evIn
  rewrite chad-ctg-zero val (LACMexec l' evIn) ctgR r (~τ .snd) (chad-preserves-≃Γ val evIn ctgL l (~τ .fst) ~Γ) (cong snd w)
  rewrite chad-ctg-zero val evIn ctgL l (~τ .fst) ~Γ (cong fst w)
  = refl
chad-ctg-zero {Γ} val evIn ctg (fst' {σ = σ} {τ = τ} t) ~τ ~Γ w
  rewrite simplify-exec-chad-fst val evIn ctg t
  = chad-ctg-zero val evIn (just ( ctg , zerov (D2τ' τ) .fst)) t (~τ , (≃τ-zerov' τ)) ~Γ (cong₂ _,_ w (zerov-equiv-zerovDense (D2τ' τ)))
chad-ctg-zero {Γ} val evIn ctg (snd' {σ = σ} t) ~τ ~Γ w
  rewrite simplify-exec-chad-snd val evIn ctg t
  = chad-ctg-zero val evIn (just (zerov (D2τ' σ) .fst , ctg)) t (≃τ-zerov' σ , ~τ) ~Γ (cong₂ _,_ (zerov-equiv-zerovDense (D2τ' σ)) w)
chad-ctg-zero {Γ} val evIn ctg (let' {σ = σ} {τ = τ}  rhs body) ~τ ~Γ w
  rewrite simplify-exec-chad-let val id evIn ctg rhs body
  = let ih-body = chad-ctg-zero (push (interp rhs val) val) (zerov (D2τ' σ) .fst , evIn) ctg body ~τ (≃Γ-intro-zero' σ evIn ~Γ) w
        preserves≃Γ = chad-preserves-≃Γ (push (interp rhs val) val) (zerov (D2τ' σ) .fst , evIn) ctg body ~τ (≃Γ-intro-zero' σ evIn ~Γ)
        body' = LACMexec (interp (chad body) (push (primal σ (interp rhs val)) (primalVal val)) .snd ctg .fst) (zerov (D2τ' σ) .fst , evIn)
        ih-rhs = chad-ctg-zero val _ _ rhs (fst preserves≃Γ) (snd preserves≃Γ) (trans (cong fst ih-body) (zerov-equiv-zerovDense (D2τ' σ)))
    in trans ih-rhs (cong snd ih-body)
chad-ctg-zero {Γ} val evIn ctg (prim {σ = σ} {τ = τ} op t) ~τ ~Γ w
  rewrite simplify-exec-chad-primop val evIn ctg t op
  = let d-op-env = push ctg (push (primal σ (interp t val)) empty)
    in chad-ctg-zero val evIn (interp (dprim' op) d-op-env) t (dprim'-preserves-≃τ val ctg op t ~τ) ~Γ (dprim'-ctg-zero (interp t val) ctg w op)
chad-ctg-zero {Γ} val evIn nothing (inl {σ = σ} t) ~τ ~Γ w 
  = chad-ctg-zero val evIn (zerov (D2τ' σ) .fst) t (≃τ-zerov' σ) ~Γ (zerov-equiv-zerovDense (D2τ' σ))
chad-ctg-zero {Γ} val evIn (just (inj₁ ctg)) (inl {σ = σ} t) ~τ ~Γ w
  = chad-ctg-zero val evIn ctg t ~τ ~Γ (cong fst w) 
chad-ctg-zero {Γ} val evIn nothing (inr {τ = τ} t) ~τ ~Γ w 
  = chad-ctg-zero val evIn (zerov (D2τ' τ) .fst) t (≃τ-zerov' τ) ~Γ (zerov-equiv-zerovDense (D2τ' τ))
chad-ctg-zero {Γ} val evIn (just (inj₂ ctg)) (inr {τ = τ} t) ~τ ~Γ w
  = chad-ctg-zero val evIn ctg t ~τ ~Γ (cong snd w) 
chad-ctg-zero {Γ} val evIn ctg (case' {σ = σ} {τ = τ} {ρ = ρ} e l r) ~τ ~Γ w
  rewrite chad-preserves-primal val e
  with interp e val in interp-e-val≡inj-x 
... | inj₁ x 
  rewrite simplify-exec-chad-case val evIn ctg e l x inj₁
  = trans ih-e (cong snd ih-l)
  where l' = LACMexec (interp (chad l) (push (primal σ x) (primalVal val)) .snd ctg .fst) (zerov (D2τ' σ) .fst , evIn)
        preserves≃Γ = chad-preserves-≃Γ (push x val) (zerov (D2τ' σ) .fst , evIn) ctg l ~τ (≃Γ-intro-zero' σ evIn ~Γ)
        w1' = ≃τ-congR (σ :+ τ) (just (inj₁ (l' .fst))) (inj₁ x) (interp e val) (sym interp-e-val≡inj-x) (fst preserves≃Γ)
        ih-l = chad-ctg-zero (push x val) (zerov (D2τ' σ) .fst , evIn) ctg l ~τ (≃Γ-intro-zero' σ evIn ~Γ) w
        ih-e = chad-ctg-zero val _ _ e w1' (snd preserves≃Γ) (cong₂ _,_ (trans (cong fst ih-l) (zerov-equiv-zerovDense (D2τ' σ))) refl)   
... | inj₂ x
  rewrite simplify-exec-chad-case val evIn ctg e r x inj₂
  = trans ih-e (cong snd ih-r)
  where r' = LACMexec (interp (chad r) (push (primal τ x) (primalVal val)) .snd ctg .fst) (zerov (D2τ' τ) .fst , evIn)
        preserves≃Γ = chad-preserves-≃Γ (push x val) (zerov (D2τ' τ) .fst , evIn) ctg r ~τ (≃Γ-intro-zero' τ evIn ~Γ)
        w1' = ≃τ-congR (σ :+ τ) (just (inj₂ (r' .fst))) (inj₂ x) (interp e val) (sym interp-e-val≡inj-x) (fst preserves≃Γ)
        ih-r = chad-ctg-zero (push x val) (zerov (D2τ' τ) .fst , evIn) ctg r ~τ (≃Γ-intro-zero' τ evIn ~Γ) w
        ih-e = chad-ctg-zero val _ _ e w1' (snd preserves≃Γ) (cong₂ _,_ refl (trans (cong fst ih-r) (zerov-equiv-zerovDense (D2τ' τ))))   