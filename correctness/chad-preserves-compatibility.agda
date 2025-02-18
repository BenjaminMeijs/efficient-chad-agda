module correctness.chad-preserves-compatibility where

open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (tt)
open import Agda.Builtin.Maybe using (just; nothing)
open import Data.List using (_∷_; map)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (sym; inspect; [_])

open import spec
open import correctness.spec
open import correctness.lemmas.value-compatibility-lemmas
open import correctness.lemmas.simplify-exec-chad
open import correctness.lemmas.LACMexec-lemmas
open import chad-preserves-primal

-- ===============================
-- Operations preserving compatibility
-- ===============================
plusv-preserves-≃τ : {τ : Typ Pr}
    → (x : LinRep (D2τ' τ)) (y : LinRep (D2τ' τ)) (z : Rep τ)
    → (Compatible-LinReps x y) → (x ≃τ z) → (y ≃τ z)
    → fst (plusv (D2τ' τ) x y) ≃τ z
plusv-preserves-≃τ {Un} _ _ _ _ _ _ = tt
plusv-preserves-≃τ {Inte} _ _ _ _ _ _ = tt
plusv-preserves-≃τ {R} _ _ _ _ _ _ = tt
plusv-preserves-≃τ {σ :* τ} (just x) (just x₁) z w1 w2 w3
    = plusv-preserves-≃τ (x .fst) (x₁ .fst) (z .fst) (w1 .fst) (w2 .fst) (w3 .fst) , plusv-preserves-≃τ (x .snd) (x₁ .snd) (z .snd) (w1 .snd) (w2 .snd) (w3 .snd)
plusv-preserves-≃τ {σ :* τ} (just (x , xs)) nothing (z , zs) tt w2 w3 = w2 .fst , w2 .snd
plusv-preserves-≃τ {σ :* τ} nothing (just (y , ys)) (z , zs) w1 w2 w3 = w3 .fst , w3 .snd
plusv-preserves-≃τ {σ :* τ} nothing nothing _ _ _ _ = tt
plusv-preserves-≃τ {σ :+ τ} (just (inj₁ x)) (just (inj₁ x₁)) (inj₁ x₂) w1 w2 w3 = plusv-preserves-≃τ x x₁ x₂ w1 w2 w3
plusv-preserves-≃τ {σ :+ τ} (just (inj₂ y₁)) (just (inj₂ y₂)) (inj₂ y) w1 w2 w3 = plusv-preserves-≃τ y₁ y₂ y w1 w2 w3
plusv-preserves-≃τ {σ :+ τ} (just _) nothing (inj₁ x₁) w1 w2 w3 = w2
plusv-preserves-≃τ {σ :+ τ} (just _) nothing (inj₂ y) w1 w2 w3 = w2
plusv-preserves-≃τ {σ :+ τ} nothing (just _) (inj₁ _) w1 w2 w3 = w3
plusv-preserves-≃τ {σ :+ τ} nothing (just _) (inj₂ _) w1 w2 w3 = w3
plusv-preserves-≃τ {σ :+ τ} nothing nothing (inj₁ _) w1 w2 w3 = tt
plusv-preserves-≃τ {σ :+ τ} nothing nothing (inj₂ _) w1 w2 w3 = tt

addLEτ-preserves-≃Γ : {Γ : Env Pr} {τ : Typ Pr}
            → (idx : Idx Γ τ) (ctg : LinRep (D2τ' τ)) (evIn : LEtup (map D2τ' Γ)) (val : Val Pr Γ)
            → (evIn ≃Γ val) → (Compatible-idx-LEtup (idx , ctg) evIn) → (Compatible-idx-val (idx , ctg) val)
            → addLEτ (convIdx D2τ' idx) ctg evIn ≃Γ val
addLEτ-preserves-≃Γ {Un ∷ Γ} Z ctg (x , xs) (push y val) w _ _ = w
addLEτ-preserves-≃Γ {Inte ∷ Γ} Z ctg (x , xs) (push y val) w _ _ = w
addLEτ-preserves-≃Γ {R ∷ Γ} Z ctg (x , xs) (push y val) w _ _ = w
addLEτ-preserves-≃Γ {(σ :* τ) ∷ Γ} Z ctg (x , xs) (push y val) w1 w2 w3 = plusv-preserves-≃τ {σ :* τ} ctg x y w2 w3 (w1 .fst) , (w1 .snd)
addLEτ-preserves-≃Γ {(σ :+ τ) ∷ Γ} Z ctg (x , xs) (push y val) w1 w2 w3 = plusv-preserves-≃τ {σ :+ τ} ctg x y w2 w3 (w1 .fst) , (w1 .snd)
addLEτ-preserves-≃Γ {Un ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = addLEτ-preserves-≃Γ idx ctg xs val w1 w2 w3 
addLEτ-preserves-≃Γ {Inte ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = addLEτ-preserves-≃Γ idx ctg xs val w1 w2 w3 
addLEτ-preserves-≃Γ {R ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = addLEτ-preserves-≃Γ idx ctg xs val w1 w2 w3 
addLEτ-preserves-≃Γ {(σ :* τ) ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = w1 .fst , addLEτ-preserves-≃Γ idx ctg xs val (w1 .snd) w2 w3 
addLEτ-preserves-≃Γ {(σ :+ τ) ∷ Γ} (S idx) ctg (x , xs) (push y val) w1 w2 w3 = w1 .fst , addLEτ-preserves-≃Γ idx ctg xs val (w1 .snd) w2 w3

dprim'-preserves-≃τ : {Γ : Env Pr} {σ τ : Typ Pr}
      (val : Val Pr Γ) (ctg : LinRep (D2τ' τ)) (op : Primop Pr σ τ) (t : Term Pr Γ σ) 
    → ctg ≃τ evalprim op (interp t val)
    → let d-op-env = push ctg (push (primal σ (interp t val)) empty)
      in interp (dprim' op) d-op-env ≃τ interp t val
dprim'-preserves-≃τ val ctg ADD t w = tt , tt
dprim'-preserves-≃τ val ctg MUL t w = tt , tt
dprim'-preserves-≃τ val ctg NEG t w = tt
dprim'-preserves-≃τ val ctg (LIT x) t w = tt
dprim'-preserves-≃τ val ctg IADD t w = tt , tt
dprim'-preserves-≃τ val ctg IMUL t w = tt , tt
dprim'-preserves-≃τ val ctg INEG t w = tt
dprim'-preserves-≃τ val ctg SIGN t w = tt

-- ===============================
-- CHAD preserves compatibility
-- ===============================
chad-preserves-≃Γ : {Γ : Env Pr} {τ : Typ Pr} 
                → (val : Val Pr Γ)
                  (evIn : LEtup (map D2τ' Γ) )
                  (ctg : LinRep (D2τ' τ))
                  (t : Term Pr Γ τ)
                → ctg ≃τ (interp t val)
                → evIn ≃Γ val
                → LACMexec (interp (chad t) (primalVal val) .snd ctg .fst ) evIn ≃Γ val
chad-preserves-≃Γ _ evIn _ unit _ w2
  rewrite LACMexec-pure tt evIn = w2
chad-preserves-≃Γ {Γ} val evIn ctg (var x) w1 w2
  using idx ← convIdx D2τ' x
  rewrite LACMexec-add idx ctg evIn
  = let ≃evIn-etup = ≃τ-and-≃Γ-implies-Compatible-idx-LEtup x ctg evIn val w1 w2 
        ≃evIn-val = ≃τ-and-≃Γ-implies-Compatible-idx-val x ctg evIn val w1 w2 
    in addLEτ-preserves-≃Γ x ctg evIn val w2 ≃evIn-etup ≃evIn-val
chad-preserves-≃Γ {Γ} val evIn nothing (pair {σ = σ} {τ = τ} l r) w1 w2
  using l' ← interp (chad l) (primalVal val) .snd (zerov (D2τ' σ) .fst) .fst
  using r' ← interp (chad r) (primalVal val) .snd (zerov (D2τ' τ) .fst) .fst
  rewrite LACMexec-sequence l' r' evIn
  = let ihl = chad-preserves-≃Γ val evIn (zerov (D2τ' σ) .fst) l (≃τ-zerov σ (interp l val)) w2
    in chad-preserves-≃Γ val (LACMexec l' evIn) (zerov (D2τ' τ) .fst) r (≃τ-zerov τ (interp r val)) ihl
chad-preserves-≃Γ {Γ} val evIn (just (ctgL , ctgR)) (pair l r) w1 w2
  using l' ← interp (chad l) (primalVal val) .snd ctgL .fst
  using r' ← interp (chad r) (primalVal val) .snd ctgR .fst
  rewrite LACMexec-sequence l' r' evIn
  = let ihl = chad-preserves-≃Γ val evIn ctgL l (w1 .fst) w2
    in chad-preserves-≃Γ val (LACMexec l' evIn) ctgR r (w1 .snd) ihl
chad-preserves-≃Γ {Γ} val evIn ctg (fst' {σ = σ} {τ = τ} t) w1 w2
  rewrite simplify-exec-chad-fst val evIn ctg t
  = chad-preserves-≃Γ val evIn (just (ctg , zerov (D2τ' τ) .fst)) t (w1 , (≃τ-zerov τ (interp t val .snd))) w2
chad-preserves-≃Γ {Γ} val evIn ctg (snd' {σ = σ} {τ = τ} t) w1 w2
  rewrite simplify-exec-chad-snd val evIn ctg t
  = chad-preserves-≃Γ val evIn (just (zerov (D2τ' σ) .fst , ctg)) t ((≃τ-zerov σ (interp t val .fst)) , w1) w2
chad-preserves-≃Γ {Γ} val evIn ctg (let' {σ = σ} {τ = τ} rhs body) w1 w2
  rewrite simplify-exec-chad-let val id evIn ctg rhs body
  =  let ev = (zerov (D2τ' σ) .fst , evIn)
         ih = chad-preserves-≃Γ (push (interp rhs val) val) ev ctg body
                                 w1 (≃Γ-intro-zero {Γ} {σ} evIn val (interp rhs val) w2)
         body' = LACMexec ((interp (chad body) (push (primal σ (interp rhs val)) (primalVal val)) .snd ctg .fst)) ev 
     in chad-preserves-≃Γ val (body' .snd) (body' .fst) rhs
        (≃Γ-fst body' (interp rhs val) val ih) (≃Γ-snd body' (interp rhs val) val ih)
chad-preserves-≃Γ {Γ} val evIn ctg (prim {σ = σ} {τ = τ} op t) w1 w2
  rewrite simplify-exec-chad-primop val evIn ctg t op
  = let d-op-env = push ctg (push (primal σ (interp t val)) empty)
    in chad-preserves-≃Γ val evIn (interp (dprim' op) d-op-env) t (dprim'-preserves-≃τ val ctg op t w1) w2
chad-preserves-≃Γ {Γ} val evIn nothing (inl {σ = σ} {τ = τ} t) w1 w2
  = chad-preserves-≃Γ val evIn (zerov (D2τ' σ) .fst) t (≃τ-zerov σ (interp t val)) w2
chad-preserves-≃Γ {Γ} val evIn (just (inj₁ ctg)) (inl t) w1 w2
  = chad-preserves-≃Γ val evIn ctg t w1 w2
chad-preserves-≃Γ {Γ} val evIn nothing (inr {σ = σ} {τ = τ} t) w1 w2
  = chad-preserves-≃Γ val evIn (zerov (D2τ' τ) .fst) t (≃τ-zerov τ (interp t val)) w2
chad-preserves-≃Γ {Γ} val evIn (just (inj₂ ctg)) (inr t) w1 w2
  = chad-preserves-≃Γ val evIn ctg t w1 w2
chad-preserves-≃Γ {Γ} val evIn ctg (case' {σ = σ} {τ = τ} {ρ = ρ}  e l r) w1 w2
  rewrite chad-preserves-primal val e
  with interp e val | inspect (interp e) val
... | inj₁ x | [ interp-e-val≡inj₁-x ]
  rewrite simplify-exec-chad-case val evIn ctg e l x inj₁
  = let l' = LACMexec (interp (chad l) (push (primal σ x) (primalVal val)) .snd ctg .fst) (zerov (D2τ' σ) .fst , evIn)
        ih = chad-preserves-≃Γ (push x val) (zerov (D2τ' σ) .fst , evIn) ctg l w1 (≃Γ-intro-zero {τ = σ} evIn val x w2)
        w1' = ≃τ-congR (σ :+ τ) (just (inj₁ (l' .fst))) (inj₁ x) (interp e val) (sym interp-e-val≡inj₁-x) (≃Γ-fst l' x val ih)
    in chad-preserves-≃Γ val (l' .snd) (just (inj₁ (l' .fst))) e w1' (≃Γ-snd l' x val ih)
... | inj₂ x | [ interp-e-val≡inj₂-x ]
  rewrite simplify-exec-chad-case val evIn ctg e r x inj₂
  = let r' = LACMexec (interp (chad r) (push (primal τ x) (primalVal val)) .snd ctg .fst) (zerov (D2τ' τ) .fst , evIn)
        ih = chad-preserves-≃Γ (push x val) (zerov (D2τ' τ) .fst , evIn) ctg r w1 (≃Γ-intro-zero {τ = τ} evIn val x w2)
        w1' = ≃τ-congR (σ :+ τ) (just (inj₂ (r' .fst))) (inj₂ x) (interp e val) (sym interp-e-val≡inj₂-x) (≃Γ-fst r' x val ih)
    in chad-preserves-≃Γ val (r' .snd) (just (inj₂ (r' .fst))) e w1' (≃Γ-snd r' x val ih)