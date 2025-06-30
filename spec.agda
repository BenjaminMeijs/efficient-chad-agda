module spec where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Float
  using (Float; primFloatPlus; primFloatTimes; primFloatNegate; primFloatLess)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (nothing; just; maybe′)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Integer using (ℤ; _+_; _-_; _*_; -_; +_; _≤_)
open import Data.Product using (_×_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Bool using (if_then_else_)
open import Data.Empty using (⊥)
open import Function.Base using (id; _$_; _∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)

open import Relation.Nullary.Decidable using (Dec; dec⇒maybe; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import spec.linear-types public
import spec.LACM as LACM
open LACM using (LACM)


-------------------- UTILITY FUNCTIONS -----------------------------------------

-- Project from a list with a bounded index into that list. Not sure why this
-- is not in the standard library for lists.
_!!_ : ∀ {n} {a : Set n} -> (l : List a) -> Fin (length l) -> a
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc i = xs !! i


-------------------- TYPES -----------------------------------------------------
-- Linear types were already defined in spec.linear-types; here are the
-- regular, non-linear types.

-- Types are indexed by whether they are primal types (i.e. types that occur in
-- the source program) or dual types (i.e. types that occur in the target
-- program).
data PDTag : Set where
  Pr Du : PDTag

-- The types of the object language. The source language is typed by
-- 'Typ Pr', which allows only a few types. The target language is typed by
-- 'Typ Du', which allows not only the source language types but also a couple
-- of other types, including functions and the linear types.
data Typ : PDTag -> Set where
  Un Inte R : ∀ {tag} -> Typ tag
  _:*_ : ∀ {tag} -> Typ tag -> Typ tag -> Typ tag
  _:+_ : ∀ {tag} -> Typ tag -> Typ tag -> Typ tag
  _:->_ : ∀ {tag} -> Typ tag -> Typ tag -> Typ tag

  -- Environment vector monad. This is the same EVM as in the paper; the
  -- implementation is LACM.
  EVM : LEnv -> Typ Du -> Typ Du

  -- The linear types (with embedded potential)
  Lin : LTyp -> Typ Du

_Typ≟_ : ∀ {tag} → ( x y : Typ tag ) → Dec ( x ≡ y)
-- Implementation of decidable equality is given at the bottom of the file

-- A normal typing environment is a list of types.
Env : PDTag -> Set
Env tag = List (Typ tag)

-- The representation / semantics of our types. LinRep from spec.linear-types
-- does the same for the linear types LTyp.
Rep : ∀ {tag} -> Typ tag -> Set
Rep Un = ⊤
Rep Inte = ℤ
Rep R = Float
Rep (σ :* τ) = Rep σ × Rep τ
Rep (σ :+ τ) = Rep σ ⊎ Rep τ
Rep (σ :-> τ) = Rep σ -> Rep τ × ℤ
Rep (EVM Γ τ) = LACM Γ (Rep τ)
Rep (Lin τ) = LinRep τ

-- Convert a type from a source-language type to a target-language type. This
-- function is operationally the identity.
dut : Typ Pr -> Typ Du
dut Un = Un
dut Inte = Inte
dut R = R
dut (σ :* τ) = dut σ :* dut τ
dut (σ :+ τ) = dut σ :+ dut τ
dut (σ :-> τ) = dut σ :-> dut τ

-- The embedded counterpart of LEtup: a tuple of all the types in a linear
-- environment. This is used to pass a linear environment as a _value_ into,
-- and out of, the monadic computation in the target program.
LEτ : LEnv -> Typ Du
LEτ [] = Un
LEτ (τ ∷ Γ) = Lin τ :* LEτ Γ

-- LEtup and ⟦LEτ⟧ are the same thing.
LEtup-eq-LEτ : (Γ : LEnv) -> Rep (LEτ Γ) ≡ LEtup Γ
LEtup-eq-LEτ [] = refl
LEtup-eq-LEτ (τ ∷ Γ) rewrite LEtup-eq-LEτ Γ = refl

LEtup-to-LEτ : (Γ : LEnv) -> Rep (LEτ Γ) -> LEtup Γ
LEtup-to-LEτ Γ x = subst (λ x → x) (LEtup-eq-LEτ Γ) x

LEτ-to-LEtup : (Γ : LEnv) -> LEtup Γ -> Rep (LEτ Γ)
LEτ-to-LEtup Γ x = subst id (sym $ LEtup-eq-LEτ Γ) x

LEτ-to-LEτLtyp : {Γ : LEnv} → Rep (LEτ Γ) → ( LinRep (LEτLtyp Γ) × ℤ)
LEτ-to-LEτLtyp  {[]} x = (tt , one)
LEτ-to-LEτLtyp  {τ ∷ Γ} (x , xs) = 
  let (ys , c) = LEτ-to-LEτLtyp xs
  in just (x , ys) , one + c


-------------------- PRIMITIVE OPERATIONS --------------------------------------

-- The primitive operations in our object language. Again, some operations are
-- available both in the source and in the target language, whereas others (the
-- 'Du'-indexed ones) are available only in the target language.
data Primop : (tag : PDTag) -> (σ τ : Typ tag) -> Set where
  ADD  : ∀ {tag} -> Primop tag (R :* R) R
  MUL  : ∀ {tag} -> Primop tag (R :* R) R
  NEG  : ∀ {tag} -> Primop tag R R
  LIT  : ∀ {tag} -> Float -> Primop tag Un R
  IADD : ∀ {tag} -> Primop tag (Inte :* Inte) Inte
  IMUL : ∀ {tag} -> Primop tag (Inte :* Inte) Inte
  INEG : ∀ {tag} -> Primop tag Inte Inte
  -- sign: (negative or positive) or zero/NaN
  SIGN : ∀ {tag} -> Primop tag R ((Un :+ Un) :+ Un)

  LZERO  : Primop Du (Lin LUn) (Lin LR)
  LADD   : Primop Du (Lin LR :* Lin LR) (Lin LR)
  LSCALE : Primop Du (Lin LR :* R) (Lin LR)
  LNEG   : Primop Du (Lin LR) (Lin LR)

-- Semantics of the primitive operations.
evalprim : ∀ {tag} {σ τ} -> Primop tag σ τ -> Rep σ -> Rep τ
evalprim ADD (x , y) = primFloatPlus x y
evalprim MUL (x , y) = primFloatTimes x y
evalprim NEG x = primFloatNegate x
evalprim (LIT x) tt = x
evalprim IADD (x , y) = x + y
evalprim IMUL (x , y) = x * y
evalprim INEG x = - x
evalprim SIGN x =
  case primFloatLess x 0.0 of
    λ where true  -> inj₁ (inj₁ tt)
            false -> case primFloatLess 0.0 x of
                       λ where true  -> inj₁ (inj₂ tt)
                               false -> inj₂ tt
evalprim LZERO tt = 0.0
evalprim LADD (x , y) = primFloatPlus x y
evalprim LSCALE (x , y) = primFloatTimes x y
evalprim LNEG x = primFloatNegate x

-- The dual type mapping, written D[τ]₂ in the paper. Dual types are linear
-- (i.e. have a monoid structure).
D2τ' : Typ Pr -> LTyp
D2τ' Un = LUn
D2τ' Inte = LUn
D2τ' R = LR
D2τ' (σ :* τ) = D2τ' σ :*! D2τ' τ
D2τ' (σ :+ τ) = D2τ' σ :+! D2τ' τ
D2τ' (σ :-> τ) = Dyn

-- Dual type as a target language type.
D2τ : Typ Pr -> Typ Du
D2τ τ = Lin (D2τ' τ)

-- The codomain of the backpropagator of a differentiated program. 'EVM' is the
-- environment vector monad, instantiated with the local accumulation monad
-- LACM. 'D2Γ' is used in the type of 'chad' below.
D2Γ : Env Pr -> Typ Du
D2Γ Γ = EVM (map D2τ' Γ) Un

-- The primal type mapping, written D[τ]₁ in the paper.
D1τ : Typ Pr -> Typ Du
D1τ Un = Un
D1τ Inte = Inte
D1τ R = R
D1τ (σ :* τ) = D1τ σ :* D1τ τ
D1τ (σ :+ τ) = D1τ σ :+ D1τ τ
D1τ (σ :-> τ) = D1τ σ :-> (D1τ τ :* (D2τ τ :-> Lin (D2τ' σ :*! Dyn) ))

-- Primal environment mapping. This is D[Γ]₁ in the paper.
D1Γ : Env Pr -> Env Du
D1Γ = map D1τ

-- Dual environment mapping. Recall LEτ from above. This is \overline{D[Γ]₂} in
-- the paper.
D2Γtup : Env Pr -> Typ Du
D2Γtup Γ = LEτ (map D2τ' Γ)

-------------------- OBJECT LANGUAGE -------------------------------------------

-- The object language. The source language and the target language are both
-- expressed using the same Term data type, just with a different index: a
-- source term is of type 'Term Pr Γ τ', whereas a target term is of type
-- 'Term Du Γ τ'.
data Term : (tag : PDTag) -> (Γ : Env tag) -> (τ : Typ tag) -> Set where
  var   : ∀ {tag} {Γ : Env tag} {τ : Typ tag}
        -> Idx Γ τ -> Term tag Γ τ
  let'  : ∀ {tag} {Γ : Env tag} {σ τ : Typ tag}
        -> Term tag Γ σ -> Term tag (σ ∷ Γ) τ -> Term tag Γ τ

  prim  : ∀ {tag} {Γ : Env tag} {σ τ : Typ tag}
        -> Primop tag σ τ -> Term tag Γ σ -> Term tag Γ τ

  unit  : ∀ {tag} {Γ : Env tag}
        -> Term tag Γ Un

  pair  : ∀ {tag} {Γ : Env tag} {σ τ : Typ tag}
        -> Term tag Γ σ -> Term tag Γ τ -> Term tag Γ (σ :* τ)
  fst'  : ∀ {tag} {Γ : Env tag} {σ τ : Typ tag}
        -> Term tag Γ (σ :* τ) -> Term tag Γ σ
  snd'  : ∀ {tag} {Γ : Env tag} {σ τ : Typ tag}
        -> Term tag Γ (σ :* τ) -> Term tag Γ τ

  inl   : ∀ {tag} {Γ : Env tag} {σ τ : Typ tag}
        -> Term tag Γ σ -> Term tag Γ (σ :+ τ)
  inr   : ∀ {tag} {Γ : Env tag} {σ τ : Typ tag}
        -> Term tag Γ τ -> Term tag Γ (σ :+ τ)
  case' : ∀ {tag} {Γ : Env tag} {σ τ ρ : Typ tag}
        -> Term tag Γ (σ :+ τ)
        -> Term tag (σ ∷ Γ) ρ -> Term tag (τ ∷ Γ) ρ
        -> Term tag Γ ρ

  fromDyn : {Γ : Env Du} {τ : LTyp} 
        -> Term Du Γ (Lin Dyn)
        -> Term Du Γ (Lin τ)

  toDyn : {Γ : Env Du} { τ : LTyp } 
         -> Term Du Γ (Lin τ)
         -> Term Du Γ (Lin Dyn)

  addFromDynEvm : {Γ : Env Du} {Γ' : LEnv}
        -> Term Du Γ (Lin Dyn)
        -> Term Du Γ (EVM Γ' Un)

  toDynEvm : {Γ : Env Du} {Γ' : LEnv}
        -> Term Du Γ (LEτ Γ')
        -> Term Du Γ (Lin Dyn)

  dynZero : {Γ : Env Du} 
            -> Term Du Γ (Lin Dyn)
  
  lam : ∀ {tag} {σ τ : Typ tag}
        -> { Γ : Env tag } -> Term tag (σ ∷ Γ) τ -> Term tag Γ (σ :-> τ)

  app : ∀ {tag} {Γ : Env tag} {σ τ : Typ tag}
        -> Term tag Γ (σ :-> τ) -> Term tag Γ σ  -> Term tag Γ τ

  -- The Γ' is the closure of the lambda. We model this explicitly because the
  -- cost of evaluating 'lam' is linear in the size of its closure, so it is
  -- worth keeping it small.
  dual-lam   : {Γ : Env Du} {τ : Typ Du}
        -> {σ : Typ Du}
        -> (Γ' : Env Du) -> ({ρ : Typ Du} -> Idx Γ' ρ -> Idx Γ ρ)  -- Γ' is a subset of Γ
        -> Term Du (σ ∷ Γ') τ -> Term Du Γ (σ :-> τ)

  pureevm : {Γ : Env Du} {Γ' : LEnv} {τ : Typ Du}
         -> Term Du Γ τ -> Term Du Γ (EVM Γ' τ)
  bindevm : {Γ : Env Du} {Γ' : LEnv} {σ τ : Typ Du}
         -> Term Du Γ (EVM Γ' σ) -> Term Du Γ (σ :-> EVM Γ' τ) -> Term Du Γ (EVM Γ' τ)
  runevm : {Γ : Env Du} {Γ' : LEnv} {τ : Typ Du}
        -> Term Du Γ (EVM Γ' τ) -> Term Du Γ (LEτ Γ') -> Term Du Γ (τ :* LEτ Γ')
  addevm : {Γ : Env Du} {Γ' : LEnv} {τ : LTyp}
        -> Idx Γ' τ -> Term Du Γ (Lin τ) -> Term Du Γ (EVM Γ' Un)
  scopeevm : {Γ : Env Du} {Γ' : LEnv} {τ : LTyp} {σ : Typ Du}
          -> Term Du Γ (Lin τ) -> Term Du Γ (EVM (τ ∷ Γ') σ)
          -> Term Du Γ (EVM Γ' (Lin τ :* σ))

  lunit : {Γ : Env Du}
        -> Term Du Γ (Lin LUn)

  lpair : {Γ : Env Du} {σ τ : LTyp}
        -> Term Du Γ (Lin σ) -> Term Du Γ (Lin τ) -> Term Du Γ (Lin (σ :*! τ))
  lfst' : {Γ : Env Du} {σ τ : LTyp}
        -> Term Du Γ (Lin (σ :*! τ)) -> Term Du Γ (Lin σ)
  lsnd' : {Γ : Env Du} {σ τ : LTyp}
        -> Term Du Γ (Lin (σ :*! τ)) -> Term Du Γ (Lin τ)
  lpairzero : {Γ : Env Du} {σ τ : LTyp}
            -> Term Du Γ (Lin (σ :*! τ))

  linl : {Γ : Env Du} {σ τ : LTyp}
       -> Term Du Γ (Lin σ) -> Term Du Γ (Lin (σ :+! τ))
  linr : {Γ : Env Du} {σ τ : LTyp}
       -> Term Du Γ (Lin τ) -> Term Du Γ (Lin (σ :+! τ))
  lcastl : {Γ : Env Du} {σ τ : LTyp}
         -> Term Du Γ (Lin (σ :+! τ))
         -> Term Du Γ (Lin σ)
  lcastr : {Γ : Env Du} {σ τ : LTyp}
         -> Term Du Γ (Lin (σ :+! τ))
         -> Term Du Γ (Lin τ)
  lsumzero : {Γ : Env Du} {σ τ : LTyp}
           -> Term Du Γ (Lin (σ :+! τ))
 

-------------------- OBJECT LANGUAGE UTILITIES ---------------------------------
-- Utilities for working with the object language: weakening and some
-- alternative forms of constructors.

-- A data type representing weakenings.
--
-- The reason we have this explicit representation of reindexing mappings, as
-- opposed to a general sink function with the following type:
--   sink : {Γ Γ' : Env tag} {τ : Typ tag}
--       -> ({σ : Typ tag} -> Idx Γ σ -> Idx Γ' σ)
--       -> Term tag Γ τ -> Term tag Γ' τ
-- is that with the above representation we'd need (a very weak form of?)
-- functional extensionality to use certain lemmas in the complexity proof. The
-- reason for that is that we'd like to use multiple lemmas about the same
-- things together, and all of those lemmas return facts about terms that
-- normalise to the same thing but contain uses of 'sink' applied to unknown
-- indices inside them. If 'sink' took a function argument, then proving
-- equality here would involve proving equality of functions given equal
-- syntactic representation, which Agda does not do, despite being much weaker
-- than full functional extensionality.
--
-- This 'Weakening' type does not model all such Idx->Idx functions, but since
-- we need only a very limited set of them and this data type is sufficient to
-- describe those, we can make our lives easy and work with this simple
-- representation.
data Weakening {tag} : (Γ Γ' : Env tag) -> Set where
  WEnd  : {Γ : Env tag} -> Weakening Γ Γ
  WCut  : {Γ' : Env tag} -> Weakening [] Γ'
  WCopy : {Γ Γ' : Env tag} {τ : Typ tag} -> Weakening Γ Γ' -> Weakening (τ ∷ Γ) (τ ∷ Γ')
  WSkip : {Γ Γ' : Env tag} {τ : Typ tag} -> Weakening Γ Γ' -> Weakening Γ (τ ∷ Γ')

-- Apply a weakening to a single index.
weaken-var
  : ∀ {tag} {Γ Γ' : Env tag}
 -> (w : Weakening Γ Γ')
 -> {τ : Typ tag}
 -> Idx Γ τ
 -> Idx Γ' τ
weaken-var WEnd i = i
weaken-var (WCopy w) Z = Z
weaken-var (WCopy w) (S i) = S (weaken-var w i)
weaken-var (WSkip w) i = S (weaken-var w i)

-- Sink a term using a weakening (an index remapping). A typical special case
-- is in 'sink1' below.
sink : ∀ {tag} {Γ Γ' : Env tag}
    -> {τ : Typ tag}
    -> Weakening Γ Γ'
    -> Term tag Γ τ
    -> Term tag Γ' τ
sink w (var i) = var (weaken-var w i)
sink w (let' e1 e2) = let' (sink w e1) (sink (WCopy w) e2)
sink w (dual-lam Γ' inj e) = dual-lam Γ' (weaken-var w ∘ inj) e
sink w (app e1 e2) = app (sink w e1) (sink w e2)
sink w (prim op e) = prim op (sink w e)
sink w unit = unit
sink w (pair e1 e2) = pair (sink w e1) (sink w e2)
sink w (fst' e) = fst' (sink w e)
sink w (snd' e) = snd' (sink w e)
sink w (inl e) = inl (sink w e)
sink w (inr e) = inr (sink w e)
sink w (case' e1 e2 e3) = case' (sink w e1) (sink (WCopy w) e2) (sink (WCopy w) e3)
sink w (pureevm e) = pureevm (sink w e)
sink w (bindevm e1 e2) = bindevm (sink w e1) (sink w e2)
sink w (runevm e1 e2) = runevm (sink w e1) (sink w e2)
sink w (addevm i e) = addevm i (sink w e)
sink w (scopeevm e1 e2) = scopeevm (sink w e1) (sink w e2)
sink w lunit = lunit
sink w (lpair e1 e2) = lpair (sink w e1) (sink w e2)
sink w (lfst' e) = lfst' (sink w e)
sink w (lsnd' e) = lsnd' (sink w e)
sink w lpairzero = lpairzero
sink w (linl e) = linl (sink w e)
sink w (linr e) = linr (sink w e)
sink w (lcastl e) = lcastl (sink w e)
sink w (lcastr e) = lcastr (sink w e)
sink w lsumzero = lsumzero
sink w (lam t) = lam (sink (WCopy w) t)
sink w dynZero = dynZero
sink w (toDyn t) = toDyn (sink w t)
sink w (fromDyn t) = fromDyn (sink w t)
sink w (addFromDynEvm t) = addFromDynEvm (sink w t)
sink w (toDynEvm t) = toDynEvm (sink w t)

-- Add one additional free variable to the bottom of the term's free variable
-- list (here of type σ). This, for example, allows one to put a term under one
-- additional let-binding (whose variable is unused in the term).
sink1 : ∀ {tag} {Γ : Env tag} {σ τ : Typ tag} -> Term tag Γ τ -> Term tag (σ ∷ Γ) τ
sink1 = sink (WSkip WEnd)

-- Build a closure. The 'dual-lam' constructor in Term represents the inclusion of
-- the (smaller) closure environment into the larger containing environment
-- with an index remapping function, but writing those inline is cumbersome.
-- It's easier to simply give a list of indices into the containing environment
-- that you want to include in the closure. This 'lamwith' function allows you
-- to do that; said list is the list 'vars'. 'α' is the argument type of the
-- dual-lambda.
lamwith : {α : Typ Du} {Γ : Env Du} {τ : Typ Du}
       -> (vars : List (Fin (length Γ)))
       -> Term Du (α ∷ map (\i -> Γ !! i) vars) τ
       -> Term Du Γ (α :-> τ)
lamwith {_} {Γ} vars body =
  dual-lam (map (Γ !!_) vars)
      (buildinj vars)
      body
  where
    buildidx : {Γ : Env Du} -> (i : Fin (length Γ)) -> Idx Γ (Γ !! i)
    buildidx {[]} ()
    buildidx {_ ∷ _} zero = Z
    buildidx {_ ∷ _} (suc i) = S (buildidx i)

    buildinj : {Γ : Env Du} {ρ : Typ Du}
            -> (vars : List (Fin (length Γ)))
            -> Idx (map (\i -> Γ !! i) vars) ρ -> Idx Γ ρ
    buildinj (i ∷ vars) Z = buildidx i
    buildinj (i ∷ vars) (S idx) = buildinj vars idx

-- 'bindevm' from Term is '>>=' of the environment vector monad EVM; this is
-- '>>'. 'a >> b' is expanded to 'let x = b in a >>= \_ -> x'. Note the
-- creation of a closure using 'lamwith' containing one entry, namely x.
thenevm : {Γ : LEnv} {Γ' : Env Du}
       -> Term Du Γ' (EVM Γ Un) -> Term Du Γ' (EVM Γ Un) -> Term Du Γ' (EVM Γ Un)
thenevm a b =
  let' b $
    bindevm (sink1 a) (lamwith (zero ∷ []) (var (S Z)))

-- Generic index retyping utility. An index of type τ into an environment Γ can
-- be retyped as an index of modified type into a modified environment.
convIdx : ∀ {n} {typ typ' : Set n} {Γ : List typ} {τ : typ}
       -> (f : typ -> typ')
       -> Idx Γ τ -> Idx (map f Γ) (f τ)
convIdx f Z = Z
convIdx f (S i) = S (convIdx f i)


-------------------- DIFFERENTIATION -------------------------------------------
-- Derivative type mappings and derivatives of primitive operations.


-- Convert a _value_ of source-language type to a primal value in the
-- differentiated world. Because D1τ is the identity for non-function types,
-- this function is also the identity on values.

zeroRep : (τ : Typ Pr) → Rep τ
zeroRep Un = tt
zeroRep Inte = ℤ.pos 0
zeroRep R = 0.0
zeroRep (τ :* τ₁) = (zeroRep τ) , (zeroRep τ₁)
zeroRep (τ :+ τ₁) = inj₁ (zeroRep τ)
zeroRep (τ :-> τ₁) = λ z →
    zeroRep τ₁ , ℤ.pos 0

-- Our primitive operations work on types of which the primal is the same as
-- the original type. This is of course true for _all_ our types in this Agda
-- development, but this ceases to be true once we add function types to the
-- source language. In that situation, we would thus require that primitive
-- operations do not take or return function values.
niceprim : {σ τ : Typ Pr} -> Primop Pr σ τ -> (D1τ σ ≡ dut σ) × (D1τ τ ≡ dut τ)
niceprim ADD = refl , refl
niceprim MUL = refl , refl
niceprim NEG = refl , refl
niceprim (LIT _) = refl , refl
niceprim SIGN = refl , refl
niceprim IADD = refl , refl
niceprim IMUL = refl , refl
niceprim INEG = refl , refl

-- The reverse derivative of a primitive operation. The returned term takes as
-- input (i.e. uses in its environment) the primal of its argument and the
-- cotangent of its output, and returns the cotangent of its argument. This is
-- wrapped in a more easily-used form below in 'dprim'.
dprim' : {σ τ : Typ Pr} -> Primop Pr σ τ -> Term Du (D2τ τ ∷ D1τ σ ∷ []) (D2τ σ)
dprim' ADD = lpair (var Z) (var Z)
dprim' MUL = lpair (prim LSCALE (pair (var Z) (snd' (var (S Z)))))
                   (prim LSCALE (pair (var Z) (fst' (var (S Z)))))
dprim' NEG = prim LNEG (var Z)
dprim' (LIT x) = lunit
dprim' SIGN = prim LZERO lunit
dprim' IADD = lpair lunit lunit
dprim' IMUL = lpair lunit lunit
dprim' INEG = lunit

-- More easy to use version of dprim' above, using let-bindings to take the two
-- input terms as separate arguments.
dprim : {Γ : Env Du} {σ τ : Typ Pr}
     -> Primop Pr σ τ -> Term Du Γ (D1τ σ) -> Term Du Γ (D2τ τ) -> Term Du Γ (D2τ σ)
dprim op p d =
  let' p $
  let' (sink1 d) $
    sink (WCopy (WCopy WCut)) (dprim' op)

-- Retype a source-language primitive operation as a target-language one.
duPrim : {σ τ : Typ Pr} -> Primop Pr σ τ -> Primop Du (dut σ) (dut τ)
duPrim ADD = ADD
duPrim MUL = MUL
duPrim NEG = NEG
duPrim (LIT x) = LIT x
duPrim SIGN = SIGN
duPrim IADD = IADD
duPrim IMUL = IMUL
duPrim INEG = INEG

-- Retype a source-language primitive operation as a target-language one
-- working on primal values. This is all the same because of 'niceprim'.
d1Prim : {σ τ : Typ Pr} -> Primop Pr σ τ -> Primop Du (D1τ σ) (D1τ τ)
d1Prim {σ} {τ} op =
  subst (\t -> Primop Du t (D1τ τ)) (sym (fst (niceprim op))) $
  subst (\t -> Primop Du (dut σ) t) (sym (snd (niceprim op))) $
    duPrim op


-------------------- EVALUATION ------------------------------------------------

-- A valuation / value environment: one value for each type in the typing
-- environment.
data Val (tag : PDTag) : Env tag -> Set where
  empty : Val tag []
  push : {Γ : Env tag} {τ : Typ tag} -> Rep τ -> Val tag Γ -> Val tag (τ ∷ Γ)

-- Project a value from a valuation.
valprj : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> (env : Val tag Γ) -> Idx Γ τ -> Rep τ
valprj (push x env) Z = x
valprj (push x env) (S i) = valprj env i

-- Given an inclusion of Γ' in Γ, and a valuation of Γ, build a valuation of
-- Γ'. This is used for evaluation of closures in 'eval' below.
buildValFromInj : ∀ {tag} {Γ Γ' : Env tag}
               -> ({ρ : Typ tag} -> Idx Γ' ρ -> Idx Γ ρ) -> Val tag Γ -> Val tag Γ'
buildValFromInj {Γ' = []} inj env = empty
buildValFromInj {Γ' = τ ∷ Γ'} inj env =
  push (valprj env (inj Z))
       (buildValFromInj (inj ∘ S) env)

-- The semantics of the term language. Aside from returning the evaluation
-- result, this also returns an integer recording the number of evaluation
-- steps taken during evaluation. This integer is used for complexity analysis.
eval : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> Val tag Γ -> Term tag Γ τ -> Rep τ × ℤ
eval env (var i) = valprj env i , one
eval env (let' rhs e) =
  let rhs' , crhs = eval env rhs
      e' , ce = eval (push rhs' env) e
  in e' , one + crhs + ce
eval env (dual-lam Γ' inj e) =
  (\x -> eval (push x (buildValFromInj inj env)) e) , one + + (length Γ')
eval env (app e1 e2) =
  let f , cf = eval env e1
      x , cx = eval env e2
      y , cy = f x
  in y , one + cf + cx + cy
eval env (prim op e) =
  let e' , ce = eval env e
  in evalprim op e' , one + ce
eval env unit = tt , one
eval env (pair e1 e2) =
  let e1' , ce1 = eval env e1
      e2' , ce2 = eval env e2
  in (e1' , e2') , one + ce1 + ce2
eval env (fst' e) =
  let e' , ce = eval env e
  in fst e' , one + ce
eval env (snd' e) =
  let e' , ce = eval env e
  in snd e' , one + ce
eval env (inl e) =
  let e , ce = eval env e
  in inj₁ e , one + ce
eval env (inr e) =
  let e , ce = eval env e
  in inj₂ e , one + ce
eval env (case' {σ = σ} {τ = τ} {ρ = ρ} e1 e2 e3) =
  let v , cv = eval env e1
  in case v of
       [ (λ x -> let z , cz = eval (push x env) e2
                in z , one + cv + cz)
       , (λ y -> let z , cz = eval (push y env) e3
                in z , one + cv + cz)
       ]
eval env (pureevm {Γ' = Γ'} e) =
  let e' , ce = eval env e
  in LACM.pure e' , one + ce
eval env (bindevm {Γ' = Γ'} e1 e2) =
  let e1' , ce1 = eval env e1
      e2' , ce2 = eval env e2
  in LACM.bind e1' e2' , one + ce1 + ce2
eval env (runevm {Γ' = Γ'} e1 e2) =
  let mf , ce1 = eval env e1
      denv , cdenv = eval env e2
      x , envctg , capp = LACM.run mf (LEtup-to-LEτ Γ' denv)
  in (x , LEτ-to-LEtup Γ' envctg) , one + ce1 + cdenv + capp
eval env (addevm {Γ' = Γ'} idx e) =
  let e' , ce = eval env e
  in LACM.add idx e' , one + ce
eval env (scopeevm e1 e2) =
  let e1' , ce1 = eval env e1
      e2' , ce2 = eval env e2
  in LACM.scope e1' e2' , one + ce1 + ce2
eval env lunit = tt , one
eval env (lpair e1 e2) =
  let e1' , ce1 = eval env e1
      e2' , ce2 = eval env e2
  in (just (e1' , e2')) , one + ce1 + ce2
eval env (lfst' {σ = σ} e) =
  let e' , ce = eval env e
  in case e' of
       λ where nothing -> let z , cz = zerov σ
                          in z , one + ce + cz
               (just (x , y)) -> x , one + ce
eval env (lsnd' {τ = τ} e) =
  let e' , ce = eval env e
  in case e' of
       λ where nothing -> let z , cz = zerov τ
                          in z , one + ce + cz
               (just (x , y)) -> y , one + ce
eval env lpairzero = nothing , one
eval env (linl e) =
  let e' , ce = eval env e
  in just (inj₁ e') , one + ce
eval env (linr e) =
  let e' , ce = eval env e
  in just (inj₂ e') , one + ce
eval env (lcastl {σ = σ} e) =
  let e' , ce = eval env e
  in case e' of
       λ where nothing ->
                  let z , cz = zerov σ
                  in z , one + ce + cz
               (just (inj₁ x)) -> x , one + ce
               (just (inj₂ _)) ->  -- NOTE: a proper implementation would error here.
                  let z , cz = zerov σ 
                  in z , one + ce + cz
eval env (lcastr {τ = τ} e) =
  let e' , ce = eval env e
  in case e' of
       λ where nothing ->
                  let z , cz = zerov τ
                  in z , one + ce + cz
               (just (inj₁ _)) ->  -- NOTE: a proper implementation would error here.
                  let z , cz = zerov τ
                  in z , one + ce + cz
               (just (inj₂ y)) -> y , one + ce
eval env lsumzero = nothing , one
eval {Γ = Γ} env (lam t) =
  (λ x → eval (push x env) t) , one + + (length Γ)
eval env (fromDyn {Γ = G} {τ = τ} t) = 
  let (x , c1) = eval env t
      zero = (let (v , c2) = zerov τ in v , (one + (c1 + c2)))
  in case x of
      maybe′ (λ (τ2 , x2) → case (dec⇒maybe (τ LTyp≟ τ2)) of
                maybe′ (λ w → (subst LinRep (sym w) x2) , (one + c1)) 
                      -- Error, ergo we decide to return a zero value, whereas a proper implementation would error here.
                      zero)
             -- Nothing, ergo we must to return a zero value
             zero
eval env (toDyn {G} {τ} t) =
  let (x , c1) = eval env t 
  in (just (τ , x)) , (one + c1)
eval env (dynZero) = 
  nothing , one
eval env (addFromDynEvm {G} {G1} t) = 
  let (x1 , c1) = eval env t 
      zero = (LACM.pure tt) , one
  in case x1 of 
        maybe′ (λ (G2 , x2) → 
            case dec⇒maybe (LEτLtyp G1 LTyp≟ G2) of 
              maybe′ (λ w → LACM.add-LEτLtyp {G1} (subst LinRep (sym w) x2) , one) -- the cost is part of the EVM action
              -- Error, ergo we decide to add zero, whereas a proper implementation would error here.
              zero)
        -- Nothing, ergo we must to add zero
        zero
eval env (toDynEvm {Γ} {G} t) = 
  let (x , c1) = eval env t 
      (v , c2) = LEτ-to-LEτLtyp {G} x
  in just (LEτLtyp G , v) , one + c1 + c2

-- Project out the evaluation result from 'eval'.
interp : ∀ {tag} {Γ : Env tag} {τ : Typ tag} → Term tag Γ τ → Val tag Γ → Rep τ
interp e env = fst (eval env e)

-- Project out the number of evaluation steps from 'eval'.
cost : ∀ {tag} {Γ : Env tag} {τ : Typ tag} -> Val tag Γ -> Term tag Γ τ -> ℤ
cost env e = snd (eval env e)


-------------------- CHAD ------------------------------------------------------

-- A term that produces the zero value of the given type.
zerot : {Γ : Env Du} -> (τ : Typ Pr) -> Term Du Γ (D2τ τ)
zerot Un = lunit
zerot Inte = lunit
zerot R = prim LZERO lunit
zerot (σ :* τ) = lpairzero
zerot (σ :+ τ) = lsumzero
zerot (σ :-> τ) = dynZero

zerot-Lin : {Γ : Env Du} → (τ : LTyp) → Term Du Γ (Lin τ)
zerot-Lin LUn = lunit
zerot-Lin LR = prim LZERO lunit
zerot-Lin (σ :*! τ) = lpairzero
zerot-Lin (σ :+! τ) = lsumzero
zerot-Lin Dyn = dynZero

zero-LEτ : {Γ : Env Du} → (G : LEnv) → Term Du Γ (LEτ G)
zero-LEτ [] = unit
zero-LEτ (x ∷ xs) = pair (zerot-Lin x) (zero-LEτ xs)

-- In th2 we initialise the environment derivative accumulator to zero, because
-- that is how CHAD will be used in practice. This term creates a zero
-- environment derivative.
zero-env-term : {Γ' : Env Du} -> (Γ : Env Pr) -> Term Du Γ' (D2Γtup Γ)
zero-env-term [] = unit
zero-env-term (τ ∷ Γ) = pair (zerot τ) (zero-env-term Γ)

-- The CHAD code transformation.
chad : {Γ : Env Pr} {τ : Typ Pr}
    -> Term Pr Γ τ
    -> Term Du (D1Γ Γ) (D1τ τ :* (D2τ τ :-> D2Γ Γ))
chad (var idx) =
  pair (var (convIdx D1τ idx))
       (lamwith [] (addevm (convIdx D2τ' idx) (var Z)))
chad (let' {σ = σ} e1 e2) =
  let' (chad e1) $
  let' (fst' (var Z)) $
  let' (sink (WCopy (WSkip WEnd)) (chad e2)) $
    pair (fst' (var Z))
         (lamwith (zero ∷ suc (suc zero) ∷ []) $
            bindevm
              (scopeevm (zerot σ) (app (snd' (var (S Z))) (var Z)))
              (lamwith (suc (suc zero) ∷ []) $
                 app (snd' (var (S Z))) (fst' (var Z))))
chad (prim op e) =
  let' (chad e) $
    pair (prim (d1Prim op) (fst' (var Z)))
         (lamwith (zero ∷ []) $
            app (snd' (var (S Z)))
                (dprim op (fst' (var (S Z))) (var Z)))
chad unit = pair unit (lamwith [] (pureevm unit))
chad (pair e1 e2) =
  let' (pair (chad e1) (chad e2)) $
    pair (pair (fst' (fst' (var Z)))
               (fst' (snd' (var Z))))
         (lamwith (zero ∷ []) $
            thenevm (app (snd' (fst' (var (S Z)))) (lfst' (var Z)))
                    (app (snd' (snd' (var (S Z)))) (lsnd' (var Z))))
chad (fst' {τ = τ} e) =
  let' (chad e) $
    pair (fst' (fst' (var Z)))
         (lamwith (zero ∷ []) $
            app (snd' (var (S Z)))
                (lpair (var Z) (zerot τ)))
chad (snd' {σ = σ} e) =
  let' (chad e) $
    pair (snd' (fst' (var Z)))
         (lamwith (zero ∷ []) $
            app (snd' (var (S Z)))
                (lpair (zerot σ) (var Z)))
chad (inl e) =
  let' (chad e) $
    pair (inl (fst' (var Z)))
         (lamwith (zero ∷ []) $
            app (snd' (var (S Z)))
                (lcastl (var Z)))
chad (inr e) =
  let' (chad e) $
    pair (inr (fst' (var Z)))
         (lamwith (zero ∷ []) $
            app (snd' (var (S Z)))
                (lcastr (var Z)))
chad (case' {σ = σ} {τ = τ} e1 e2 e3) =
  let' (chad e1) $
    case' (fst' (var Z))
      (let' (sink (WCopy (WSkip WEnd)) (chad e2)) $
         pair (fst' (var Z))
              (lamwith (zero ∷ suc (suc zero) ∷ []) $
                 bindevm
                   (scopeevm (zerot σ) (app (snd' (var (S Z))) (var Z)))
                   (lamwith (suc (suc zero) ∷ []) $
                      app (snd' (var (S Z))) (linl (fst' (var Z))))))
      (let' (sink (WCopy (WSkip WEnd)) (chad e3)) $
         pair (fst' (var Z))
              (lamwith (zero ∷ suc (suc zero) ∷ []) $
                 bindevm
                   (scopeevm (zerot τ) (app (snd' (var (S Z))) (var Z)))
                   (lamwith (suc (suc zero) ∷ []) $
                      app (snd' (var (S Z))) (linr (fst' (var Z))))))
chad {Γ = Γ} (lam {σ = σ} {τ = τ} {Γ = G} t) = 
  pair 
    (lam (let' (chad t)
            (pair (fst' (var Z)) 
              (lam (let' (runevm (app (snd' (var (S Z))) (var Z)) (pair (zerot σ) (zero-LEτ (map D2τ' Γ)))) 
                   (lpair (fst' (snd' (var Z))) (toDynEvm (snd' (snd' (var Z)) ))))))))
    (lamwith [] (addFromDynEvm (var Z)))
chad (app {σ = σ} {τ = τ} s t) = 
  let' (chad t)
    (let' (sink1 (chad s)) 
      (let' (app (fst' (var Z)) (fst' (var (S Z)))) 
        (pair 
          (fst' (var Z))
          (lamwith (zero ∷ (suc zero) ∷ (suc ∘ suc $ zero) ∷ []) 
            (let' 
              (app (snd' (var (S Z))) (var Z)) 
            -- (d,x)₀ ∷ v₁ ∷ (b,b')₂ ∷ (f,f')₃ ∷ (a,a')₄ ∷ []
              (thenevm (app (snd' (var ( S ( S ( S ( S  Z)))))) (lfst' (var Z))) 
                       (app (snd' (var ( S ( S ( S (    Z)))))) (lsnd' (var Z)))))))))


-------------------- THE COMPLEXITY THEOREMS -----------------------------------

-- The potential function, here using c_φ = 1 because this suffices due to our
-- costing of plusv.
φ : (τ : LTyp) -> LinRep τ -> ℤ
φ LUn tt = one
φ LR _ = one
φ (σ :*! τ) nothing = one
φ (σ :*! τ) (just (x , y)) = one + φ σ x + φ τ y
φ (σ :+! τ) nothing = one
φ (σ :+! τ) (just (inj₁ x)) = one + φ σ x
φ (σ :+! τ) (just (inj₂ y)) = one + φ τ y
φ Dyn nothing = one
φ Dyn (just (τ , x)) = one + φ τ x

-- The potential function mapped over a list of linear types.
φ' : (Γ : LEnv) -> LEtup Γ -> ℤ
φ' [] tt = + 0
φ' (τ ∷ Γ) (x , env) = φ τ x + φ' Γ env


-- In th2 we bound φ by the size of the incoming cotangent. This measures the
-- size of a cotangent value.
size : (τ : LTyp) -> LinRep τ -> ℕ
size LUn .tt = 1
size LR _ = 1
size (σ :*! τ) nothing = 1
size (σ :*! τ) (just (x , y)) = 1 +ℕ size σ x +ℕ size τ y
size (σ :+! τ) nothing = 1
size (σ :+! τ) (just (inj₁ x)) = 1 +ℕ size σ x
size (σ :+! τ) (just (inj₂ y)) = 1 +ℕ size τ y
size Dyn nothing = 1
size Dyn (just (τ , x)) = 1 +ℕ size τ x

-- -------------------------
-- The implementation of decidable equality for types
-- We put this at the bottom of the file, because it is large (due to quadratic size-up) but not interesting.
-- -------------------------
:*-injective : ∀ {tag} → { σ1 σ2 τ1 τ2 : Typ tag } → (σ1 :* σ2) ≡ (τ1 :* τ2) → σ1 ≡ τ1 × σ2 ≡ τ2
:*-injective {tag} {σ1} {σ2} {τ1} {τ2} refl = refl , refl
:+-injective : ∀ {tag} → { σ1 σ2 τ1 τ2 : Typ tag } → (σ1 :+ σ2) ≡ (τ1 :+ τ2) → σ1 ≡ τ1 × σ2 ≡ τ2
:+-injective {tag} {σ1} {σ2} {τ1} {τ2} refl = refl , refl
:->-injective : ∀ {tag} → { σ1 σ2 τ1 τ2 : Typ tag } → (σ1 :-> σ2) ≡ (τ1 :-> τ2) → σ1 ≡ τ1 × σ2 ≡ τ2
:->-injective {tag} {σ1} {σ2} {τ1} {τ2} refl = refl , refl
EVM-injective : { σ τ : Typ Du } → {env1 env2 : LEnv} → EVM env1 σ ≡ EVM env2 τ → env1 ≡ env2 × σ ≡ τ
EVM-injective {σ} {τ} {evn1} {env2} refl = refl , refl
Lin-injective : { σ τ : LTyp } → Lin σ ≡ Lin τ → σ ≡ τ
Lin-injective {σ} {τ} refl = refl


Un Typ≟ Un = yes refl
Inte Typ≟ Inte = yes refl
R Typ≟ R = yes refl
(x1 :* x2) Typ≟ (y1 :* y2)
  with x1 Typ≟ y1 | x2 Typ≟ y2 
... | yes w1 | yes w2 = yes (cong₂ _:*_ w1 w2)
... | no w1  | _      = no λ x → w1 (:*-injective x .fst)
... | _      | no w2  = no λ x → w2 (:*-injective x .snd)
(x1 :+ x2) Typ≟ (y1 :+ y2)
  with x1 Typ≟ y1 | x2 Typ≟ y2 
... | yes w1 | yes w2 = yes (cong₂ _:+_ w1 w2)
... | no w1  | _      = no λ x → w1 (:+-injective x .fst)
... | _      | no w2  = no λ x → w2 (:+-injective x .snd)
(EVM x1 x2) Typ≟ (EVM y1 y2)
  with x1 LEnv≟ y1 | x2 Typ≟ y2
... | yes w1 | yes w2 = yes (cong₂ EVM w1 w2)
... | no w1  | _      = no λ x → w1 (EVM-injective x .fst)
... | _      | no w2  = no λ x → w2 (EVM-injective x .snd)
(x1 :-> x2) Typ≟ (y1 :-> y2)
  with x1 Typ≟ y1 | x2 Typ≟ y2 
... | yes w1 | yes w2 = yes (cong₂ _:->_ w1 w2)
... | no w1  | _      = no λ x → w1 (:->-injective x .fst)
... | _      | no w2  = no λ x → w2 (:->-injective x .snd)
Lin x Typ≟ Lin y
  with x LTyp≟ y
... | yes w = yes (cong Lin w)
... | no w = no λ v → w (Lin-injective v)
Un Typ≟ Inte = no λ ()
Un Typ≟ R = no λ ()
Un Typ≟ (y :* y₁) = no λ ()
Un Typ≟ (y :+ y₁) = no λ ()
Un Typ≟ (y :-> y₁) = no λ ()
Un Typ≟ EVM x y = no λ ()
Un Typ≟ Lin x = no λ ()
Inte Typ≟ Un = no λ ()
Inte Typ≟ R = no λ ()
Inte Typ≟ (y :* y₁) = no λ ()
Inte Typ≟ (y :+ y₁) = no λ ()
Inte Typ≟ (y :-> y₁) = no λ ()
Inte Typ≟ EVM x y = no λ ()
Inte Typ≟ Lin x = no λ ()
R Typ≟ Un = no λ ()
R Typ≟ Inte = no λ ()
R Typ≟ (y :* y₁) = no λ ()
R Typ≟ (y :+ y₁) = no λ ()
R Typ≟ (y :-> y₁) = no λ ()
R Typ≟ EVM x y = no λ ()
R Typ≟ Lin x = no λ ()
(x :* x₁) Typ≟ Un = no λ ()
(x :* x₁) Typ≟ Inte = no λ ()
(x :* x₁) Typ≟ R = no λ ()
(x :* x₁) Typ≟ (y :+ y₁) = no λ ()
(x :* x₁) Typ≟ (y :-> y₁) = no λ ()
(x :* x₁) Typ≟ EVM x₂ y = no λ ()
(x :* x₁) Typ≟ Lin x₂ = no λ ()
(x :+ x₁) Typ≟ Un = no λ ()
(x :+ x₁) Typ≟ Inte = no λ ()
(x :+ x₁) Typ≟ R = no λ ()
(x :+ x₁) Typ≟ (y :* y₁) = no λ ()
(x :+ x₁) Typ≟ (y :-> y₁) = no λ ()
(x :+ x₁) Typ≟ EVM x₂ y = no λ ()
(x :+ x₁) Typ≟ Lin x₂ = no λ ()
(x :-> x₁) Typ≟ Un = no λ ()
(x :-> x₁) Typ≟ Inte = no λ ()
(x :-> x₁) Typ≟ R = no λ ()
(x :-> x₁) Typ≟ (y :* y₁) = no λ ()
(x :-> x₁) Typ≟ (y :+ y₁) = no λ ()
(x :-> x₁) Typ≟ EVM x₂ y = no λ ()
(x :-> x₁) Typ≟ Lin x₂ = no λ ()
EVM x x₁ Typ≟ Un = no λ ()
EVM x x₁ Typ≟ Inte = no λ ()
EVM x x₁ Typ≟ R = no λ ()
EVM x x₁ Typ≟ (y :* y₁) = no λ ()
EVM x x₁ Typ≟ (y :+ y₁) = no λ ()
EVM x x₁ Typ≟ (y :-> y₁) = no λ ()
EVM x x₁ Typ≟ Lin x₂ = no λ ()
Lin x Typ≟ Un = no λ ()
Lin x Typ≟ Inte = no λ ()
Lin x Typ≟ R = no λ ()
Lin x Typ≟ (y :* y₁) = no λ ()
Lin x Typ≟ (y :+ y₁) = no λ ()
Lin x Typ≟ (y :-> y₁) = no λ ()
Lin x Typ≟ EVM x₁ y = no λ ()
    