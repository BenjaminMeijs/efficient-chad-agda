module correctness.chad-numerical-precision where

open import Data.Nat
open import Agda.Builtin.Float
  using (Float; primFloatPlus; primFloatTimes; primFloatNegate; primFloatLess; primShowFloat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.List using (_∷_; map; [])
open import Data.Product using (_×_)
open import Function using (_$_)


open import spec
import spec.LACM as LACM
open import correctness.spec

relu : ∀ {Γ} → Term Pr (R ∷ Γ) R
relu = case' (prim SIGN (var Z)) 
        (case' (var Z) (prim (LIT 0.0) unit) -- negative, y = 0
                       (var (S (S Z)))) -- positive , y = x
        (prim (LIT 0.0) unit) -- Zero or NaN , y = 0

abs : ∀ {Γ} →  Term Pr (R ∷ Γ) R
abs = case' (prim SIGN (var Z))
                (case' (var Z)
                          (prim NEG (var (S (S Z)))) 
                          (var (S (S Z))))
                (prim (LIT 0.0) unit)

abs-100 : ∀ {Γ} → Term Pr (R ∷ Γ) R
abs-100 = let' (prim ADD (pair (var Z) (prim (LIT -100.0) unit))) abs 

ill-conditioned-example : Float
ill-conditioned-example =
  let f : Float → Float
      f = λ x → LACMexec (interp (chad abs-100) (push x empty) .snd 1.0 .fst) ( 0.0 , tt) .fst
      a = primShowFloat $ f 100.00000000000000 -- gives  0.0
      b = primShowFloat $ f 100.00000000000001 -- gives  1.0
      c = primShowFloat $ f  99.99999999999999 -- gives -1.0
  in {! c  !}