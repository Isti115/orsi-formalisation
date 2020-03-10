open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding (_<_)
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All

open import Relation.Binary.PropositionalEquality as Eq hiding ([_])

module ProofTest where

open import Simple
import Statements

varTypes : Fin 1 → Types
varTypes = (λ n → Nat)

open module NatOnlySimple = Simple.Program 1 varTypes
open module NatOnlyStatements = Statements 1 varTypes

lemm3 : {X Y : Set} {f g : X → Y} {x : X} {y : Y} → f ≡ g → f x ≡ y → g x ≡ y
lemm3 refl p = p

inst : Instruction
inst = Assignment [(0F , Plus v[ 0F ] (ConstNat 1))]

asdf2 : (EQ v[ 0F ] (ConstNat 1)) ▷[
    (TRUE , SKIP)
    ,
    [
      ((LT v[ 0F ] (ConstNat 3))
      ,
      Assignment [(0F , Plus v[ 0F ] (ConstNat 1))])
    ]
  ] (EQ v[ 0F ] (ConstNat 2))

asdf2 =
  ▷-proof
    {EQ v[ 0F ] (ConstNat 1)}
    {EQ v[ 0F ] (ConstNat 2)}
    (
      (λ p⌝q r → inj₂ (cong (_+ 1) (proj₁ p⌝q)))
    ∷ [])
    {FALSE , SKIP}
