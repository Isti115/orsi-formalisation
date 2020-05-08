open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding (_<_)
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Fin.Patterns
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.Relation.Unary.All

open import Relation.Binary.PropositionalEquality as Eq hiding ([_])

module ProofTest where

open import Base
import Statements

varTypes : Fin 1 → Types
varTypes = (λ n → Nat)

open module NatOnlyBase = Base.Environment 1 varTypes
open module NatOnlyStatements = Statements 1 varTypes

lemm3 : {X Y : Set} {f g : X → Y} {x : X} {y : Y} → f ≡ g → f x ≡ y → g x ≡ y
lemm3 refl p = p

Before : Predicate
Before = EQ v[ 0F ] (Const 1)

After : Predicate
After = EQ v[ 0F ] (Const 2)

cond : Predicate
cond = LT v[ 0F ] (Const 3)

inst : Instruction
inst = Assignment 0F (Plus v[ 0F ] (Const 1))

prf : {st : State} → (st ⊢ (Before △ ⌝ After)) → (st ⊢ cond) → (⟦ [ inst ] ⟧il st ⊢ (Before ▽ After))
prf (ownRefl p , ⌝q) r rewrite p = inj₂ (ownRefl refl)

thm : Before ▷[ [ ( cond , [ inst ] ) ] ] After
thm = ▷-proof {Before} {After} ((λ { {st} → prf {st} }) ∷ [])
