module ORSI.Simple where

-- Imports

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as Eq
open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Function
-- open import Data.String

-- Vars, Values, State, emptyState

Vars : Set
Vars = ℕ

Values : Set
Values = ℕ

State : Set
State = Vars → Values

emptyState : State
emptyState = λ x → 0

-- Expression, evaluate

data Expression : Set where
  Const : ℕ -> Expression
  Var : Vars -> Expression
  Plus : Expression -> Expression -> Expression

⟦_⟧e : Expression -> State → ℕ
⟦ Const v ⟧e st = v
⟦ Var x ⟧e st = st x
⟦ Plus e1 e2 ⟧e st = ⟦ e1 ⟧e st + ⟦ e2 ⟧e st

-- Instruction, execute

data Instruction : Set where
  SKIP : Instruction
  Assignment : Vars → Expression → Instruction

⟦_⟧i : Instruction → State → State
⟦ SKIP ⟧i st = st
⟦ Assignment var value ⟧i st x = if ⌊ x Data.Nat.≟ var ⌋ then ⟦ value ⟧e st else st x

data Predicate : Set where
  TRUE : Predicate
  FALSE : Predicate
  NOT : Predicate -> Predicate
  AND : Predicate -> Predicate -> Predicate
  OR : Predicate -> Predicate -> Predicate

ConditionalInstruction : Set
ConditionalInstruction = (Predicate × Instruction)

ParallelProgram : Set
ParallelProgram = List ConditionalInstruction

-- predicateWithState

⟦_⟧ : Predicate -> State -> Set
_⋈_ : State -> Predicate -> Set

s ⋈ p = ⟦ p ⟧ s

⟦ TRUE ⟧ state = ⊤
⟦ FALSE ⟧ state = ⊥
⟦ NOT p ⟧ state = ¬(state ⋈ p)
⟦ AND p₁ p₂ ⟧ state = ((state ⋈ p₁) × (state ⋈ p₂))
⟦ OR  p₁ p₂ ⟧ state = ((state ⋈ p₁) ⊎ (state ⋈ p₂))

Condition : Set
Condition = State → Bool

⟦_⟧b : Predicate → Condition
⟦ TRUE ⟧b = const true
⟦ FALSE ⟧b = const false
⟦ NOT p ⟧b state = not (⟦ p ⟧b state)
⟦ AND p₁ p₂ ⟧b state = (⟦ p₁ ⟧b state) ∧ (⟦ p₂ ⟧b state)
⟦ OR p₁ p₂ ⟧b state = (⟦ p₁ ⟧b state) ∨ (⟦ p₂ ⟧b state)
{-
fromBool : Bool → Set
fromBool false = ⊥
fromBool true = ⊤

⟦_⟧ : Predicate → State → Set
⟦ p ⟧ st = fromBool (⟦ p ⟧b st)

fromBoolnot : (b : Bool) → fromBool (not b) ↔ fromBool b → ⊥
fromBoolnot false = {!!}
fromBoolnot true = {!!}

f : (p : Predicate)(s : State) → fromBool (⟦ p ⟧b s) ≡ ⟦ p ⟧ s
f TRUE st = refl
f FALSE st = refl
f (NOT p) st rewrite f p st = {!!}
f (AND p p₁) st = {!!}
f (OR p p₁) st = {!!}
-}

⟦_⟧ci : ConditionalInstruction → State → State
⟦ (p , i) ⟧ci st  with ⟦ p ⟧b st
⟦ (p , i) ⟧ci st | false = st
⟦ (p , i) ⟧ci st | true = ⟦ i ⟧i st

-- test:

testInstruction : ConditionalInstruction
testInstruction = (TRUE , SKIP)

testPrf : (⟦ Assignment 1 (Const 5) ⟧i emptyState) 1 ≡ 5
testPrf = refl
