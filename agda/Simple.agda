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

evaluate : State -> Expression -> ℕ
evaluate state (Const v) = v
evaluate state (Var x) = state x
evaluate state (Plus e1 e2) = (evaluate state e1) + (evaluate state e2)

-- Instruction, execute

data Instruction : Set where
  SKIP : Instruction
  Assignment : Vars → Expression → Instruction

execute : State → Instruction → State
execute state SKIP = state
-- execute state (Assignment var value) x with (x Data.Nat.≟ var)
-- ... | (yes _) = (evaluate state value)
-- ... | (no _) = state x
execute state (Assignment var value) =
  λ x → if ⌊ x Data.Nat.≟ var ⌋ then (evaluate state value) else state x
-- -- execute state (Assignment var value) = λ x → state x

--

ConditionalInstruction : Set
conditionalExecute : State -> ConditionalInstruction -> State

ParallelProgram : Set
ParallelProgram = List ConditionalInstruction

data Predicate : Set where
  TRUE : Predicate
  FALSE : Predicate
  --
  WP : (Instruction × Predicate) -> Predicate
  CWP : (ConditionalInstruction × Predicate) -> Predicate
  PCWP : (ParallelProgram × Predicate) -> Predicate
  --
  NOT : Predicate -> Predicate
  AND : Predicate -> Predicate -> Predicate
  OR : Predicate -> Predicate -> Predicate

-- syntax
-- _∧_ = AND

-- predicateWithState

predicateWithState : Predicate -> State -> Set

-- pws = predicateWithState

_⋈_ : State -> Predicate -> Set
_⋈_ s p = predicateWithState p s

predicateWithState TRUE state = ⊤
predicateWithState FALSE state = ⊥
--
predicateWithState (WP (instruction , predicate)) state =
  (execute state instruction) ⋈ predicate
  -- predicateWithState predicate (execute state instruction)
predicateWithState (CWP (conditionalInstruction , predicate)) state =
  (conditionalExecute state conditionalInstruction) ⋈ predicate
  -- predicateWithState predicate (conditionalExecute state conditionalInstruction)
predicateWithState (PCWP (parallelProgram , predicate)) state =
  All (λ ci -> state ⋈ (CWP (ci , predicate))) parallelProgram
--
predicateWithState (NOT p) state = ¬(state ⋈ p)
predicateWithState (AND p₁ p₂) state = ((state ⋈ p₁) × (state ⋈ p₂))
predicateWithState (OR p₁ p₂) state = ((state ⋈ p₁) ⊎ (state ⋈ p₂))
-- predicateWithState (NOT p) state = ¬(predicateWithState p state)
-- predicateWithState (AND p₁ p₂) state = ((predicateWithState p₁ state) × (predicateWithState p₂ state))
-- predicateWithState (OR p₁ p₂) state = ((predicateWithState p₁ state) ⊎ (predicateWithState p₂ state))

--

Condition : Set
Condition = State → Bool

predicateToCondition : Predicate → Condition
predicateToCondition TRUE = const true
predicateToCondition FALSE = const false
--
predicateToCondition (WP (instruction , predicate)) state =
  (predicateToCondition predicate) (execute state instruction)
predicateToCondition (CWP (conditionalInstruction , predicate)) state =
  (predicateToCondition predicate) (conditionalExecute state conditionalInstruction)
predicateToCondition (PCWP (parallelProgram , predicate)) state =
  Data.List.all (λ ci → predicateToCondition (CWP (ci , predicate)) state) parallelProgram
--
predicateToCondition (NOT p) =
  λ state → not (predicateToCondition p state)
predicateToCondition (AND p₁ p₂) =
  λ state → (predicateToCondition p₁ state) ∧ (predicateToCondition p₂ state)
predicateToCondition (OR p₁ p₂) =
  λ state → (predicateToCondition p₁ state) ∨ (predicateToCondition p₂ state)

ConditionalInstruction = (Predicate × Instruction)

{-# TERMINATING #-}
conditionalExecute state (predicate , instruction) = check (condition state)
  where
    check : Bool -> State
    check true = execute state instruction
    check false = state

    condition =  predicateToCondition predicate

-- test:

-- testInstruction : ConditionalInstruction
-- testInstruction = (TRUE , SKIP)
--
-- testPrf : (execute emptyState (Assignment 1 (Const 5))) 1 ≡ 5
-- testPrf = refl
