module Prototype_3.Simple

import public Prototype_3.util

%access public export
%default total

Vars : Type
Vars = Nat

State : Type
State = (x : Vars) -> Nat

emptyState : State
emptyState x = 0

--

data Expression : Type where
  Const : Nat -> Expression
  Var : Vars -> Expression
  Plus : Expression -> Expression -> Expression

evaluate : State -> Expression -> Nat
evaluate state (Const v) = v
evaluate state (Var x) = state x
evaluate state (Plus e1 e2) = (evaluate state e1) + (evaluate state e2)

--

data Instruction : Type where
  SKIP : Instruction
  Assignment : Vars -> Expression -> Instruction

SequentialProgram : Type
SequentialProgram = List Instruction

execute : State -> Instruction -> State
execute state SKIP = state
execute state (Assignment x v) =
  f where
    f y with (decEq x y)
      | Yes pro = evaluate state v
      | No contra = state y

executeAll : State -> SequentialProgram -> State
executeAll state [] = state
executeAll state (i::is) = executeAll (execute state i) is

--

Condition : Type
Condition = State -> Bool

ConditionalInstruction : Type
ConditionalInstruction = (Condition, Instruction)

ParallelProgram : Type
ParallelProgram = List ConditionalInstruction

-- data Predicate : Type where
--   TRUE : Predicate
--   FALSE : Predicate
--   --
--   LTE : Expression -> Expression -> Predicate
--   GTE : Expression -> Expression -> Predicate
--   LT : Expression -> Expression -> Predicate
--   GT : Expression -> Expression -> Predicate
--   --
--   EQ : Expression -> Expression -> Predicate
--   --
--   WP : (Instruction, Predicate) -> Predicate
--   CWP : (ParallelProgram, Predicate) -> Predicate
--   --
--   NOT : Predicate -> Predicate
--   AND : Predicate -> Predicate -> Predicate
--   OR : Predicate -> Predicate -> Predicate
--

conditionalExecute : State -> ConditionalInstruction -> State
conditionalExecute state (condition, instruction) = check (condition state)
  where
    check : Bool -> State
    check True = execute state instruction
    check False = state

conditionalExecuteAll : State -> ParallelProgram -> State
conditionalExecuteAll state [] = state
conditionalExecuteAll state (ci::cis) =
  conditionalExecuteAll (conditionalExecute state ci) cis

-- Weakest Precondition
wp : (Instruction, Condition) -> Condition
wp (instruction, condition) state =
  condition (execute state instruction)

-- Conditional Weakest Precondition
cwp : (ConditionalInstruction, Condition) -> Condition
cwp (conditionalInstruction, condition) state =
  condition (conditionalExecute state conditionalInstruction)

-- Parallel Conditional Weakest Precondition
pcwp : (ParallelProgram, Condition) -> Condition
pcwp (parallelProgram, condition) state =
  -- all condition (map (conditionalExecute state) parallelProgram)
  all (\c => c state) (map (\ci => cwp (ci, condition)) parallelProgram)

-- cwp : (ParallelProgram, Condition) -> Condition
-- cwp (parallelProgram, condition) state =
--   and (map ((Lazy . condition) . (conditionalExecute state)) parallelProgram)
