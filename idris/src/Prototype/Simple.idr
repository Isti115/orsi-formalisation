module Prototype.Simple

%access public export
%default total

Vars : Type -- actually VarSpace : Type 1
Vars = Nat

State : Type
State = (x : Vars) -> Nat

Predicate : Type
Predicate = State -> Bool

-- data Expression : (operatorSpace : OperatorSpace) -> Type

data Expression : Type where
  Const : Nat -> Expression
  Var : Vars -> Expression
  Plus : Expression -> Expression -> Expression

evaluate : State -> Expression -> Nat
evaluate state (Const v) = v
evaluate state (Var x) = state x
evaluate state (Plus e1 e2) = (evaluate state e1) + (evaluate state e2)

Condition : Type
Condition = State -> Bool
-- data Condition : Type where

data Instruction : Type where
  SKIP : Instruction
  Assignment : Vars -> Expression -> Instruction

ConditionalInstruction : Type
ConditionalInstruction = (Condition, Instruction)
-- data ConditionalInstruction : Type where
--   CondInst : Condition ->

execute : State -> Instruction -> State
execute state SKIP = state
execute state (Assignment x v) =
  f where
    f y with (decEq x y)
      | Yes pro = evaluate state v
      | No contra = state y

  -- \y -> with (decEq x y)
  --   | Yes pro = evaluate state v
  --   | No contra = state y

  -- \y => case decEq x y of
  --   Yes pro => evaluate state v
  --   No contra => state y

-- execute state (Assignment x v) = \y => if x == y then evaluate state v else state y

executeAll : State -> List Instruction -> State
executeAll state [] = state
executeAll state (i::is) = executeAll (execute state i) is

pairsum : (Int -> Bool) -> (Int, Int) -> Int
pairsum f (x, y) with (f x)
  | True = 1
  | False = 0

-- Test : Type
-- Test = (State -> Bool)

-- sajt : Condition -> State -> Test -> (Nat -> Nat)
-- sajt valami asdf with (valami asdf)
--   | True = 4
--   | False = 5
  -- | True = test -- execute state instruction
  -- | False = test

conditionalExecute : State -> ConditionalInstruction -> State
conditionalExecute state (condition, instruction) = check (condition state)
  where
    check : Bool -> State
    check True = execute state instruction
    check False = state

-- conditionalExecute state (condition, instruction) =
  -- case (condition state) of
  --   True => execute state instruction
  --   False => state

-- conditionalExecute state (condition, instruction) =
  --   if (condition state) then execute state instruction else state


conditionalExecuteAll : State -> List ConditionalInstruction -> State
conditionalExecuteAll state [] = state
conditionalExecuteAll state (ci::cis) =
  conditionalExecuteAll (conditionalExecute state ci) cis

--

wp : (Instruction, Condition) -> Condition
wp (instruction, condition) =
  \state => condition (execute state instruction)

-- infix 0 #=>#

data Implies : Condition -> Condition -> Type where
  Impl :
    (a : Condition) ->
    (b : Condition) ->
    (c : ((s : State) -> (p : a s = True) -> b s = True)) ->
    Implies a b
