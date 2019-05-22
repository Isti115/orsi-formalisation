module Prototype_2.Simple

import public Prototype_2.util

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
mutual

  ConditionalInstruction : Type
  ConditionalInstruction = (Predicate, Instruction)

  ConcurrentProgram : Type
  ConcurrentProgram = List ConditionalInstruction

  data Predicate : Type where
    TRUE : Predicate
    FALSE : Predicate
    --
    LTE : Expression -> Expression -> Predicate
    GTE : Expression -> Expression -> Predicate
    LT : Expression -> Expression -> Predicate
    GT : Expression -> Expression -> Predicate
    --
    EQ : Expression -> Expression -> Predicate
    --
    WP : (Instruction, Predicate) -> Predicate
    CWP : (ConcurrentProgram, Predicate) -> Predicate
    --
    NOT : Predicate -> Predicate
    AND : Predicate -> Predicate -> Predicate
    OR : Predicate -> Predicate -> Predicate

  syntax pws [p] [s] = predicateWithState p s

  predicateWithState : Predicate -> State -> Type
  predicateWithState TRUE state = Unit
  predicateWithState FALSE state = Void
  --
  predicateWithState (LTE e1 e2) state = Nat.LTE (evaluate state e1) (evaluate state e2)
  predicateWithState (GTE e1 e2) state = Nat.GTE (evaluate state e1) (evaluate state e2)
  predicateWithState (LT e1 e2) state = Nat.LT (evaluate state e1) (evaluate state e2)
  predicateWithState (GT e1 e2) state = Nat.GT (evaluate state e1) (evaluate state e2)
  --
  predicateWithState (EQ e1 e2) state = (=) (evaluate state e1) (evaluate state e2)
  --
  predicateWithState (WP (instruction, predicate)) state =
    pws predicate (execute state instruction)
  predicateWithState (CWP (concurrentProgram, predicate)) state =
    HVect $ fromList $ map (predicateWithState predicate) (map (conditionalExecute state) concurrentProgram)
    -- typeTuplify $ map (predicateWithState predicate) (map (conditionalExecute state) concurrentProgram)
    -- typeTuplify $ map (predicateWithState predicate) (the (List State) (map (conditionalExecute state) concurrentProgram))
  --
  predicateWithState (NOT p) state = Not (predicateWithState p state)
  predicateWithState (AND p1 p2) state = (predicateWithState p1 state, predicateWithState p2 state)
  predicateWithState (OR p1 p2) state = Either (predicateWithState p1 state) (predicateWithState p2 state)

  Condition : Type
  Condition = State -> Bool

  syntax ptc [p] = predicateToCondition p

  predicateToCondition : Predicate -> Condition
  predicateToCondition TRUE state = True
  predicateToCondition FALSE state = False
  --
  predicateToCondition (LTE e1 e2) state = Nat.lte (evaluate state e1) (evaluate state e2)
  predicateToCondition (GTE e1 e2) state = Nat.gte (evaluate state e1) (evaluate state e2)
  predicateToCondition (LT e1 e2) state = Nat.lt (evaluate state e1) (evaluate state e2)
  predicateToCondition (GT e1 e2) state = Nat.gt (evaluate state e1) (evaluate state e2)
  --
  predicateToCondition (EQ e1 e2) state = (==) (evaluate state e1) (evaluate state e2)
  --
  predicateToCondition (WP (instruction, predicate)) state =
    predicateToCondition predicate (execute state instruction)
  predicateToCondition (CWP (concurrentProgram, predicate)) state =
    all (predicateToCondition predicate) (map (conditionalExecute state) concurrentProgram)
    -- (the (List State) (map (conditionalExecute state) concurrentProgram))
  --
  predicateToCondition (NOT p) state = not (predicateToCondition p state)
  predicateToCondition (AND p1 p2) state = predicateToCondition p1 state && predicateToCondition p2 state
  predicateToCondition (OR p1 p2) state = predicateToCondition p1 state || predicateToCondition p2 state

  --

  conditionalExecute : State -> ConditionalInstruction -> State
  conditionalExecute state (predicate, instruction) = check (condition state)
    where
      check : Bool -> State
      check True = execute state instruction
      check False = state

      -- condition = predicateToCondition predicate
      condition = assert_total predicateToCondition predicate

  conditionalExecuteAll : State -> ConcurrentProgram -> State
  conditionalExecuteAll state [] = state
  conditionalExecuteAll state (ci::cis) =
    conditionalExecuteAll (conditionalExecute state ci) cis
