module Prototype.example

import Prototype.Simple as PS

%access public export
%default total

startState : PS.State
startState = \x => 0

inst1 : PS.Instruction
inst1 = PS.Assignment 3 (PS.Const 110)
-- inst1 = SKIP

inst2 : PS.Instruction
inst2 = PS.Assignment 5 (PS.Const 120)

inst3 : PS.Instruction
inst3 = PS.Assignment 3 (PS.Plus (PS.Var 5) (PS.Const 35))

inst4 : PS.Instruction
inst4 = PS.Assignment 3 (PS.Plus (PS.Var 3) (PS.Const 5))

endState : PS.State
endState = PS.executeAll startState [inst1, inst2, inst3]

cond1 : PS.Condition
cond1 state = state 3 < state 5

cond2 : PS.Condition
cond2 state = state 3 < 10

cond2' : (s : State) -> (p : cond2 s = True) -> (LT (s 3) 10)
cond2' = ?d

cond2''helper : (m, n : Nat) -> (p : (S m) < (S n) = True) -> (m < n = True)
cond2''helper Z Z p = absurd p
cond2''helper Z (S n) p = Refl
cond2''helper (S m) Z p = absurd p
cond2''helper (S m) (S n) p = ?f

cond2'' : (m, n : Nat) -> (p : m < n = True) -> (LT m n)
cond2'' Z Z p = absurd p
cond2'' Z (S n) p = LTESucc LTEZero
cond2'' (S m) Z p = absurd p
cond2'' (S m) (S n) p = LTESucc (cond2'' m n (cond2''helper m n p))

cond2''back : (m, n : Nat) -> (LT m n) -> (m < n = True)
cond2''back m (S n) (LTESucc p) = ?h
cond2''back (S m) (S n) (LTESucc p) = ?h

cond2''' : (m, n : Nat) -> (LT (S m) (S n)) -> (LT m n)
cond2''' m n (LTESucc p) = p 

cond3 : PS.Condition
cond3 state = state 3 < 20

condEndState : PS.State
condEndState = PS.conditionalExecuteAll startState [
  (const True, inst1),
  (const True, inst2),
  (cond1, inst3)
]

test0 : endState 3 = 155
test0 = Refl

test1 :
  (state : PS.State) ->
  (x : PS.Vars) ->
  (state x = 5) ->
  ((PS.execute state (PS.Assignment x (PS.Plus (PS.Var x) (PS.Const 1)))) x = 6)
test1 state x p =
  let
    eq = (decEqSelfIsYes {x})
    -- sp = sym p
    -- seq = sym eq
  in
    -- ?f
    rewrite eq in rewrite p in Refl
    -- rewrite p in rewrite eq in Refl
    -- rewrite eq in (rewrite p in Refl)
    -- ?a

helper : Dec a -> Bool
helper (Yes pro) = True
helper (No con) = False
-- helper x =
--   case x of
--     Yes pro => True
--     No con => False

-- test2 : (x : PS.Vars) -> (helper (decEq x x) = True)
-- test2 x = rewrite sym (decEqSelfIsYes {x}) in Refl
test2 : (x : PS.Vars) -> (helper (decEq x x) = True)
test2 x =
  let
    eq = (decEqSelfIsYes {x})
  in
    -- ?g
    rewrite eq in Refl
-- test2 x with (decEqSelfIsYes {x})
--   | eq = rewrite eq in Refl

test3 : (x, y, z : Bool) -> (x = y) -> (y = z) -> (x = z)
test3 x y z p q = rewrite p in rewrite q in Refl

test4 : PS.Implies (Prototype.example.cond2) (PS.wp (Prototype.example.inst4, Prototype.example.cond3))
test4 =
  PS.Impl cond2 (PS.wp (Prototype.example.inst4, Prototype.example.cond3)) prf
    where
      prf :
        (s : State) ->
        (Prototype.example.cond2 s = True) ->
        PS.wp (Prototype.example.inst4, Prototype.example.cond3) s = True
      prf s p =
        let
          h1 = plusCommutative (s 3) 5
        in
          ?c
