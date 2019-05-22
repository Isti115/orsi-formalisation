module Prototype_3.example

import Prototype_3.Simple as PSi
import Prototype_3.Statements as PSt

import example3

%access public export
%default total

startState : PSi.State
startState = \x => 0

inst1 : PSi.Instruction
inst1 = PSi.Assignment 3 (PSi.Const 10)
-- inst1 = SKIP

inst2 : PSi.Instruction
inst2 = PSi.Assignment 5 (PSi.Const 120)

inst3 : PSi.Instruction
inst3 = PSi.Assignment 3 (PSi.Plus (PSi.Var 5) (PSi.Const 35))

inst4 : PSi.Instruction
inst4 = PSi.Assignment 3 (PSi.Plus (PSi.Var 3) (PSi.Const 5))

endState : PSi.State
endState = PSi.executeAll startState [inst1, inst2, inst3]

test0 : endState 3 = 155
test0 = Refl

--

cond1 : PSi.Condition
cond1 state = (PSi.evaluate state (Var 3)) < (PSi.evaluate state (Const 5))

cond2 : PSi.Condition
cond2 state = (PSi.evaluate state (Var 3)) < (PSi.evaluate state (Const 10))

cond3 : PSi.Condition
cond3 state = (PSi.evaluate state (Var 3)) < (PSi.evaluate state (Const 20))

cptest : PSi.ParallelProgram
cptest = [
  (const True, inst1),
  (const True, inst2),
  (cond1, inst3)
]

cptest2 : PSi.ParallelProgram
cptest2 = [
  (const True, PSi.Assignment 3 (PSi.Plus (PSi.Var 3) (PSi.Const 5)))
]

cptest3 : PSi.ParallelProgram
cptest3 = [
  (const True, PSi.Assignment 3 (PSi.Plus (PSi.Var 3) (PSi.Const 5))),
  (const True, PSi.Assignment 3 (PSi.Plus (PSi.Var 3) (PSi.Const 6)))
]

condEndState : PSi.State
condEndState = PSi.conditionalExecuteAll startState cptest

--

P : (x : PSi.Vars) -> PSi.Condition
P x state = (PSi.evaluate state (Var x)) == (PSi.evaluate state (Const 5))

Q : (x : PSi.Vars) -> PSi.Condition
Q x state = (PSi.evaluate state (Var x)) == (PSi.evaluate state (Const 6))

--

prf_test2' :
  (st : State) ->
  (st 3 < 10 = True) ->
  (5 + st 3 < 20 = True)
prf_test2' st p =
  trans {n = 5 + st 3} (lePlus 5 p) (the (15 < 20 = True) Refl)

prf_test2 :
  (st : State) ->
  (Prototype_3.example.cond2 st = True) ->
  (pcwp (Prototype_3.example.cptest2, Prototype_3.example.cond3) st = True)
prf_test2 st p = rewrite (plusCommutative (st 3) 5) in prf_test2' st p

pcwptest2 :
  PSt.Implies
  (Prototype_3.example.cond2)
  (PSi.pcwp (Prototype_3.example.cptest2, Prototype_3.example.cond3))
pcwptest2 =
  PSt.Impl prf_test2

--

prf3_lemm : {b1, b2 : Bool} -> (b1 = True) -> (b2 = True) -> (b1 && b2 = True)
prf3_lemm {b1 = False} {b2} p q = absurd p
prf3_lemm {b1 = True} {b2 = False} p q = absurd q
prf3_lemm {b1 = True} {b2 = True} p q = Refl

prf_test3' :
  (st : State) ->
  (st 3 < 10 = True) ->
  (((5 + st 3 < 20) && (6 + st 3 < 20)) = True)
prf_test3' st p =
  prf3_lemm
    (trans {n = 5 + st 3} (lePlus 5 p) (the (15 < 20 = True) Refl))
    (trans {n = 6 + st 3} (lePlus 6 p) (the (16 < 20 = True) Refl))

prf_test3 :
  (st : State) ->
  (Prototype_3.example.cond2 st = True) ->
  (pcwp (Prototype_3.example.cptest3, Prototype_3.example.cond3) st = True)
prf_test3 st p =
  rewrite (plusCommutative (st 3) 5) in
  rewrite (plusCommutative (st 3) 6) in
    prf_test3' st p
    --prf_test3' st p

pcwptest3 :
  PSt.Implies
  (Prototype_3.example.cond2)
  (PSi.pcwp (Prototype_3.example.cptest3, Prototype_3.example.cond3))
pcwptest3 =
  PSt.Impl prf_test3

constTrueCond : PSi.Condition
-- constTrueCond state = True
constTrueCond = const True

pcwptest4 :
  (program : PSi.ParallelProgram) ->
  PSt.Implies
    (Prototype_3.example.constTrueCond)
    (PSi.pcwp (program, Prototype_3.example.constTrueCond))
pcwptest4 [] = PSt.Impl (\state, p => Refl)
pcwptest4 ((cond, inst) :: xs) =
  pcwpProve
    {postCondition = Prototype_3.example.constTrueCond}
    {xs = xs}
    -- ?p1
    (Impl (\state, p => Refl))
    -- ?p2
    (pcwptest4 xs)

-- pcwptest4 ((cond, inst) :: xs) = PSt.Impl prf
--   where
--     prf :
--       (st : PSi.State) ->
--       (Prototype_3.example.constTrueCond st = True) ->
--       ((PSi.pcwp (((cond, inst) :: xs), Prototype_3.example.constTrueCond)) st = True)
--     prf state p = ?ct --pcwptest4 xs
