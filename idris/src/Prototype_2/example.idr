module Prototype_2.example

import Prototype_2.Simple as PSi
import Prototype_2.Statements as PSt

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

pred1 : PSi.Predicate
pred1 = LT (Var 3) (Const 5)

pred2 : PSi.Predicate
pred2 = LT (Var 3) (Const 10)

pred3 : PSi.Predicate
pred3 = LT (Var 3) (Const 20)

condEndState : PSi.State
condEndState = PSi.conditionalExecuteAll startState [
  (PSi.TRUE, inst1),
  (PSi.TRUE, inst2),
  (pred1, inst3)
]

cptest : PSi.ConcurrentProgram
cptest = [
  (PSi.TRUE, inst1),
  (PSi.TRUE, inst2),
  (pred1, inst3)
]

test0 : endState 3 = 155
test0 = Refl

P : (x : PSi.Vars) -> PSi.Predicate
P x = (PSi.EQ (Var x) (Const 5))

Q : (x : PSi.Vars) -> PSi.Predicate
Q x = (PSi.EQ (Var x) (Const 6))

-- Concurrent WP test

cptest2 : PSi.ConcurrentProgram
cptest2 = [
  (PSi.TRUE, PSi.Assignment 3 (PSi.Plus (PSi.Var 3) (PSi.Const 5)))
]

cptest3 : PSi.ConcurrentProgram
cptest3 = [
  (PSi.TRUE, PSi.Assignment 3 (PSi.Plus (PSi.Var 3) (PSi.Const 5))),
  (PSi.TRUE, PSi.Assignment 3 (PSi.Plus (PSi.Var 3) (PSi.Const 6)))
]

-- cwptest : PSt.Implies (Prototype_2.example.pred2) (PSi.CWP (Prototype_2.example.cptest2, Prototype_2.example.pred3))
-- cwptest =
--   PSt.Impl prf
--     where
--       prf s p =
--         let
--           q =
--             LTESucc $
--             LTESucc $
--             LTESucc $
--             LTESucc $
--             LTESucc $
--             lteSuccRight $
--             lteSuccRight $
--             lteSuccRight $
--             lteSuccRight $
--             lteSuccRight $
--             p
--         in
--           rewrite (plusCommutative (s 3) 5) in (q :: Nil)

cwptest2_lemma : (s : Nat -> Nat) -> Nat.LTE (S (plus (s 3) 5)) 10 -> Nat.LTE (S (plus (s 3) 5)) 20
cwptest2_lemma s p =
  lteSuccRight $
  lteSuccRight $
  lteSuccRight $
  lteSuccRight $
  lteSuccRight $
  lteSuccRight $
  lteSuccRight $
  lteSuccRight $
  lteSuccRight $
  lteSuccRight $
  p

cwptest2 :
  PSt.Implies
    (PSi.CWP (Prototype_2.example.cptest2, Prototype_2.example.pred2))
    (PSi.CWP (Prototype_2.example.cptest2, Prototype_2.example.pred3))
cwptest2 =
  PSt.Impl prf
    where
      prf s p = hVectApply p [cwptest2_lemma s]

cwptest3 :
  PSt.Implies
    (PSi.CWP (Prototype_2.example.cptest3, Prototype_2.example.pred2))
    (PSi.CWP (Prototype_2.example.cptest3, Prototype_2.example.pred3))
cwptest3 =
  PSt.Impl prf
    where
      prf s p = hVectApply p ?s

-- cwptest4 :
--   {ccp : PSi.ConcurrentProgram} ->
--   PSt.Implies
--     (PSi.CWP (ccp, PSi.TRUE))
--     (PSi.CWP (ccp, PSi.TRUE))
-- cwptest4 =
--   PSt.Impl prf
--     where
--       prf s p = hVectApply p ?asdf

-- test1 :
--   (state : PSi.State) ->
--   (x : PSi.Vars) ->
--   (pws (P x) state) ->
--   (pws (Q x) (PSi.execute state (PSi.Assignment x (PSi.Plus (PSi.Var x) (PSi.Const 1)))))
-- test1 state x p =
--   let
--     eq = (decEqSelfIsYes {x})
--   in
--     rewrite eq in rewrite p in Refl

-- helper : Dec a -> Bool
-- helper (Yes pro) = True
-- helper (No con) = False

-- test2 : (x : PSi.Vars) -> (helper (decEq x x) = True)
-- test2 x =
--   let
--     eq = (decEqSelfIsYes {x})
--   in
--     rewrite eq in Refl

-- test4 : PSi.Implies (Prototype_2.example.pred2) (PSi.WP (Prototype_2.example.inst4, Prototype_2.example.pred3))
-- test4 =
--   PSi.Impl pred2 (PSi.WP (inst4, pred3)) prf
--     where
--       prf :
--         (s : State) ->
--         (pws Prototype_2.example.pred2 s) ->
--         (pws (PSi.WP (Prototype_2.example.inst4, Prototype_2.example.pred3)) s)
--       prf s p =
--         let
--           q =
--             LTESucc $
--             LTESucc $
--             LTESucc $
--             LTESucc $
--             LTESucc $
--             lteSuccRight $
--             lteSuccRight $
--             lteSuccRight $
--             lteSuccRight $
--             lteSuccRight $
--             p
--         in
--           rewrite (plusCommutative (s 3) 5) in q
