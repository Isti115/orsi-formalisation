module Prototype_2.Statements

import Prototype_2.util
import Prototype_2.Simple

%access public export
%default total

Statement : Type
Statement = Type

data Implies : Predicate -> Predicate -> Statement where
  Impl :
    {p : Predicate} ->
    {q : Predicate} ->
    ((st : State) -> (pws p st) -> (pws q st)) ->
    Implies p q

strenghtenImpliesLeft : (Implies p q) -> (r : Predicate) -> (Implies (AND p r) q)
strenghtenImpliesLeft (Impl {p} prf) r =
  Impl prf'
    where
      prf' : (st : State) -> (pws (AND p r) st) -> (pws q st)
      prf' state left = prf state (fst left)

weakenImpliesRight : (Implies p q) -> (r : Predicate) -> (Implies p (OR q r))
weakenImpliesRight (Impl {q} prf) r =
  Impl prf'
    where
      prf' : (st : State) -> (pws p st) -> (pws (OR q r) st)
      prf' state left = Left $ prf state left

-- |> = unless
Unless : Predicate -> (ConcurrentProgram, Predicate) -> Statement
Unless p (s, q) = Implies (AND p (NOT q)) (CWP (s, OR p q))

lemma1 : (predicateWithState (AND p (NOT (OR q r))) st) -> (predicateWithState (AND p (NOT q)) st)
lemma1 prf = (fst prf, snd prf . Left)

lemma2 : (predicateWithState (CWP (s, OR p q)) st) -> (predicateWithState (CWP (s, OR p (OR q r))) st)
lemma2 prf = ?a

weakenUnlessRight : (Unless p (s, q)) -> (r : Predicate) -> (Unless p (s, (OR q r)))
weakenUnlessRight (Impl {p = (AND p (NOT q))} {q = (CWP (s, OR p q))} prf) r =
  Impl prf'
    where
      prf' : (st : State) -> (pws (AND p (NOT (OR q r))) st) -> (pws (CWP (s, OR p (OR q r))) st)
      prf' state left = lemma2 $ prf state $ lemma1 left

-- test : foldr Pair () (map (predicateWithState (OR p (OR q r))) (map (conditionalExecute st) s))

-- test : predicateWithState (CWP (ss, TRUE)) st
-- test {ss} = ?a -- tuplify (map (const ()) ss)

-- weakenUnlessRight

-- |-> = ensures
-- ~-> = leads to

-- test : {m : Either Int Bool} -> String
-- test {m = Left m} = "left"
-- test {m = Right m} =
--   case m of
--     True => "righttrue"
--     False => "rightfalse"
