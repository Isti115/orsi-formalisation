module Prototype_3.Statements

import Prototype_3.util
import Prototype_3.Simple

%access public export
%default total

Statement : Type
Statement = Type

data Implies : Condition -> Condition -> Statement where
  Impl :
    {p : Condition} ->
    {q : Condition} ->
    ((st : State) -> (p st = True) -> (q st = True)) ->
    Implies p q

--
pcwpProve' :
  (st : State) ->
  ((cwp (x, postCondition)) st = True) ->
  ((pcwp (xs, postCondition)) st = True) ->
  ((pcwp ((x::xs), postCondition)) st = True)
pcwpProve' st firstPrf restPrf = rewrite firstPrf in restPrf

pcwpProve :
  Implies preCondition (cwp (x, postCondition)) ->
  Implies preCondition (pcwp (xs, postCondition)) ->
  Implies preCondition (pcwp ((x::xs), postCondition))
pcwpProve {x} {xs} {postCondition} (Impl firstPrf) (Impl restPrf) =
  Impl prf
    where
      prf :
        (st : State) ->
        (preCondition st = True) ->
        ((pcwp (x::xs, postCondition)) st = True)
      prf st p =
        pcwpProve'
          st
          (firstPrf st p)
          (restPrf st p)

--

myNot : Condition -> Condition
myNot p = f
  where
    f : Condition
    f st = not (p st)

toMyNot : {p : Condition} -> (st : State) -> (not (p st) = True) -> ((myNot p) st = True)
toMyNot {p} st prf = rewrite prf in Refl

fromMyNot : {p, q : Condition} -> (st : State) -> ((myNot p) st = True) -> (not (p st) = True)
fromMyNot {p} st prf with (p st)
  | False = Refl
  | True = absurd prf


--

myAnd : Condition -> Condition -> Condition
myAnd p q = f
  where
    f : Condition
    f st = (p st) && (q st)

toMyAnd : {p, q : Condition} -> (st : State) -> (p st = True, q st = True) -> ((myAnd p q) st = True)
toMyAnd {p} {q} st prf = rewrite (fst prf) in rewrite (snd prf) in Refl

fromMyAnd : {p, q : Condition} -> (st : State) -> ((myAnd p q) st = True) -> (p st = True, q st = True)
fromMyAnd {p} {q} st prf with (p st)
  | False = absurd prf
  | True with (q st)
    | False = absurd prf
    | True = (Refl, Refl)

--

myOr : Condition -> Condition -> Condition
myOr p q = f
  where
    f : Condition
    f st = (p st) || (q st)

toMyOr : {p, q : Condition} -> (st : State) -> Either (p st = True) (q st = True) -> ((myOr p q) st = True)
toMyOr {p} {q} st prf with (prf)
  | Left l = rewrite l in Refl
  | Right r with (p st)
     | True = Refl
     | False = rewrite r in Refl

fromMyOr : {p, q : Condition} -> (st : State) -> ((myOr p q) st = True) -> Either (p st = True) (q st = True)
fromMyOr {p} {q} st prf with (p st)
  | True = Left Refl
  | False with (q st)
    | True = Right Refl
    | False = absurd prf

--

-- myAll : List Condition -> Condition
-- myAll ps = f
--   where
--     f : Condition
--     f st = (foldl myAnd (const True) ps) st

-- pcwpProve :
--   Implies fromCond toCond ->
--   Implies fromCond (cwp (program, toCond)) ->
--   Implies fromCond (pcwp (program, toCond))

-- toMyAll
-- fromMyAll

--

strenghtenImpliesLeft : (Implies p q) -> (r : Condition) -> (Implies (myAnd p r) q)
strenghtenImpliesLeft (Impl {p} {q} prf) r =
  Impl prf'
    where
      prf' : (st : State) -> ((myAnd p r) st = True) -> (q st = True)
      prf' state left = prf state (fst $ fromMyAnd state left)

weakenImpliesRight : (Implies p q) -> (r : Condition) -> (Implies p (myOr q r))
weakenImpliesRight (Impl {p} {q} prf) r =
  Impl prf'
    where
      prf' : (st : State) -> (p st = True) -> ((myOr q r) st = True)
      prf' state left = toMyOr state (Left (prf state left))

-- |> = unless
Unless : Condition -> (ParallelProgram, Condition) -> Statement
Unless p (s, q) = Implies (myAnd p (myNot q)) (pcwp (s, myOr p q))

sameNotTrueAndFalse : (a = True) -> (a = False) -> Void
sameNotTrueAndFalse p = rewrite p in (\q => absurd q)

lemma1 :
  {p, q, r : Condition} ->
  (st : State) ->
  ((myAnd p (myNot (myOr q r))) st = True) ->
  ((myAnd p (myNot q)) st = True)
lemma1 {p} {q} {r} st prf with (q st)
  | False =
    let
      (left, right) = fromMyAnd {q = myNot r} st prf
    in
      rewrite left in Refl
  | True = prf

lemma2_helper_helper :
  -- Foldable t =>
  (pp : List (State -> Bool)) ->
  foldl (\x1, y => x1 && Delay (y st)) False pp = False
lemma2_helper_helper {pp = []} = Refl
lemma2_helper_helper {pp = (l :: ls)} = lemma2_helper_helper ls

lemma2_helper2_h1 :
  pcwp (x :: xs, condition) st = True ->
  cwp (x, condition) st = True
lemma2_helper2_h1 {st} {x} {xs} {condition} prf with (condition (conditionalExecute st x))
  | False =
    let
      r = lemma2_helper_helper {st = st} (map (\ci => cwp (ci, condition)) xs)
    in
      void (sameNotTrueAndFalse prf r)
  | True = Refl

lemma2_helper2_h2 :
  cwp (x, myOr p q) st = True ->
  cwp (x, myOr p (myOr q r)) st = True
-- lemma2_helper2_h2 {p} {st} {x} prf = ?l2h22
lemma2_helper2_h2 {p} {st} {x} prf with (p (conditionalExecute st x))
  | False = rewrite prf in Refl
  | True = Refl

lemma2_helper2 :
  pcwp (x :: xs, myOr p q) st = True ->
  cwp (x, myOr p (myOr q r)) st = True
lemma2_helper2 prf = lemma2_helper2_h2 (lemma2_helper2_h1 prf)

lemma2_helper :
  ((pcwp ((x :: xs), condition)) st = True) ->
  ((pcwp (xs, condition)) st = True)
lemma2_helper {condition} {st} {x} {xs} prf with (condition (conditionalExecute st x))
  | False =
    let
      r = lemma2_helper_helper {st = st} (map (\ci => cwp (ci, condition)) xs)
    in
      void (sameNotTrueAndFalse prf r)
  | True = prf

lemma2 :
  (st : State) ->
  ((pcwp (s, myOr p q)) st = True) ->
  ((pcwp (s, myOr p (myOr q r))) st = True)
lemma2 st {s = []} {p = p} prf = Refl
lemma2 st {s = (x :: xs)} {p = p} {q} {r} prf =
  pcwpProve'
    {x = x}
    {xs = xs}
    {postCondition = myOr p (myOr q r)}
    st
    (lemma2_helper2 prf)
    (lemma2 st (lemma2_helper prf))

weakenUnlessRight : (Unless p (s, q)) -> (r : Condition) -> (Unless p (s, (myOr q r)))
weakenUnlessRight (Impl {p = (myAnd p (myNot q))} {q = (pcwp (s, myOr p q))} prf) r =
  Impl prf'
    where
      prf' :
        (st : State) ->
        ((myAnd p (myNot (myOr q r))) st = True) ->
        ((pcwp (s, myOr p (myOr q r))) st = True)
      prf' state left = lemma2 state $ prf state $ lemma1 state left

--

-- |-> = ensures
-- Ensures : Condition -> (ParallelProgram, Condition) -> Statement
-- Ensures p (s, q) = (Unless p (s, q), any ... s)

-- ~-> = leads to

-- test : {m : Either Int Bool} -> String
-- test {m = Left m} = "left"
-- test {m = Right m} =
--   case m of
--     True => "righttrue"
--     False => "rightfalse"
