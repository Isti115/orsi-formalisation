module Prototype_4.Statements

import Prototype_4.Simple

%access public export
%default total

postulate typeDecidable : (a : Type) -> Either (Not a) a

Statement : Type
Statement = Type

data Implies : Predicate -> Predicate -> Statement where
  Impl :
    {p : Predicate} ->
    {q : Predicate} ->
    (prf : (st : State) -> (pprf : pws p st) -> (pws q st)) ->
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

-- Implies _ (PCWP ((ci :: cis), _)) ->

lessImpliesPCWP : (Implies p (PCWP ((ci :: cis), q))) -> (Implies p (PCWP (cis, q)))
lessImpliesPCWP {q} {cis} (Impl prf) = (Impl prf')
  where
    prf' : (st : State) -> (pws p st) -> (pws (PCWP (cis, q)) st)
    prf' st pprf with (prf st pprf)
      | (pr :: prs) = prs

-- |> = unless
Unless : ParallelProgram -> Predicate -> Predicate -> Statement
Unless s p q = Implies (AND p (NOT q)) (PCWP (s, OR p q))

wurLemma1 : (predicateWithState (AND p (NOT (OR q r))) st) -> (predicateWithState (AND p (NOT q)) st)
wurLemma1 prf = (fst prf, snd prf . Left)

wurLemma2 : (predicateWithState (CWP (ci, OR p q)) st) -> (predicateWithState (CWP (ci, OR p (OR q r))) st)
wurLemma2 (Left l) = Left l
wurLemma2 (Right r) = Right (Left r)

wurLemma3 : (predicateWithState (PCWP (s, OR p q)) st) -> (predicateWithState (PCWP (s, OR p (OR q r))) st)
wurLemma3 [] = []
wurLemma3 (prf :: prfs) = (wurLemma2 prf :: wurLemma3 prfs)

weakenUnlessRight : (Unless s p q) -> (r : Predicate) -> (Unless s p (OR q r))
weakenUnlessRight (Impl {p = (AND p (NOT q))} {q = (PCWP (s, OR p q))} prf) r =
  Impl prf'
    where
      prf' : (st : State) -> (pws (AND p (NOT (OR q r))) st) -> (pws (PCWP (s, OR p (OR q r))) st)
      prf' state left = wurLemma3 $ prf state $ wurLemma1 left

-- |-> = ensures
Ensures : ParallelProgram -> Predicate -> Predicate -> Statement
Ensures s p q = (Unless s p q, Any (\ci => Implies (AND p (NOT q)) (CWP (ci, q))) s)

-- ~-> = leads to
data LeadsTo : ParallelProgram -> Predicate -> Predicate -> Statement where
  FromEnsures : Ensures s p q -> LeadsTo s p q
  Transitivity : (LeadsTo s p q, LeadsTo s q r) -> LeadsTo s p r
  Disjunctivity : (Either (LeadsTo s p r) (LeadsTo s q r)) -> LeadsTo s (OR p q) r

-- init

-- FP

-- inv
inv : ParallelProgram -> Predicate -> Statement
inv s p = Implies p (PCWP (s, p))

-- TERM

--

--  :

-- pspLemma1 :
--   (prf1 : Implies (AND p (NOT q)) (PCWP (s, OR p q))) ->
--   (prf2 : Any (\ci => Implies (AND p (NOT q)) (CWP (ci, q))) s) ->
--   (ul : Implies (AND r (NOT b)) (PCWP (s, OR r b))) ->
--   (st : State) ->
--   (pprf : predicateWithState (AND (OR p r) (NOT (OR (AND q r) b))) st) ->
--   predicateWithState (PCWP (s, OR (OR p r) (OR (AND q r) b))) st
-- pspLemma1 prf1 (Here y) ul st pprf = ?prf2_rhs_1
-- pspLemma1 prf1 (There y) ul st pprf = ?prf2_rhs_2

pspLemma1 :
  (Implies (AND p (NOT q)) (PCWP (s, OR p q))) ->
  -- (Any (\ci => Implies (AND p (NOT q)) (CWP (ci, q))) s) ->
  (Implies (AND r (NOT b)) (PCWP (s, OR r b))) ->
  (pws (AND (OR p r) (NOT (OR (AND q r) b))) st) ->
  (pws (PCWP (s, OR (OR p r) (OR (AND q r) b))) st)
pspLemma1 {s = []} prf1 ul prf2 = Nil
pspLemma1
  {r} {st} {s = ci :: cis}
  (Impl prf1) (Impl ul_prf) (Left p_st, prf2_b) = (?d :: ?f)
  -- with (prf1 st (p_st, ?sajt))
  --   | (pr :: prs) = (?d :: ?f)
pspLemma1
  {p} {q} {b} {r} {st} {s = ci :: cis}
  prf1 (Impl ul_prf) (Right r_st, prf2_b) with (ul_prf st (r_st, \prf_b_st => prf2_b (Right prf_b_st)))
    | (pr :: prs) =
      let
        prf1' = lessImpliesPCWP prf1
        ul = (the (Implies (AND r (NOT b)) (PCWP ((ci :: cis), OR r b))) (Impl ul_prf))
        ul' = lessImpliesPCWP ul
        restPrf = pspLemma1 prf1' ul' (Right r_st, prf2_b)
      in
        case pr of
          Left r_st_ci => ((Left $ Right r_st_ci) :: restPrf)
          Right b_st_ci => ((Right $ Right b_st_ci) :: restPrf)
    -- where
    --   not_b_st : (pws (NOT b) st)
    --   not_b_st prf_b_st = prf3_b (Right prf_b_st)

  -- with (typeDecidable (pws r st))
  -- | Left con = (?d :: ?f) --(pspLemma1 {s = cis} prf1 prf2 prf3))
  -- | Right pro = (?d :: ?f) where
  --   valami : Nat
  --   valami = 5

    -- pspLemma1 {st} (Impl prf1) prf2 prf3 with (prf1 st)
--   | [] =?d
--   | (cip :: cips) =?f --(?d :: ?f)

PSP : (LeadsTo s p q, Unless s r b) -> LeadsTo s (OR p r) (OR (AND q r) b)
PSP ((FromEnsures (prf1, prf2)), ul) {s} = FromEnsures (Impl (\st => pspLemma1 prf1 ul), ?b_)
PSP ((Transitivity (step1, step2)), ul) = ?a_2
PSP ((Disjunctivity (Left prf)), ul) = ?a_4
PSP ((Disjunctivity (Right prf)), ul) = ?a_4


-- test : {m : Either Int Bool} -> String
-- test {m = Left m} = "left"
-- test {m = Right m} =
--   case m of
--     True => "righttrue"
--     False => "rightfalse"
