module Prototype_4.Statements

import Prototype_4.Util
import Prototype_4.Simple

%access public export
%default total

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

wurLemma1 : (pws (AND p (NOT (OR q r))) st) -> (pws (AND p (NOT q)) st)
wurLemma1 prf = (fst prf, snd prf . Left)

wurLemma2 : (pws (CWP (ci, OR p q)) st) -> (pws (CWP (ci, OR p (OR q r))) st)
wurLemma2 (Left l) = Left l
wurLemma2 (Right r) = Right (Left r)

wurLemma3 : (pws (PCWP (s, OR p q)) st) -> (pws (PCWP (s, OR p (OR q r))) st)
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

pspLemma1 :
  (Implies (AND p (NOT q)) (PCWP (s, OR p q))) ->
  -- (Any (\ci => Implies (AND p (NOT q)) (CWP (ci, q))) s) ->
  (Implies (AND r (NOT b)) (PCWP (s, OR r b))) ->
  (pws (AND (AND p r) (NOT (OR (AND q r) b))) st) ->
  (pws (PCWP (s, OR (AND p r) (OR (AND q r) b))) st)
pspLemma1 {s = []} prf1 ul prf2 = Nil
pspLemma1
  {q} {r} {st} {s = ci :: cis}
  (Impl prf1) (Impl ul_prf) ((p_st, r_st), prf2_b) with (ul_prf st (r_st, \prf_b_st => prf2_b (Right prf_b_st)))
    | ((Left r_st_ci) :: prs) with (typeDecidable (pws q st))
      | (Left not_q_st) with (prf1 st (p_st, not_q_st))
        | ((Left p_st_ci) :: prs2) =
          (
            Left (p_st_ci, r_st_ci) ::
            pspLemma1 (lessImpliesPCWP (Impl prf1)) (lessImpliesPCWP (Impl ul_prf)) ((p_st, r_st), prf2_b)
          )
        | ((Right q_st_ci) :: prs2) =
          (
            Right (Left (q_st_ci, r_st_ci)) ::
            pspLemma1 (lessImpliesPCWP (Impl prf1)) (lessImpliesPCWP (Impl ul_prf)) ((p_st, r_st), prf2_b)
          )
      | (Right q_st) =
        (
          (void (prf2_b (Left (q_st, r_st)))) ::
          pspLemma1 (lessImpliesPCWP (Impl prf1)) (lessImpliesPCWP (Impl ul_prf)) ((p_st, r_st), prf2_b)
        )
    | ((Right b_st_ci) :: prs) =
      (
        Right (Right b_st_ci) ::
        pspLemma1 (lessImpliesPCWP (Impl prf1)) (lessImpliesPCWP (Impl ul_prf)) ((p_st, r_st), prf2_b)
      )

pspLemma2 :
  (ul : Implies (AND r (NOT b)) (PCWP (s, OR r b))) ->
  (prf1 : Implies (AND p (NOT q)) (PCWP (s, OR p q))) ->
  (prf2 : Any (\ci => Implies (AND p (NOT q)) (CWP (ci, q))) s) ->
    -- (pprf : pws (AND (AND p r) (NOT (OR (AND q r) b))) st) ->
  Any (\ci => Implies (AND (AND p r) (NOT (OR (AND q r) b))) (CWP (ci, OR (AND q r) b))) s
-- pspLemma2 {s = []} ul prf1 prf2 impossible
pspLemma2
  {s = ci :: cis} {p} {q} {r} {b}
  (Impl ul_prf) (Impl prf1_prf) (Here (Impl prf2_here)) =
  Here (Impl lemma_prf)
    where
      lemma_prf :
        (st : State) ->
        (pws (AND (AND p r) (NOT (OR (AND q r) b))) st) ->
        (pws (CWP (ci, OR (AND q r) b)) st)
      lemma_prf st ((p_st, r_st), pprf_2) with (ul_prf st (r_st, \b_prf => pprf_2 (Right b_prf)))
        | (Left r_st_ci :: _) with (typeDecidable (pws q st))
          | (Left not_q_st) =
              let
                q_st_ci = prf2_here st (p_st, not_q_st)
              in
                Left (q_st_ci, r_st_ci)
          | (Right q_st) = void (pprf_2 (Left (q_st, r_st)))
      | ((Right b_st_ci) :: prs) =
        (
          Right (Right b_st_ci) ::
          pspLemma1 (lessImpliesPCWP (Impl prf1)) (lessImpliesPCWP (Impl ul_prf)) ((p_st, r_st), prf2_b)
        )
        | (Right b_st_ci :: _) = Right b_st_ci
        -- let
          -- n_b_prf : Not (pws b st)
          -- n_b_prf b_prf = pprf_2 (Right b_prf)
        -- in
        --   ?asdf

pspLemma2 {s = ci :: cis} ul_prf prf1_prf (There prf2_there) =
  There (pspLemma2 (lessImpliesPCWP ul_prf) (lessImpliesPCWP prf1_prf) prf2_there)

PSP : (LeadsTo s p q, Unless s r b) -> LeadsTo s (AND p r) (OR (AND q r) b)
PSP ((FromEnsures (prf1, prf2)), ul) {s} = FromEnsures (Impl (\st => pspLemma1 prf1 ul), (pspLemma2 ul prf1 prf2))
PSP ((Transitivity (step1, step2)), ul) = ?a_2
PSP ((Disjunctivity (Left prf)), ul) = ?a_4
PSP ((Disjunctivity (Right prf)), ul) = ?a_4


-- test : {m : Either Int Bool} -> String
-- test {m = Left m} = "left"
-- test {m = Right m} =
--   case m of
--     True => "righttrue"
--     False => "rightfalse"
