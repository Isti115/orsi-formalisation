module ORSI.Statements where

open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All
open import Data.List.Any

open import ORSI.Simple

variable
  p q r a b : Predicate
  ci : ConditionalInstruction
  cis s : ParallelProgram
  st : State

Statement : Set₁
Statement = Set

data Implies : Predicate -> Predicate -> Statement where
  Impl :
    (prf : (pprf : st ⋈ p) -> (st ⋈ q)) ->
    Implies p q

_⇒_ = Implies

strenghtenImpliesLeft : (p ⇒ q) -> (r : Predicate) -> ((AND p r) ⇒ q)
strenghtenImpliesLeft {p} {q} (Impl prf) r = Impl prf'
  where
    prf' : st ⋈ (AND p r) → st ⋈ q
    prf' (st_p , st_r) = prf st_p

weakenImpliesRight : (p ⇒ q) -> (r : Predicate) -> (p ⇒ (OR q r))
weakenImpliesRight {p} {q} (Impl prf) r = Impl prf'
  where
    prf' : st ⋈ p → st ⋈ (OR q r)
    prf' st_p = inj₁ (prf st_p)

impliesTrans : (p ⇒ q) -> (q ⇒ r) -> (p ⇒ r)
impliesTrans {p} {q} {r} (Impl p_q_prf) (Impl q_r_prf) = Impl p_r_prf
  where
    p_r_prf : st ⋈ p → st ⋈ r
    p_r_prf st_p = q_r_prf (p_q_prf st_p)

notOrToAndNotNot_prf : st ⋈ (NOT (OR p q)) → st ⋈ (AND (NOT p) (NOT q))
notOrToAndNotNot_prf {st} {p} {q} p_q_or_n = (p_n , q_n)
  where
    p_n : st ⋈ NOT p
    p_n st_p = p_q_or_n (inj₁ st_p)

    q_n : st ⋈ NOT q
    q_n st_q = p_q_or_n (inj₂ st_q)

notOrToAndNotNot_imp : (NOT (OR p q)) ⇒ (AND (NOT p) (NOT q))
notOrToAndNotNot_imp = Impl notOrToAndNotNot_prf

impliesCWP : st ⋈ CWP (ci , p) → p ⇒ q → st ⋈ CWP (ci , q)
impliesCWP {st} {ci}  p_prf (Impl prf) = {!   !}
-- impliesCWP {st} {ci}  p_prf (Impl prf) with ((ORSI.Simple.check st (proj₁ ci) (proj₂ ci))
--   | true = {!   !}
--   | false = ?

allImpliesPCWP : st ⋈ PCWP (s , p) → p ⇒ q → st ⋈ PCWP (s , q)
allImpliesPCWP [] imp = []
allImpliesPCWP (ci_prf ∷ cis_prfs) imp@(Impl prf) =
  (impliesCWP ci_prf imp ∷ allImpliesPCWP cis_prfs imp)

lessImpliesPCWP : (p ⇒ (PCWP ((ci ∷ cis) , q))) -> (p ⇒ (PCWP (cis , q)))
lessImpliesPCWP {p} {_} {cis} {q} (Impl prf) = Impl prf'
  where
    prf' : st ⋈ p → st ⋈ (PCWP (cis , q))
    prf' pprf with (prf pprf)
    ... | (ci_prf ∷ cis_prfs) = cis_prfs

--

Unless : ParallelProgram -> Predicate -> Predicate -> Statement
Unless s p q = (AND p (NOT q)) ⇒ (PCWP (s , OR p q))

_▷[_]_ : Predicate -> ParallelProgram -> Predicate -> Statement
_▷[_]_ p s q = Unless s p q

-- weakenUnlessRight : (Unless s p q) -> (r : Predicate) -> (Unless s p (OR q r))

-- weakenUnlessRight : (p ▷[ s ] q) -> (r : Predicate) -> (p ▷[ s ] (OR q r))
-- weakenUnlessRight (Impl prf) r = Impl prf'
--   where
--     prf' : (st : State) → st ⋈ AND p (NOT (OR q r)) → st ⋈ PCWP (s , OR p (OR q r))
--     prf' st st_p_q_r_or_not_and = {!   !}
--
weakenUnlessRight : (p ▷[ s ] q) -> (r : Predicate) -> (p ▷[ s ] (OR q r))
weakenUnlessRight {p} {[]} {q} (Impl prf) r = Impl (λ pprf → [])
weakenUnlessRight {p} {ci ∷ cis} {q} (Impl prf) r = Impl prf'
  where
    prf' : st ⋈ AND p (NOT (OR q r)) → st ⋈ PCWP ((ci ∷ cis) , OR p (OR q r))
    prf' {st} st_p_q_r_or_not_and with st_p_q_r_or_not_and
    ... | (st_p , st_q_or_r_n) with (prf (st_p , proj₁ (notOrToAndNotNot_prf st_q_or_r_n)))
    ...   | (ci_prf ∷ cis_prfs) =
        (inj₁ st_p ∷ allImpliesPCWP {st} {cis} {OR p q} {OR p (OR q r)} cis_prfs (Impl prf''))
          where
            prf'' : st ⋈ OR p q → st ⋈ OR p (OR q r)
            prf'' (inj₁ st_p) = inj₁ st_p
            prf'' (inj₂ st_q) = inj₂ (inj₁ st_q)
--
-- weakenUnlessRight : (p ▷[ s ] q) -> (r : Predicate) -> (p ▷[ s ] (OR q r))
-- weakenUnlessRight {p} {[]} {q} (Impl prf) r = Impl (λ st pprf → [])
-- weakenUnlessRight {p} {ci ∷ cis} {q} (Impl prf) r = Impl prf'
--   where
--     prf' : (st : State) → st ⋈ AND p (NOT (OR q r)) → st ⋈ PCWP ((ci ∷ cis) , OR p (OR q r))
--     prf' st pprf with pprf
--     ... | (st_p , st_q_or_r_n) with (prf st (st_p , st_q_n))
--       where
--         st_q_n : st ⋈ NOT q
--         st_q_n st_q = st_q_or_r_n (inj₁ st_q)
--     ...   | (ci_prf ∷ cis_prfs) =
--         (inj₁ st_p ∷ allImpliesPCWP {st} {cis} {OR p q} {OR p (OR q r)} cis_prfs (Impl prf''))
--           where
--             prf'' : (st : State) → st ⋈ OR p q → st ⋈ OR p (OR q r)
--             prf'' st (inj₁ st_p) = inj₁ st_p
--             prf'' st (inj₂ st_q) = inj₂ (inj₁ st_q)


--

Ensures : ParallelProgram -> Predicate -> Predicate -> Statement
Ensures s p q = (Unless s p q × Any (λ ci -> Implies (AND p (NOT q)) (CWP (ci , q))) s)

_↦[_]_ : Predicate -> ParallelProgram -> Predicate -> Statement
_↦[_]_ p s q = Ensures s p q

data LeadsTo : ParallelProgram -> Predicate -> Predicate -> Statement where
  FromEnsures : Ensures s p q -> LeadsTo s p q
  Transitivity : (LeadsTo s p q × LeadsTo s q r) -> LeadsTo s p r
  Disjunctivity : ((LeadsTo s p r) ⊎ (LeadsTo s q r)) -> LeadsTo s (OR p q) r

_↪[_]_ : Predicate -> ParallelProgram -> Predicate -> Statement
_↪[_]_ p s q = LeadsTo s p q
