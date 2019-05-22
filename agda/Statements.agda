
module ORSI.Statements where

open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Relation.Binary.PropositionalEquality as Eq

open import ORSI.Simple

variable
  a b : Bool
  p q r : Predicate
  i : Instruction
  ci : ConditionalInstruction
  cis s : ParallelProgram
  st : State

Statement : Set₁
Statement = Set

_⇒_ : Predicate → Predicate → Statement
p ⇒ q = ∀{st} → ⟦ p ⟧b st ≡ true → ⟦ q ⟧b st ≡ true

∧-elim₁ : a ∧ b ≡ true → a ≡ true
∧-elim₁ {true} {true} p = refl

∨-intr₁ : a ≡ true → a ∨ b ≡ true
∨-intr₁ {true} p = p

strenghtenImpliesLeft : (p ⇒ q) → (AND p r ⇒ q)
strenghtenImpliesLeft p⇒q p∧r = p⇒q (∧-elim₁ p∧r)

weakenImpliesRight : (p ⇒ q) → (p ⇒ (OR q r))
weakenImpliesRight p⇒q p = ∨-intr₁ (p⇒q p)

impliesTrans : (p ⇒ q) -> (q ⇒ r) -> (p ⇒ r)
impliesTrans p⇒q q⇒r p = q⇒r (p⇒q p)

notOrToAndNotNot_prf : ⟦ NOT (OR p q) ⟧b st ≡ true → ⟦ AND (NOT p) (NOT q) ⟧b st ≡ true
notOrToAndNotNot_prf {p}{q}{st} with ⟦ p ⟧b st | ⟦ q ⟧b st
notOrToAndNotNot_prf {p}{q}{st} | false | false = λ x → x
notOrToAndNotNot_prf {p}{q}{st} | false | true  = λ ()
notOrToAndNotNot_prf {p}{q}{st} | true  | false = λ ()
notOrToAndNotNot_prf {p}{q}{st} | true  | true  = λ ()

notOrToAndNotNot_imp : (NOT (OR p q)) ⇒ (AND (NOT p) (NOT q))
notOrToAndNotNot_imp {p}{q} = notOrToAndNotNot_prf {p}{q}

WP : Instruction → Predicate → Condition
WP i p st = ⟦ p ⟧b (⟦ i ⟧i st)

CWP : ConditionalInstruction → Predicate → Condition
CWP ci p st = ⟦ p ⟧b (⟦ ci ⟧ci st)

impliesCWP : CWP ci p st ≡ true → p ⇒ q → CWP ci q st ≡ true
impliesCWP {r , i}{p}{st} cwp p⇒q with ⟦ r ⟧b st
impliesCWP {r , i} {p} {st} cwp p⇒q | false = p⇒q cwp
impliesCWP {r , i} {p} {st} cwp p⇒q | true = p⇒q cwp
{-

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
-}
