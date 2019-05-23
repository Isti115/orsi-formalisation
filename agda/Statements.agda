
module Statements where

open import Data.Unit
open import Data.Bool
open import Data.Bool.Properties
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Relation.Binary.PropositionalEquality as Eq
open import Function

open import Simple

variable
  a b : Bool
  P Q R : Predicate
  c d e : Condition
  i : Instruction
  ci : ConditionalInstruction
  cis S : ParallelProgram
  st : State

Statement : Set₁
Statement = Set

_⇒_ : Predicate → Predicate → Statement
P ⇒ Q = ∀{st} → st ⋈p P → st ⋈p Q
--
-- _⇛_ : Condition → Condition → Statement
-- c ⇛ d = ∀{st} → T (st ⊨ c) → T (st ⊨ d)

-- -- ∧-elim
--
-- ∧-elim : T (a ∧ b) → (T a × T b)
-- ∧-elim {true} {true} Ta∧b = (tt , tt)
--
-- ∧-elim₁ : T (a ∧ b) → T a
-- ∧-elim₁ = proj₁ ∘ ∧-elim
--
-- ∧-elim₂ : T (a ∧ b) → T b
-- ∧-elim₂ = proj₂ ∘ ∧-elim
--
-- -- ∨-intr
--
-- ∨-intr : (T a ⊎ T b) → T (a ∨ b)
-- ∨-intr {true} {b} (inj₁ Ta) = tt
-- ∨-intr {a} {true} (inj₂ Tb) rewrite ∨-comm a true = tt
--
-- -- ∨-intr {false} {true} (inj₂ Tb) = refl
-- -- ∨-intr {true} {true} (inj₂ Tb) = refl
--
-- ∨-intr₁ : T a → T (a ∨ b)
-- ∨-intr₁ = ∨-intr ∘ inj₁
--
-- ∨-intr₂ : T b → T (a ∨ b)
-- ∨-intr₂ = ∨-intr ∘ inj₂
--
-- --
--
impliesTrans : (P ⇒ Q) → (Q ⇒ R) → (P ⇒ R)
impliesTrans p⇒q q⇒r p = q⇒r (p⇒q p)

strenghtenImpliesLeft : (P ⇒ Q) → (AND P R ⇒ Q)
strenghtenImpliesLeft p⇒q p∧r = p⇒q (proj₁ p∧r)

weakenImpliesRight : (P ⇒ Q) → (P ⇒ OR Q R)
weakenImpliesRight p⇒q p = inj₁ (p⇒q p)
--
-- -- De Morgan
--
-- notOrToAndNotNot : NOT (OR p q) ⇒ AND (NOT p) (NOT q)
-- notOrToAndNotNot {p} {q} {st} ¬_p∨q_ with st ⊢ p | st ⊢ q
-- ... | false | false = tt
--
-- notAndToOrNotNot : NOT (AND p q) ⇒ OR (NOT p) (NOT q)
-- notAndToOrNotNot {p} {q} {st} ¬_p∧q_ with st ⊢ p | st ⊢ q
-- ... | false | _ = tt
-- ... | st⊢p | false rewrite ∨-comm (not st⊢p) (not false) = tt

notOrToAndNotNot : NOT (OR P Q) ⇒ AND (NOT P) (NOT Q)
notOrToAndNotNot ¬_p∨q_ = ((λ p → ¬_p∨q_ (inj₁ p)) , (λ q → ¬_p∨q_ (inj₂ q)))

notAndToOrNotNot : NOT (AND P Q) ⇒ OR (NOT P) (NOT Q)
notAndToOrNotNot ¬_p∧q_ = {!  !}
--
WP : (Instruction × Predicate) → Assertion
WP (i , p) = λ st → (⟦ i ⟧i st) ⋈p p

CWP : (ConditionalInstruction × Predicate) → Assertion
CWP (ci , p) = λ st → (⟦ ci ⟧ci st) ⋈p p

PCWP : (ParallelProgram × Predicate) → Assertion
PCWP (s , p) = λ st → All (λ ci → st ⋈a (CWP (ci , p))) s
--
-- -- impliesCWP : T ((CWP (ci , p)) st) → p ⇒ q → T ((CWP (ci , q)) st)
-- -- impliesCWP p⇒q cwp = p⇒q cwp
-- -- impliesCWP = _|>_
-- -- impliesCWP {ci = (r , i)} {p} {st} cwp p⇒q with st ⊢ r
-- -- ... | false = p⇒q cwp
-- -- ... | true = p⇒q cwp
--
-- impliesCWP : p ⇒ q → (CWP (ci , p)) ⇛ (CWP (ci , q))
-- impliesCWP p⇒q cwp = p⇒q cwp
--
-- lessPCWP : PCWP ((ci ∷ cis) , p) ⇛ PCWP (cis , p)
-- lessPCWP {ci} {p = p} {st = st} pcwp with (st ⊨ CWP (ci , p))
-- ... | true = pcwp
--
-- data Singleton {a} {A : Set a} (x : A) : Set a where
--   _with≡_ : (y : A) → x ≡ y → Singleton x
--
-- inspect' : ∀ {a} {A : Set a} (x : A) → Singleton x
-- inspect' x = x with≡ refl
--
-- allImpliesPCWP : ∀{p}{q}{s} → p ⇒ q → PCWP (s , p) ⇛ PCWP (s , q)
-- allImpliesPCWP {s = []} p⇒q pcwp = tt
-- allImpliesPCWP {p} {q} {s = ci ∷ cis} p⇒q {st} pcwp = {!!}
--
-- {-
--
-- A ↔ B
--
--
--
--
-- with inspect' (st ⊨ CWP (ci , p)) | ⟦ proj₁ ci ⟧c st
-- allImpliesPCWP {p} {q} {ci ∷ cis} p⇒q {st} pcwp | false with≡ x | false = {!!}
-- allImpliesPCWP {p} {q} {ci ∷ cis} p⇒q {st} pcwp | true with≡ x | false = {!!}
-- allImpliesPCWP {p} {q} {ci ∷ cis} p⇒q {st} pcwp | false with≡ x | true = {!!}
-- allImpliesPCWP {p} {q} {ci ∷ cis} p⇒q {st} pcwp | true with≡ x | true = {!!}
--
-- (st ⊨ CWP (ci , p))
--
-- allImpliesPCWP {p} {q} {ci ∷ cis} p⇒q {st} () | false
-- allImpliesPCWP {p} {q} {ci ∷ cis} p⇒q {st} pcwp | true with ⟦ proj₁ ci ⟧c st
-- allImpliesPCWP {p} {q} {ci ∷ cis} p⇒q {st} pcwp | true | false = T∧ {⟦ q ⟧c st}{_} ({!impliesCWP {p} {q} {ci} p⇒q !} , allImpliesPCWP {p} {q} {cis} p⇒q {st} pcwp)
-- allImpliesPCWP {p} {q} {ci ∷ cis} p⇒q {st} pcwp | true | true = {!!}
-- -}
--
-- -- allImpliesPCWP : PCWP (s , p) → p ⇒ q → st ⊢ PCWP (s , q)
-- -- allImpliesPCWP [] imp = []
-- -- allImpliesPCWP (ci_prf ∷ cis_prfs) imp@(Impl prf) =
-- --   (impliesCWP ci_prf imp ∷ allImpliesPCWP cis_prfs imp)
--
-- {-
-- lessImpliesPCWP : (p ⇒ (PCWP ((ci ∷ cis) , q))) → (p ⇒ (PCWP (cis , q)))
-- lessImpliesPCWP {p} {_} {cis} {q} (Impl prf) = Impl prf'
--   where
--     prf' : st ⊢ p → st ⊢ (PCWP (cis , q))
--     prf' pprf with (prf pprf)
--     ... | (ci_prf ∷ cis_prfs) = cis_prfs
-- -}
-- --
--
-- Unless : ParallelProgram → Predicate → Predicate → Statement
-- Unless s p q = ⟦ (AND p (NOT q)) ⟧c ⇛ (PCWP (s , OR p q))
--
-- _▷[_]_ : Predicate → ParallelProgram → Predicate → Statement
-- _▷[_]_ p s q = Unless s p q
--
-- weakenUnlessRight : (p ▷[ s ] q) → (p ▷[ s ] (OR q r))
-- weakenUnlessRight p∧¬q = {!   !}
-- -- weakenUnlessRight (Impl prf) r = Impl prf'
-- --   where
-- --     prf' : (st : State) → st ⊢ AND p (NOT (OR q r)) → st ⊢ PCWP (s , OR p (OR q r))
-- --     prf' st st_p_q_r_or_not_and = {!   !}
--
--
-- {-
-- weakenUnlessRight : (p ▷[ s ] q) → (r : Predicate) → (p ▷[ s ] (OR q r))
-- weakenUnlessRight {p} {[]} {q} (Impl prf) r = Impl (λ pprf → [])
-- weakenUnlessRight {p} {ci ∷ cis} {q} (Impl prf) r = Impl prf'
--   where
--     prf' : st ⊢ AND p (NOT (OR q r)) → st ⊢ PCWP ((ci ∷ cis) , OR p (OR q r))
--     prf' {st} st_p_q_r_or_not_and with st_p_q_r_or_not_and
--     ... | (st_p , st_q_or_r_n) with (prf (st_p , proj₁ (notOrToAndNotNot_prf st_q_or_r_n)))
--     ...   | (ci_prf ∷ cis_prfs) =
--         (inj₁ st_p ∷ allImpliesPCWP {st} {cis} {OR p q} {OR p (OR q r)} cis_prfs (Impl prf''))
--           where
--             prf'' : st ⊢ OR p q → st ⊢ OR p (OR q r)
--             prf'' (inj₁ st_p) = inj₁ st_p
--             prf'' (inj₂ st_q) = inj₂ (inj₁ st_q)
-- --
-- -- weakenUnlessRight : (p ▷[ s ] q) → (r : Predicate) → (p ▷[ s ] (OR q r))
-- -- weakenUnlessRight {p} {[]} {q} (Impl prf) r = Impl (λ st pprf → [])
-- -- weakenUnlessRight {p} {ci ∷ cis} {q} (Impl prf) r = Impl prf'
-- --   where
-- --     prf' : (st : State) → st ⊢ AND p (NOT (OR q r)) → st ⊢ PCWP ((ci ∷ cis) , OR p (OR q r))
-- --     prf' st pprf with pprf
-- --     ... | (st_p , st_q_or_r_n) with (prf st (st_p , st_q_n))
-- --       where
-- --         st_q_n : st ⊢ NOT q
-- --         st_q_n st_q = st_q_or_r_n (inj₁ st_q)
-- --     ...   | (ci_prf ∷ cis_prfs) =
-- --         (inj₁ st_p ∷ allImpliesPCWP {st} {cis} {OR p q} {OR p (OR q r)} cis_prfs (Impl prf''))
-- --           where
-- --             prf'' : (st : State) → st ⊢ OR p q → st ⊢ OR p (OR q r)
-- --             prf'' st (inj₁ st_p) = inj₁ st_p
-- --             prf'' st (inj₂ st_q) = inj₂ (inj₁ st_q)
-- --
-- -}
--
-- Ensures : ParallelProgram → Predicate → Predicate → Statement
-- Ensures s p q = (Unless s p q × (Any (λ ci → ⟦ AND p (NOT q) ⟧c ⇛ (CWP (ci , q))) s))
--
-- _↦[_]_ : Predicate → ParallelProgram → Predicate → Statement
-- _↦[_]_ p s q = Ensures s p q
--
-- data LeadsTo : ParallelProgram → Predicate → Predicate → Statement where
--   FromEnsures : Ensures s p q → LeadsTo s p q
--   Transitivity : (LeadsTo s p q × LeadsTo s q r) → LeadsTo s p r
--   Disjunctivity : ((LeadsTo s p r) ⊎ (LeadsTo s q r)) → LeadsTo s (OR p q) r
--
-- _↪[_]_ : Predicate → ParallelProgram → Predicate → Statement
-- _↪[_]_ p s q = LeadsTo s p q
