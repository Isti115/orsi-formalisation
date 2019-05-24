
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
  P Q R B : Predicate
  a b : Assertion
  c d : Condition
  i : Instruction
  ci : ConditionalInstruction
  cis S : ParallelProgram
  st : State

Statement : Set₁
Statement = Set

--

_⇒_ : Predicate → Predicate → Statement
P ⇒ Q = ∀{st} → st ⊢ P → st ⊢ Q
--
_⇛_ : Assertion → Assertion → Statement
a ⇛ b = ∀{st} → st ⊩ a → st ⊩ b

--

orCommutative : OR P Q ⇒ OR Q P
orCommutative (inj₁ p) = inj₂ p
orCommutative (inj₂ q) = inj₁ q

andCommutative : AND P Q ⇒ AND Q P
andCommutative (p , q) = (q , p)

--

weakenOrLeft : OR P Q ⇒ OR (OR P R) Q
weakenOrLeft (inj₁ p) = inj₁ (inj₁ p)
weakenOrLeft (inj₂ q) = inj₂ q

weakenOrRight : OR P Q ⇒ OR P (OR Q R)
weakenOrRight = orCommutative ∘ weakenOrLeft ∘ orCommutative

strenghtenOrLeft : OR (AND P R) Q ⇒ OR P Q
strenghtenOrLeft (inj₁ (p , r)) = inj₁ p
strenghtenOrLeft (inj₂ q) = inj₂ q

strenghtenOrRight : OR P (AND Q R) ⇒ OR P Q
strenghtenOrRight = orCommutative ∘ strenghtenOrLeft ∘ orCommutative

--

weakenAndLeft : AND P Q ⇒ AND (OR P R) Q
weakenAndLeft (p , q) = (inj₁ p , q)

weakenAndRight : AND P Q ⇒ AND P (OR Q R)
weakenAndRight = andCommutative ∘ weakenAndLeft ∘ andCommutative

strenghtenAndLeft : AND (AND P R) Q ⇒ AND P Q
strenghtenAndLeft ((p , r) , q) = (p , q)

strenghtenAndRight : AND P (AND Q R) ⇒ AND P Q
strenghtenAndRight = andCommutative ∘ strenghtenAndLeft ∘ andCommutative

--

impliesTrans : (P ⇒ Q) → (Q ⇒ R) → (P ⇒ R)
impliesTrans p⇒q q⇒r p = q⇒r (p⇒q p)

strenghtenImpliesLeft : (P ⇒ Q) → (AND P R ⇒ Q)
strenghtenImpliesLeft p⇒q p∧r = p⇒q (proj₁ p∧r)

weakenImpliesRight : (P ⇒ Q) → (P ⇒ OR Q R)
weakenImpliesRight p⇒q p = inj₁ (p⇒q p)

-- De Morgan

notOrToAndNotNot : NOT (OR P Q) ⇒ AND (NOT P) (NOT Q)
notOrToAndNotNot ¬_p∨q_ = ((λ p → ¬_p∨q_ (inj₁ p)) , (λ q → ¬_p∨q_ (inj₂ q)))

-- notAndToOrNotNot : NOT (AND P Q) ⇒ OR (NOT P) (NOT Q)
-- notAndToOrNotNot {P} {Q} {st} ¬_p∧q_ = {!   !}

notAndToOrNotNot : NOT (AND P Q) ⇒ OR (NOT P) (NOT Q)
notAndToOrNotNot {P} {Q} {st} ¬_p∧q_ with assertionDecidability {P} {st}
notAndToOrNotNot {P} {Q} {st} ¬_p∧q_ | inj₁ ¬p = inj₁ ¬p
-- notAndToOrNotNot {P} {Q} {st} ¬_p∧q_ | inj₂ p = inj₂ (λ x → ¬_p∧q_ (p , x))
notAndToOrNotNot {P} {Q} {st} ¬_p∧q_ | inj₂ p = inj₂ ¬q
  where
    ¬q : st ⊢ NOT Q
    ¬q = λ q → ¬_p∧q_ (p , q)

--

WP : (Instruction × Predicate) → Assertion
WP (i , P) = λ st → (⟦ i ⟧i st) ⊢ P

CWP : (ConditionalInstruction × Predicate) → Assertion
CWP (ci , P) = λ st → (⟦ ci ⟧ci st) ⊢ P

PCWP : (ParallelProgram × Predicate) → Assertion
PCWP (S , P) = λ st → All (λ ci → st ⊩ (CWP (ci , P))) S

--

impliesCWP : P ⇒ Q → (CWP (ci , P)) ⇛ (CWP (ci , Q))
impliesCWP p⇒q cwp = p⇒q cwp

lessPCWP : PCWP ((ci ∷ cis) , P) ⇛ PCWP (cis , P)
lessPCWP (ci_prf ∷ cis_prfs) = cis_prfs

allImpliesPCWP : P ⇒ Q → PCWP (S , P) ⇛ PCWP (S , Q)
allImpliesPCWP p⇒q [] = []
allImpliesPCWP p⇒q (ci_prf ∷ cis_prfs) = p⇒q ci_prf ∷ allImpliesPCWP p⇒q cis_prfs

lessImpliesPCWP : (⟦ P ⟧a ⇛ (PCWP ((ci ∷ cis) , Q))) → (⟦ P ⟧a ⇛ (PCWP (cis , Q)))
lessImpliesPCWP p⇛pcwp p = lessPCWP (p⇛pcwp p)

--

Unless : ParallelProgram → Predicate → Predicate → Statement
Unless S P Q = ⟦ (AND P (NOT Q)) ⟧a ⇛ (PCWP (S , OR P Q))

_▷[_]_ : Predicate → ParallelProgram → Predicate → Statement
_▷[_]_ P S Q = Unless S P Q

weakenUnlessRight : (P ▷[ S ] Q) → (P ▷[ S ] (OR Q R))
weakenUnlessRight {P} {Q = Q} p∧¬q⇛pcwp (p , ¬_q∨r_) =
  allImpliesPCWP weakenOrRight (p∧¬q⇛pcwp (p , (¬_q∨r_ ∘ inj₁)))
  -- λ { (p , ¬_q∨r_) → allImpliesPCWP {OR P Q} weakenOrRight (p∧¬q⇛pcwp (p , (λ q → ¬_q∨r_ (inj₁ q)) }

Ensures : ParallelProgram → Predicate → Predicate → Statement
Ensures S P Q = (Unless S P Q × (Any (λ ci → ⟦ AND P (NOT Q) ⟧a  ⇛ (CWP (ci , Q))) S))

_↦[_]_ : Predicate → ParallelProgram → Predicate → Statement
_↦[_]_ P S Q = Ensures S P Q

data LeadsTo : ParallelProgram → Predicate → Predicate → Statement where
  FromEnsures : Ensures S P Q → LeadsTo S P Q
  Transitivity : (LeadsTo S P Q × LeadsTo S Q R) → LeadsTo S P R
  Disjunctivity : ((LeadsTo S P R) ⊎ (LeadsTo S Q R)) → LeadsTo S (OR P Q) R

_↪[_]_ : Predicate → ParallelProgram → Predicate → Statement
_↪[_]_ P S Q = LeadsTo S P Q

Invariant : ParallelProgram -> Predicate -> Statement
Invariant S P = ⟦ P ⟧a ⇛ (PCWP (S , P))

_∈inv[_] : Predicate → ParallelProgram → Statement
P ∈inv[ S ] = Invariant S P

-- PSP

PSP : ((P ↪[ S ] Q) × (R ▷[ S ] B)) → (AND P R) ↪[ S ] (OR (AND Q R) B)
-- PSP (P↪[S]Q , R▷[S]B) = {!   !}
PSP (FromEnsures (P▷[S]Q , exists) , R▷[S]B) = {!  !}
PSP (Transitivity (P↪[S]Q₁ , Q₁↪[S]Q) , R▷[S]B) = {!   !}
PSP (Disjunctivity (inj₁ P↪[S]Q₁) , R▷[S]B) = {!   !}
PSP (Disjunctivity (inj₂ Q↪[S]Q₁) , R▷[S]B) = {!   !}
