module Statements where

open import Data.Unit
open import Data.Bool
open import Data.Bool.Properties
-- open import Data.Nat
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Relation.Binary.PropositionalEquality as Eq
open import Function

open import Simple
open module NatOnly = Simple.Program (λ n → Nat)

⌝_ : Predicate → Predicate
⌝_ = NOT

infixr 6 _△_
_△_ : Predicate → Predicate → Predicate
_△_ = AND

infixr 5 _▽_
_▽_ : Predicate → Predicate → Predicate
_▽_ = OR

-- open Simple.NatOnly using (NatOnly)

-- postulate
--   VarTypes : ℕ → Types
--
-- module Example = Simple.Program VarTypes
-- open Example

variable
  P P₁ Q Q₁ R B :  Predicate
  A A₁ A₂ A₃ a b : Assertion
  c d : Condition
  i : Instruction
  s0 ci : ConditionalInstruction
  cis : List ConditionalInstruction
  S : ParallelProgram
  st : State
  W X Y Z : Set

Statement : Set₁
Statement = Set

--


-- Predicate implication
infix 4 _⇒_
_⇒_ : Predicate → Predicate → Statement
P ⇒ Q = ∀{st} → st ⊢ P → st ⊢ Q

_⇐_ : Predicate → Predicate → Statement
P ⇐ Q = Q ⇒ P

⇒-⌝-Reverse : (P ⇒ Q) → ((⌝ Q) ⇒ (⌝ P))
⇒-⌝-Reverse p⇒q = λ ⌝q p → ⌝q (p⇒q p)

⇐-⌝-Reverse : (P ⇐ Q) → ((⌝ Q) ⇐ (⌝ P))
⇐-⌝-Reverse p⇐q = λ ⌝p q → ⌝p (p⇐q q)


-- Predicate Equivalence
_⇔_ : Predicate → Predicate → Statement
P ⇔ Q = (P ⇒ Q) × (P ⇐ Q)

⇔Symmetric : (P ⇔ Q) → (Q ⇔ P)
⇔Symmetric (p⇒q , p⇐q) = (p⇐q , p⇒q)

⇔-⌝-Compatible : (P ⇔ Q) → ((⌝ P) ⇔ (⌝ Q))
⇔-⌝-Compatible (p⇒q , p⇐q) = ((⇒-⌝-Reverse p⇐q) , (⇒-⌝-Reverse p⇒q))


-- Assertion implication

infix 4 _⇛_
_⇛_ : Assertion → Assertion → Statement
a ⇛ b = ∀{st} → st ⊩ a → st ⊩ b

_⇚_ : Assertion → Assertion → Statement
a ⇚ b = b ⇛ a

_⇚⇛_ : Assertion → Assertion → Statement
a ⇚⇛ b = (a ⇛ b) × (a ⇚ b)

⇚⇛-Symmetric : (a ⇚⇛ b) → (a ⇚⇛ b)
⇚⇛-Symmetric (a⇛b , b⇚a) = (a⇛b , b⇚a)


--

→Disjunctive : (Z → X ⊎ Y) → ((X → W) × (Y → W)) → (Z → W)
→Disjunctive z→x⊎y (x→z , y→z) z with (z→x⊎y z)
→Disjunctive z→x⊎y (x→z , y→z) z | inj₁ x = x→z x
→Disjunctive z→x⊎y (x→z , y→z) z | inj₂ y = y→z y

⇒Disjunctive : (R ⇒ P ▽ Q) → (P ⇒ B × Q ⇒ B) → (R ⇒ B)
⇒Disjunctive r⇒p▽q (p⇒b , q⇒b) r with (r⇒p▽q r)
⇒Disjunctive r⇒p▽q (p⇒b , q⇒b) r | inj₁ p = p⇒b p
⇒Disjunctive r⇒p▽q (p⇒b , q⇒b) r | inj₂ q = q⇒b q

⇛Disjunctive : (R ⇒ P ▽ Q) → (⟦ P ⟧a ⇛ A × ⟦ Q ⟧a ⇛ A) → (⟦ R ⟧a ⇛ A)
⇛Disjunctive r⇒p▽q (p⇛a , q⇛a) r with (r⇒p▽q r)
⇛Disjunctive r⇒p▽q (p⇛a , q⇛a) r | inj₁ p = p⇛a p
⇛Disjunctive r⇒p▽q (p⇛a , q⇛a) r | inj₂ q = q⇛a q

--

orCommutative : P ▽ Q ⇒ Q ▽ P
orCommutative (inj₁ p) = inj₂ p
orCommutative (inj₂ q) = inj₁ q

andCommutative : P △ Q ⇒ Q △ P
andCommutative (p , q) = (q , p)

--

weaken : P ⇒ P ▽ Q
weaken = inj₁

strenghten : P △ Q ⇒ P
strenghten = proj₁

impliesOrLeft : P ⇒ R → P ▽ Q ⇒ R ▽ Q
impliesOrLeft p⇒r (inj₁ p) = inj₁ (p⇒r p)
impliesOrLeft p⇒r (inj₂ q) = inj₂ q

impliesOrRight : Q ⇒ R → P ▽ Q ⇒ P ▽ R
impliesOrRight q⇒r = orCommutative ∘ impliesOrLeft q⇒r ∘ orCommutative

impliesAndLeft : P ⇒ R → P △ Q ⇒ R △ Q
impliesAndLeft p⇒r (p , q) = (p⇒r p , q)

impliesAndRight : Q ⇒ R → P △ Q ⇒ P △ R
impliesAndRight q⇒r = andCommutative ∘ impliesAndLeft q⇒r ∘ andCommutative

--

weakenOrLeft : P ▽ Q ⇒ (P ▽ R) ▽ Q
weakenOrLeft = impliesOrLeft weaken

weakenOrRight : P ▽ Q ⇒ P ▽ (Q ▽ R)
weakenOrRight = impliesOrRight weaken

strenghtenOrLeft : (P △ R) ▽ Q ⇒ P ▽ Q
strenghtenOrLeft = impliesOrLeft strenghten

strenghtenOrRight : P ▽ (Q △ R) ⇒ P ▽ Q
strenghtenOrRight = impliesOrRight strenghten

weakenAndLeft : P △ Q ⇒ (P ▽ R) △ Q
weakenAndLeft = impliesAndLeft weaken

weakenAndRight : P △ Q ⇒ P △ (Q ▽ R)
weakenAndRight = impliesAndRight weaken

strenghtenAndLeft : (P △ R) △ Q ⇒ P △ Q
strenghtenAndLeft = impliesAndLeft strenghten

strenghtenAndRight : P △ (Q △ R) ⇒ P △ Q
strenghtenAndRight = impliesAndRight strenghten

--

impliesTrans : (P ⇒ Q) → (Q ⇒ R) → (P ⇒ R)
impliesTrans p⇒q q⇒r p = q⇒r (p⇒q p)

strenghtenImpliesLeft : (P ⇒ Q) → (P △ R ⇒ Q)
strenghtenImpliesLeft p⇒q p∧r = p⇒q (proj₁ p∧r)

weakenImpliesRight : (P ⇒ Q) → (P ⇒ Q ▽ R)
weakenImpliesRight p⇒q p = inj₁ (p⇒q p)

-- Distributivity

andDistributiveToLeft : (P △ (Q ▽ R)) ⇒ ((P △ Q) ▽ (P △ R))
andDistributiveToLeft (p , inj₁ q) = inj₁ (p , q)
andDistributiveToLeft (p , inj₂ r) = inj₂ (p , r)

andDistributiveFromLeft : (P △ (Q ▽ R)) ⇐ ((P △ Q) ▽ (P △ R))
andDistributiveFromLeft (inj₁ (p , q)) = (p , inj₁ q)
andDistributiveFromLeft (inj₂ (p , r)) = (p , inj₂ r)

andDistributiveLeft : (P △ (Q ▽ R)) ⇔ ((P △ Q) ▽ (P △ R))
andDistributiveLeft = (andDistributiveToLeft , andDistributiveFromLeft)

--

andDistributiveToRight : ((P ▽ Q) △ R) ⇒ ((P △ R) ▽ (Q △ R))
andDistributiveToRight (inj₁ p , r) = inj₁ (p , r)
andDistributiveToRight (inj₂ q , r) = inj₂ (q , r)

andDistributiveFromRight : ((P ▽ Q) △ R) ⇐ ((P △ R) ▽ (Q △ R))
andDistributiveFromRight (inj₁ (p , r)) = (inj₁ p , r)
andDistributiveFromRight (inj₂ (q , r)) = (inj₂ q , r)

andDistributiveRight : ((P ▽ Q) △ R) ⇔ ((P △ R) ▽ (Q △ R))
andDistributiveRight = (andDistributiveToRight , andDistributiveFromRight)

--

orDistributiveToLeft : (P ▽ (Q △ R)) ⇒ ((P ▽ Q) △ (P ▽ R))
orDistributiveToLeft (inj₁ p) = (inj₁ p , inj₁ p)
orDistributiveToLeft (inj₂ (q , r)) = (inj₂ q , inj₂ r)

orDistributiveFromLeft : (P ▽ (Q △ R)) ⇐ ((P ▽ Q) △ (P ▽ R))
orDistributiveFromLeft (inj₁ p , p∨r) = inj₁ p
orDistributiveFromLeft (inj₂ q , inj₁ p) = inj₁ p
orDistributiveFromLeft (inj₂ q , inj₂ r) = inj₂ (q , r)

orDistributiveLeft : (P ▽ (Q △ R)) ⇔ ((P ▽ Q) △ (P ▽ R))
orDistributiveLeft = (orDistributiveToLeft , orDistributiveFromLeft)

--

orDistributiveToRight : ((P △ Q) ▽ R) ⇒ ((P ▽ R) △ (Q ▽ R))
orDistributiveToRight (inj₁ (p , q)) = (inj₁ p , inj₁ q)
orDistributiveToRight (inj₂ r) = (inj₂ r , inj₂ r)

orDistributiveFromRight : ((P △ Q) ▽ R) ⇐ ((P ▽ R) △ (Q ▽ R))
orDistributiveFromRight (inj₂ r , q∨r) = inj₂ r
orDistributiveFromRight (inj₁ p , inj₂ r) = inj₂ r
orDistributiveFromRight (inj₁ p , inj₁ q) = inj₁ (p , q)

orDistributiveRight : ((P △ Q) ▽ R) ⇔ ((P ▽ R) △ (Q ▽ R))
orDistributiveRight = (orDistributiveToRight , orDistributiveFromRight)


-- De Morgan

notOrToAndNotNot : ⌝ (P ▽ Q) ⇒ (⌝ P) △ (⌝ Q)
notOrToAndNotNot ¬_p∨q_ = ((¬_p∨q_ ∘ inj₁) , (¬_p∨q_ ∘ inj₂))

-- notAndToOrNotNot : NOT (AND P Q) ⇒ OR (NOT P) (NOT Q)
-- notAndToOrNotNot {P} {Q} {st} ¬_p∧q_ = {!   !}

notAndToOrNotNot : ⌝ (P △ Q) ⇒ (⌝ P) ▽ (⌝ Q)
notAndToOrNotNot {P} {Q} {st} ¬_p∧q_ with assertionDecidability {P} {st}
notAndToOrNotNot {P} {Q} {st} ¬_p∧q_ | inj₁ ¬p = inj₁ ¬p
-- notAndToOrNotNot {P} {Q} {st} ¬_p∧q_ | inj₂ p = inj₂ (λ x → ¬_p∧q_ (p , x))
notAndToOrNotNot {P} {Q} {st} ¬_p∧q_ | inj₂ p = inj₂ ¬q
  where
    ¬q : st ⊢ (⌝ Q)
    ¬q = λ q → ¬_p∧q_ (p , q)

--

allImplies : {A : Set} → {f g : A → Set} → {l : List A} → ({a : A} → f a → g a) → All f l → All g l
allImplies fa→ga [] = []
allImplies fa→ga (fl ∷ fls) = (fa→ga fl) ∷ (allImplies fa→ga fls)

anyImplies : {A : Set} → {f g : A → Set} → {l : List A} → ({a : A} → f a → g a) → Any f l → Any g l
anyImplies fa→ga (here hl) = here (fa→ga hl)
anyImplies fa→ga (there tl) = there (anyImplies fa→ga tl)

--

WP : (Instruction × Predicate) → Assertion
WP (i , P) = λ st → (⟦ i ⟧i st) ⊢ P

WP-⇒-Compatible : P ⇒ Q → WP (i , P) ⇛ WP (i , Q)
WP-⇒-Compatible p⇒q wp = p⇒q wp

WP-⇐-Compatible : P ⇐ Q → WP (i , P) ⇚ WP (i , Q)
WP-⇐-Compatible p⇐q wp = p⇐q wp

CWP : (ConditionalInstruction × Predicate) → Assertion
CWP (ci , P) = λ st → (⟦ ci ⟧ci st) ⊢ P

PCWP : (ParallelProgram × Predicate) → Assertion
PCWP ((s0 , S) , P) = λ st → All (λ ci → st ⊩ (CWP (ci , P))) S

--

impliesCWP : P ⇒ Q → (CWP (ci , P)) ⇛ (CWP (ci , Q))
impliesCWP p⇒q cwp = p⇒q cwp

lessPCWP : PCWP ((s0 , (ci ∷ cis)) , P) ⇛ PCWP ((s0 , cis) , P)
lessPCWP (ci_prf ∷ cis_prfs) = cis_prfs

-- morePCWP : ⟦ CWP (ci , P) ⟧a → PCWP (cis , P) ⇛ PCWP ((ci ∷ cis) , P)
-- morePCWP cwp pcwp = ?

impliesPCWP : P ⇒ Q → PCWP (S , P) ⇛ PCWP (S , Q)
impliesPCWP p⇒q [] = []
impliesPCWP p⇒q (ci_prf ∷ cis_prfs) = p⇒q ci_prf ∷ impliesPCWP p⇒q cis_prfs

lessImpliesPCWP : (⟦ P ⟧a ⇛ (PCWP ((s0 , (ci ∷ cis)) , Q))) → (⟦ P ⟧a ⇛ (PCWP ((s0 , cis) , Q)))
lessImpliesPCWP p⇛pcwp = λ p → lessPCWP (p⇛pcwp p)

--

Unless : ParallelProgram → Predicate → Predicate → Statement
Unless S P Q = ⟦ (P △ (⌝ Q)) ⟧a ⇛ (PCWP (S , P ▽ Q))

infix 4 _▷[_]_
_▷[_]_ : Predicate → ParallelProgram → Predicate → Statement
_▷[_]_ P S Q = Unless S P Q


▷-⇔-left : P ⇔ Q → P ▷[ S ] R → Q ▷[ S ] R
▷-⇔-left (p⇒q , p⇐q) p▷[s]r (q , ¬r) =
  impliesPCWP
    (impliesOrLeft p⇒q)
    (p▷[s]r (p⇐q q , ¬r))


lessUnless : (P ▷[ s0 , ci ∷ cis ] Q) → (P ▷[ s0 , cis ] Q)
lessUnless p▷[ci∷cis]q = λ p△⌝q → lessPCWP (p▷[ci∷cis]q p△⌝q)

impliesUnlessRight : Q ⇒ R → (P ▷[ S ] Q) → (P ▷[ S ] R)
impliesUnlessRight q⇒r p▷[s]q (p , ¬r) =
  impliesPCWP (λ { (inj₁ p) → inj₁ p ; (inj₂ q) → inj₂ (q⇒r q) }) (p▷[s]q (p , ¬r ∘ q⇒r))

-- impliesUnlessRight : Q ⇒ R → (P ▷[ S ] Q) → (P ▷[ S ] R)
-- impliesUnlessRight q⇒r p▷[s]q (p , ⌝r) with (p▷[s]q (p , (λ q → ⌝r (q⇒r q))))
-- ... | [] = []
-- ... | inj₁ p_ ∷ rest = inj₁ p_ ∷ impliesUnlessRight q⇒r (lessUnless p▷[s]q) (p , ⌝r)
-- ... | inj₂ q_ ∷ rest = (inj₂ (q⇒r q_ )) ∷ impliesUnlessRight q⇒r (lessUnless p▷[s]q) (p , ⌝r)

weakenUnlessRight' : Q ⇒ R → (P ▷[ S ] Q) → (P ▷[ S ] (Q ▽ R))
weakenUnlessRight' q⇒r p∧¬q⇛pcwp (p , ¬_q∨r_) =
  impliesPCWP weakenOrRight (p∧¬q⇛pcwp (p , (¬_q∨r_ ∘ inj₁)))

weakenUnlessRight : (P ▷[ S ] Q) → (P ▷[ S ] (Q ▽ R))
weakenUnlessRight = impliesUnlessRight weaken

-- weakenUnlessRight : (P ▷[ S ] Q) → (P ▷[ S ] (OR Q R))
-- weakenUnlessRight {P} {Q = Q} p∧¬q⇛pcwp (p , ¬_q∨r_) =
--   impliesPCWP weakenOrRight (p∧¬q⇛pcwp (p , (¬_q∨r_ ∘ inj₁)))
  -- λ { (p , ¬_q∨r_) → impliesPCWP {OR P Q} weakenOrRight (p∧¬q⇛pcwp (p , (λ q → ¬_q∨r_ (inj₁ q)) }

unlessDisjunctive : ((P ▷[ S ] R) × (Q ▷[ S ] R)) → (P ▽ Q ▷[ S ] R)
unlessDisjunctive (p▷[s]r , q▷[s]r) (inj₁ p , ⌝r) = impliesPCWP (impliesOrLeft weaken) (p▷[s]r (p , ⌝r))
unlessDisjunctive (p▷[s]r , q▷[s]r) (inj₂ q , ⌝r) = impliesPCWP (impliesOrLeft (orCommutative ∘ weaken)) (q▷[s]r (q , ⌝r))

-- FALSE
-- impliesUnlessLeft : P ⇒ Q → Q ▷[ S ] R → P ▷[ S ] R
-- impliesUnlessLeft p⇒q q▷[s]r (p , ⌝r) with q▷[s]r (p⇒q p , ⌝r)
-- ... | [] = []
-- ... | inj₁ q_ ∷ rest = {!   !} ∷ (impliesUnlessLeft p⇒q (lessUnless q▷[s]r) ((p , ⌝r)))
-- ... | inj₂ r_ ∷ rest = (inj₂ r_) ∷ (impliesUnlessLeft p⇒q (lessUnless q▷[s]r) ((p , ⌝r)))

unlessReflexive : P ▷[ S ] P
-- unlessReflexive : {P : Predicate} → (P ▷[ S ] P)
unlessReflexive (p , ¬p) = ⊥-elim (¬p p)

unlessFromImplies : (P ⇒ Q) → (P ▷[ S ] Q)
-- unlessFromImplies p⇒q (p , ¬q) = ⊥-elim (¬q (p⇒q p))
unlessFromImplies p⇒q = impliesUnlessRight p⇒q unlessReflexive

--

Progress : ParallelProgram → Predicate → Predicate → Statement
Progress (s0 , cis) P Q = (Any (λ ci → ⟦ P △ ⌝ Q ⟧a ⇛ (CWP (ci , Q))) cis)

infix 4 _↣[_]_
_↣[_]_ : Predicate → ParallelProgram → Predicate → Statement
_↣[_]_ P S Q = Progress S P Q


↣-⇔-left : P ⇔ Q → P ↣[ S ] R → Q ↣[ S ] R
↣-⇔-left (p⇒q , p⇐q) p↣[s]r =
  anyImplies
    (λ { f (q , ⌝r) → f (p⇐q q , ⌝r) })
    p↣[s]r

--

-- "Biztosítja"
Ensures : ParallelProgram → Predicate → Predicate → Statement
Ensures S P Q = (Unless S P Q × Progress S P Q)

infix 4 _↦[_]_
_↦[_]_ : Predicate → ParallelProgram → Predicate → Statement
_↦[_]_ P S Q = Ensures S P Q


⇔-↦-left : P ⇔ Q → P ↦[ S ] R → Q ↦[ S ] R
⇔-↦-left p⇔q (p▷[s]r , p↣[s]r) = (▷-⇔-left p⇔q p▷[s]r , ↣-⇔-left p⇔q p↣[s]r)

-- FALSE
-- impliesEnsuresLeft : P ⇒ Q → P ↦[ S ] R → Q ↦[ S ] R
-- impliesEnsuresLeft p⇒q (p▷[s]r , progress) = {!   !}

-- tmp' : (P ▽ Q) △ ⌝ R ⇒ (P △ ⌝ R) ▽ (Q △ ⌝ R)
-- tmp' (inj₁ p , ⌝r) = inj₁ (p , ⌝r)
-- tmp' (inj₂ q , ⌝r) = inj₂ (q , ⌝r)
--
-- tmp : (⟦ P △ ⌝ R ⟧a ⇛ CWP (ci , R) × ⟦ Q △ ⌝ R ⟧a ⇛ CWP (ci , R)) → ⟦ (P ▽ Q) △ ⌝ R ⟧a ⇛ CWP (ci , R)
-- tmp (x , y) = ⇛Disjunctive tmp' (x , y)

-- FALSE
-- ensuresDisjunctive : ((P ↦[ S ] R) × (Q ↦[ S ] R)) → (P ▽ Q ↦[ S ] R)
-- ensuresDisjunctive ((P▷[S]R , existsP) , (Q▷[S]R , existsQ)) =
--   (unlessDisjunctive (P▷[S]R , Q▷[S]R) , {!   !})

-- -- ensuresDisjunctive : (P ↦[ S ] R) ⊎ (P ↦[ S ] R) → (P ▽ Q ↦[ S ] R)
-- -- ensuresDisjunctive (inj₁ (P▷[S]R , exists)) = ({!   !} , anyImplies {!   !} exists)
-- -- ensuresDisjunctive (inj₂ (Q▷[S]R , exists)) = ({!   !} , {!   !})

--

-- "Elkerülhetetlen / Inevitable"
data LeadsTo : ParallelProgram → Predicate → Predicate → Statement where
  FromEnsures : Ensures S P Q → LeadsTo S P Q
  Transitivity : (LeadsTo S P Q × LeadsTo S Q R) → LeadsTo S P R
  Disjunctivity : ((LeadsTo S P R) × (LeadsTo S Q R)) → LeadsTo S (P ▽ Q) R

infix 4 _↪[_]_
_↪[_]_ : Predicate → ParallelProgram → Predicate → Statement
_↪[_]_ P S Q = LeadsTo S P Q


⇔-↪-left : P ⇔ Q → P ↪[ S ] R → Q ↪[ S ] R
⇔-↪-left p⇔q (FromEnsures p↦[s]r) = FromEnsures (⇔-↦-left p⇔q p↦[s]r)
-- ⇔-↪-left p⇔q (Transitivity (p↪[s]p₁ , p₁↪[s]r)) = Transitivity (⇔-↪-left p⇔q p↪[s]p₁ , p₁↪[s]r)
⇔-↪-left p⇔q (Transitivity (p↪[s]q , q↪[s]r)) = Transitivity (⇔-↪-left p⇔q p↪[s]q , q↪[s]r)
⇔-↪-left p⇔q (Disjunctivity (p↪[s]r , q↪[s]r)) = {!Disjunctivity {} (? , ?)!}

-- impliesLeadsToLeft : P ⇒ Q → P ↪[ S ] R → Q ↪[ S ] R
-- impliesLeadsToLeft p⇒q (FromEnsures ensures) = FromEnsures (impliesEnsuresLeft p⇒q ensures)
-- impliesLeadsToLeft p⇒q (Transitivity (p↪[s]p₁ , p₁↪[s]r)) = {!   !}
-- impliesLeadsToLeft p⇒q (Disjunctivity (p₁↪[s]r , p₂↪[s]r)) = {!   !}

--

Invariant : ParallelProgram -> Predicate -> Statement
Invariant S P = ⟦ P ⟧a ⇛ (PCWP (S , P))

infix 4 _∈inv[_]
_∈inv[_] : Predicate → ParallelProgram → Statement
P ∈inv[ S ] = Invariant S P

-- init
-- FP
-- TERM

-- PSP

pspFromEnsures₁ : P ▷[ S ] Q → R ▷[ S ] B → (P △ R) ▷[ S ] (Q △ R ▽ B)
pspFromEnsures₁ p▷[s]q r▷[s]b _p△r_△⌝_q△r▽b_@((p , r) , ⌝_q△r▽b_) with (notOrToAndNotNot ⌝_q△r▽b_)
... | ⌝_q△r_ , ⌝b with (r▷[s]b (r , ⌝b))
...   | [] = []
...   | inj₁ r' ∷ rest with (p▷[s]q (p , λ q → ⌝_q△r_ (q , r)))
...     | inj₁ p' ∷ rest' = inj₁ (p' , r') ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_
...     | inj₂ q' ∷ rest' = inj₂ (inj₁ (q' , r')) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_
pspFromEnsures₁ p▷[s]q r▷[s]b _p△r_△⌝_q△r▽b_@((p , r) , ⌝_q△r▽b_) | ⌝_q△r_ , ⌝b -- ...
      | inj₂ b_ ∷ rest = inj₂ (inj₂ b_) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_

pspFromEnsures₂ : P ▷[ S ] Q → R ▷[ S ] B → P ↣[ S ] Q → Progress S (P △ R) (Q △ R ▽ B)
pspFromEnsures₂ {P} {S = (s0 , ci ∷ cis)} {Q} {R} {B} p▷[s]q r▷[s]b (here p△⌝q⇛cwp) = here f
  where
    f : ⟦ (P △ R) △ (⌝ (Q △ R ▽ B)) ⟧a ⇛ CWP (ci , Q △ R ▽ B)
    f ((p , r) , ⌝_q△r▽b_) with (notOrToAndNotNot ⌝_q△r▽b_)
    ... | ⌝_q△r_ , ⌝b with (r▷[s]b (r , ⌝b))
    ...   | inj₁ r' ∷ rest with (p▷[s]q (p , λ q → ⌝_q△r_ (q , r)))
    ...     | inj₁ p' ∷ rest' = inj₁ (p△⌝q⇛cwp (p , (λ q → ⌝_q△r_ (q , r))) , r')
    ...     | inj₂ q' ∷ rest' = inj₁ (q' , r')
    f ((p , r) , ⌝_q△r▽b_) | ⌝_q△r_ , ⌝b -- ...
          | inj₂ b_ ∷ rest = inj₂ b_
pspFromEnsures₂ p▷[s]q r▷[s]b (there rest) = there (pspFromEnsures₂ (lessUnless p▷[s]q) (lessUnless r▷[s]b) rest)

pspFromEnsures : P ↦[ S ] Q → R ▷[ S ] B → (P △ R) ↦[ S ] (Q △ R ▽ B)
pspFromEnsures (p▷[s]q , p↣[s]q) r▷[s]b = (pspFromEnsures₁ p▷[s]q r▷[s]b , pspFromEnsures₂ p▷[s]q r▷[s]b p↣[s]q)

--

pspFromTransitivity : (P ↪[ S ] P₁ × P₁ ↪[ S ] Q) → R ▷[ S ] B → (P △ R) ↪[ S ] ((Q △ R) ▽ B)
pspFromTransitivity (p↪[s]q₁ , q₁↪[s]q) r▷[s]b = {!   !}

--

PSP : ((P ↪[ S ] Q) × (R ▷[ S ] B)) → (P △ R) ↪[ S ] ((Q △ R) ▽ B)

pspFromDisjunctivity : (P ↪[ S ] Q × P₁ ↪[ S ] Q) → R ▷[ S ] B → ((P ▽ P₁) △ R) ↪[ S ] (Q △ R ▽ B)
pspFromDisjunctivity {P} {S} {Q} {P₁} {R} (p₁↪[s]q₁ , p₂↪[s]q₁) r▷[s]b =
  ⇔-↪-left {(P △ R) ▽ (P₁ △ R)} {(P ▽ P₁) △ R}
    (⇔Symmetric andDistributiveRight)
    (Disjunctivity (PSP (p₁↪[s]q₁ , r▷[s]b) , PSP (p₂↪[s]q₁ , r▷[s]b)))


PSP (FromEnsures ensures , r▷[s]b) = FromEnsures (pspFromEnsures ensures r▷[s]b)
PSP (Transitivity transitivity , r▷[s]b) = pspFromTransitivity transitivity r▷[s]b
PSP (Disjunctivity disjunctivity , r▷[s]b) = pspFromDisjunctivity disjunctivity r▷[s]b
