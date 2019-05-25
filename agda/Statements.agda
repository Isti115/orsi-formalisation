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
  A A₁ A₂ A₃ a b : Assertion
  c d : Condition
  i : Instruction
  ci : ConditionalInstruction
  cis S : ParallelProgram
  st : State
  W X Y Z : Set

Statement : Set₁
Statement = Set

--

infix 4 _⇒_
_⇒_ : Predicate → Predicate → Statement
P ⇒ Q = ∀{st} → st ⊢ P → st ⊢ Q

infix 4 _⇛_
_⇛_ : Assertion → Assertion → Statement
a ⇛ b = ∀{st} → st ⊩ a → st ⊩ b

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

orCommutative : OR P Q ⇒ OR Q P
orCommutative (inj₁ p) = inj₂ p
orCommutative (inj₂ q) = inj₁ q

andCommutative : AND P Q ⇒ AND Q P
andCommutative (p , q) = (q , p)

--

weaken : P ⇒ OR P Q
weaken = inj₁

strenghten : AND P Q ⇒ P
strenghten = proj₁

impliesOrLeft : P ⇒ R → OR P Q ⇒ OR R Q
impliesOrLeft p⇒r (inj₁ p) = inj₁ (p⇒r p)
impliesOrLeft p⇒r (inj₂ q) = inj₂ q

impliesOrRight : Q ⇒ R → OR P Q ⇒ OR P R
impliesOrRight q⇒r = orCommutative ∘ impliesOrLeft q⇒r ∘ orCommutative

impliesAndLeft : P ⇒ R → AND P Q ⇒ AND R Q
impliesAndLeft p⇒r (p , q) = (p⇒r p , q)

impliesAndRight : Q ⇒ R → AND P Q ⇒ AND P R
impliesAndRight q⇒r = andCommutative ∘ impliesAndLeft q⇒r ∘ andCommutative

--

weakenOrLeft : OR P Q ⇒ OR (OR P R) Q
weakenOrLeft = impliesOrLeft weaken

weakenOrRight : OR P Q ⇒ OR P (OR Q R)
weakenOrRight = impliesOrRight weaken

strenghtenOrLeft : OR (AND P R) Q ⇒ OR P Q
strenghtenOrLeft = impliesOrLeft strenghten

strenghtenOrRight : OR P (AND Q R) ⇒ OR P Q
strenghtenOrRight = impliesOrRight strenghten

weakenAndLeft : AND P Q ⇒ AND (OR P R) Q
weakenAndLeft = impliesAndLeft weaken

weakenAndRight : AND P Q ⇒ AND P (OR Q R)
weakenAndRight = impliesAndRight weaken

strenghtenAndLeft : AND (AND P R) Q ⇒ AND P Q
strenghtenAndLeft = impliesAndLeft strenghten

strenghtenAndRight : AND P (AND Q R) ⇒ AND P Q
strenghtenAndRight = impliesAndRight strenghten

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

allImplies : {A : Set} → {f g : A → Set} → {l : List A} → ({a : A} → f a → g a) → All f l → All g l
allImplies fa→ga [] = []
allImplies fa→ga (fl ∷ fls) = (fa→ga fl) ∷ (allImplies fa→ga fls)

anyImplies : {A : Set} → {f g : A → Set} → {l : List A} → ({a : A} → f a → g a) → Any f l → Any g l
anyImplies fa→ga (here hl) = here (fa→ga hl)
anyImplies fa→ga (there tl) = there (anyImplies fa→ga tl)

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

impliesPCWP : P ⇒ Q → PCWP (S , P) ⇛ PCWP (S , Q)
impliesPCWP p⇒q [] = []
impliesPCWP p⇒q (ci_prf ∷ cis_prfs) = p⇒q ci_prf ∷ impliesPCWP p⇒q cis_prfs

lessImpliesPCWP : (⟦ P ⟧a ⇛ (PCWP ((ci ∷ cis) , Q))) → (⟦ P ⟧a ⇛ (PCWP (cis , Q)))
lessImpliesPCWP p⇛pcwp = λ p → lessPCWP (p⇛pcwp p)

--

Unless : ParallelProgram → Predicate → Predicate → Statement
Unless S P Q = ⟦ (AND P (NOT Q)) ⟧a ⇛ (PCWP (S , OR P Q))

infix 4 _▷[_]_
_▷[_]_ : Predicate → ParallelProgram → Predicate → Statement
_▷[_]_ P S Q = Unless S P Q

weakenUnlessRight : (P ▷[ S ] Q) → (P ▷[ S ] (OR Q R))
weakenUnlessRight {P} {Q = Q} p∧¬q⇛pcwp (p , ¬_q∨r_) =
  impliesPCWP weakenOrRight (p∧¬q⇛pcwp (p , (¬_q∨r_ ∘ inj₁)))
  -- λ { (p , ¬_q∨r_) → impliesPCWP {OR P Q} weakenOrRight (p∧¬q⇛pcwp (p , (λ q → ¬_q∨r_ (inj₁ q)) }

unlessDisjunctive : ((P ▷[ S ] R) × (Q ▷[ S ] R)) → (P ▽ Q ▷[ S ] R)
unlessDisjunctive (P▷[S]R , Q▷[S]R) (inj₁ p , ⌝r) = impliesPCWP (impliesOrLeft weaken) (P▷[S]R (p , ⌝r))
unlessDisjunctive (P▷[S]R , Q▷[S]R) (inj₂ q , ⌝r) = impliesPCWP (impliesOrLeft (orCommutative ∘ weaken)) (Q▷[S]R (q , ⌝r))

lessUnless : (P ▷[ ci ∷ cis ] Q) → (P ▷[ cis ] Q)
lessUnless p▷[ci∷cis]q = λ p△⌝q → lessPCWP (p▷[ci∷cis]q p△⌝q)

--

Progress : ParallelProgram → Predicate → Predicate → Statement
Progress S P Q = (Any (λ ci → ⟦ P △ ⌝ Q ⟧a ⇛ (CWP (ci , Q))) S)

infix 4 _↣[_]_
_↣[_]_ : Predicate → ParallelProgram → Predicate → Statement
_↣[_]_ P S Q = Progress S P Q

--

Ensures : ParallelProgram → Predicate → Predicate → Statement
Ensures S P Q = (Unless S P Q × Progress S P Q)

infix 4 _↦[_]_
_↦[_]_ : Predicate → ParallelProgram → Predicate → Statement
_↦[_]_ P S Q = Ensures S P Q

-- tmp' : (P ▽ Q) △ ⌝ R ⇒ (P △ ⌝ R) ▽ (Q △ ⌝ R)
-- tmp' (inj₁ p , ⌝r) = inj₁ (p , ⌝r)
-- tmp' (inj₂ q , ⌝r) = inj₂ (q , ⌝r)
--
-- tmp : (⟦ P △ ⌝ R ⟧a ⇛ CWP (ci , R) × ⟦ Q △ ⌝ R ⟧a ⇛ CWP (ci , R)) → ⟦ (P ▽ Q) △ ⌝ R ⟧a ⇛ CWP (ci , R)
-- tmp (x , y) = ⇛Disjunctive tmp' (x , y)

-- THIS IS FALSE!
-- ensuresDisjunctive : ((P ↦[ S ] R) × (Q ↦[ S ] R)) → (P ▽ Q ↦[ S ] R)
-- ensuresDisjunctive ((P▷[S]R , existsP) , (Q▷[S]R , existsQ)) =
--   (unlessDisjunctive (P▷[S]R , Q▷[S]R) , {!   !})

-- -- ensuresDisjunctive : (P ↦[ S ] R) ⊎ (P ↦[ S ] R) → (P ▽ Q ↦[ S ] R)
-- -- ensuresDisjunctive (inj₁ (P▷[S]R , exists)) = ({!   !} , anyImplies {!   !} exists)
-- -- ensuresDisjunctive (inj₂ (Q▷[S]R , exists)) = ({!   !} , {!   !})
--
data LeadsTo : ParallelProgram → Predicate → Predicate → Statement where
  FromEnsures : Ensures S P Q → LeadsTo S P Q
  Transitivity : (LeadsTo S P Q × LeadsTo S Q R) → LeadsTo S P R
  Disjunctivity : ((LeadsTo S P R) × (LeadsTo S Q R)) → LeadsTo S (OR P Q) R

infix 4 _↪[_]_
_↪[_]_ : Predicate → ParallelProgram → Predicate → Statement
_↪[_]_ P S Q = LeadsTo S P Q

Invariant : ParallelProgram -> Predicate -> Statement
Invariant S P = ⟦ P ⟧a ⇛ (PCWP (S , P))

infix 4 _∈inv[_]
_∈inv[_] : Predicate → ParallelProgram → Statement
P ∈inv[ S ] = Invariant S P

-- init
-- FP
-- TERM

-- PSP

-- TRY 1:

-- pspFromEnsures₁ : P ▷[ S ] Q → R ▷[ S ] B → (P △ R) ▷[ S ] (Q △ R ▽ B)
-- pspFromEnsures₁ p▷[s]q r▷[s]b ((p , r) , ⌝_q△r▽b_) with (notOrToAndNotNot ⌝_q△r▽b_)
-- pspFromEnsures₁ p▷[s]q r▷[s]b ((p , r) , ⌝_q△r▽b_) | ⌝_q△r_ , ⌝b with (r▷[s]b (r , ⌝b))
-- pspFromEnsures₁ p▷[s]q r▷[s]b ((p , r) , ⌝_q△r▽b_) | ⌝_q△r_ , ⌝b | [] = []
-- --
-- pspFromEnsures₁ p▷[s]q r▷[s]b _p△r_△⌝_q△r▽b_@((p , r) , ⌝_q△r▽b_) | ⌝_q△r_ , ⌝b | inj₁ r_ ∷ rest with (p▷[s]q {!   !})
-- ... | inj₁ p_ ∷ rest' = inj₁ (p_ , r_) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_
-- ... | inj₂ q_ ∷ rest' = inj₂ (inj₁ (q_ , r_)) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_
-- --
-- pspFromEnsures₁ p▷[s]q r▷[s]b _p△r_△⌝_q△r▽b_@((p , r) , ⌝_q△r▽b_) | ⌝_q△r_ , ⌝b | inj₂ b_ ∷ rest =
--   inj₂ (inj₂ b_) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_

-- TRY 2:

-- pspFromEnsures₁ : P ▷[ S ] Q → R ▷[ S ] B → (P △ R) ▷[ S ] (Q △ R ▽ B)
-- pspFromEnsures₁ {Q = Q} p▷[s]q r▷[s]b {st = st} _p△r_△⌝_q△r▽b_@((p , r) , ⌝_q△r▽b_)
--   with (notOrToAndNotNot ⌝_q△r▽b_)
-- ... | ⌝_q△r_ , ⌝b with (r▷[s]b (r , ⌝b))
-- ...   | [] = []
-- ...   | inj₁ r_ ∷ rest with assertionDecidability {Q} {st}
-- ...     | inj₁ ⌝q with (p▷[s]q (p , ⌝q))
-- ...       | inj₁ p_ ∷ rest' = inj₁ (p_ , r_) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_
-- ...       | inj₂ q_ ∷ rest' = inj₂ (inj₁ (q_ , r_)) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_
-- pspFromEnsures₁ {Q = Q} p▷[s]q r▷[s]b {st} _p△r_△⌝_q△r▽b_@((p , r) , ⌝_q△r▽b_) | ⌝_q△r_ , ⌝b | inj₁ r_ ∷ rest -- ...
--         | inj₂ q = inj₂ (inj₁ ({!   !} , r_)) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_
-- pspFromEnsures₁ p▷[s]q r▷[s]b _p△r_△⌝_q△r▽b_@((p , r) , ⌝_q△r▽b_) | ⌝_q△r_ , ⌝b -- ...
--       | inj₂ b_ ∷ rest = inj₂ (inj₂ b_) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_

--TRY 3:

pspFromEnsures₁ : P ▷[ S ] Q → R ▷[ S ] B → (P △ R) ▷[ S ] (Q △ R ▽ B)
pspFromEnsures₁ p▷[s]q r▷[s]b _p△r_△⌝_q△r▽b_@((p , r) , ⌝_q△r▽b_) with (notOrToAndNotNot ⌝_q△r▽b_)
... | ⌝_q△r_ , ⌝b with (r▷[s]b (r , ⌝b))
...   | [] = []
...   | inj₁ r_ ∷ rest with (p▷[s]q (p , λ q → ⌝_q△r_ (q , r)))
...     | inj₁ p_ ∷ rest' = inj₁ (p_ , r_) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_
...     | inj₂ q_ ∷ rest' = inj₂ (inj₁ (q_ , r_)) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_
pspFromEnsures₁ p▷[s]q r▷[s]b _p△r_△⌝_q△r▽b_@((p , r) , ⌝_q△r▽b_) | ⌝_q△r_ , ⌝b -- ...
      | inj₂ b_ ∷ rest = inj₂ (inj₂ b_) ∷ pspFromEnsures₁ (lessUnless p▷[s]q) (lessUnless r▷[s]b) _p△r_△⌝_q△r▽b_

pspFromEnsures₂ : P ▷[ S ] Q → R ▷[ S ] B → P ↣[ S ] Q → Progress S (P △ R) (Q △ R ▽ B)
-- pspFromEnsures₂ p▷[s]q r▷[s]b (here p△⌝q⇛cwp) = here ( λ { ((p , r) , ⌝_q△r▽b_) → {!   !} } )
pspFromEnsures₂ {P} {S = ci ∷ cis} {Q} {R} {B} p▷[s]q r▷[s]b (here p△⌝q⇛cwp) = here f
  where
    f : ⟦ (P △ R) △ (⌝ (Q △ R ▽ B)) ⟧a ⇛ CWP (ci , Q △ R ▽ B)
    f ((p , r) , ⌝_q△r▽b_) with (notOrToAndNotNot ⌝_q△r▽b_)
    ... | ⌝_q△r_ , ⌝b with (r▷[s]b (r , ⌝b))
    ...   | inj₁ r_ ∷ rest with (p▷[s]q (p , λ q → ⌝_q△r_ (q , r)))
    -- ...     | inj₁ p_ ∷ rest' = inj₁ (? , r_)
    -- ...     | inj₁ p_ ∷ rest' = inj₁ ((p△⌝q⇛cwp (p , (λ x → ⌝_q△r▽b_ (inj₁ (x , r))))) , r_)
    ...     | inj₁ p_ ∷ rest' = inj₁ (p△⌝q⇛cwp (p , (λ q → ⌝_q△r_ (q , r))) , r_)
    ...     | inj₂ q_ ∷ rest' = inj₁ (q_ , r_)
    f ((p , r) , ⌝_q△r▽b_) | ⌝_q△r_ , ⌝b -- ...
          | inj₂ b_ ∷ rest = inj₂ b_
pspFromEnsures₂ p▷[s]q r▷[s]b (there rest) = there (pspFromEnsures₂ (lessUnless p▷[s]q) (lessUnless r▷[s]b) rest)

pspFromEnsures : P ↦[ S ] Q → R ▷[ S ] B → (P △ R) ↦[ S ] (Q △ R ▽ B)
pspFromEnsures (P▷[S]Q , P↣[S]Q) R▷[S]B = (pspFromEnsures₁ P▷[S]Q R▷[S]B , pspFromEnsures₂ P▷[S]Q R▷[S]B P↣[S]Q)

PSP : ((P ↪[ S ] Q) × (R ▷[ S ] B)) → (P △ R) ↪[ S ] ((Q △ R) ▽ B)
-- PSP (P↪[S]Q , R▷[S]B) = {!   !}
PSP (FromEnsures ensures , R▷[S]B) = FromEnsures (pspFromEnsures ensures R▷[S]B)
PSP (Transitivity (P↪[S]Q₁ , Q₁↪[S]Q) , R▷[S]B) = {!   !}
-- PSP (Disjunctivity (inj₁ P↪[S]Q₁) , R▷[S]B) = {!   !}
-- PSP (Disjunctivity (inj₂ Q↪[S]Q₁) , R▷[S]B) = {!   !}
PSP (Disjunctivity (P↪[S]Q₁ , Q↪[S]Q₁) , R▷[S]B) = {!   !}
