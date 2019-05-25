module Simple where

-- Imports

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as Eq
open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
-- open import Data.List.All
-- open import Data.List.Any
open import Function
-- open import Data.String

-- Vars, Values, State, emptyState

Vars : Set
Vars = ℕ

Values : Set
Values = ℕ

State : Set
State = Vars → Values

emptyState : State
emptyState = λ x → 0

-- Expression, evaluate

data Expression : Set where
  Const : ℕ -> Expression
  Var : Vars -> Expression
  Plus : Expression -> Expression -> Expression

⟦_⟧e : Expression -> State → ℕ
⟦ Const v ⟧e state = v
⟦ Var x ⟧e state = state x
⟦ Plus e e₁ ⟧e state = ⟦ e ⟧e state + ⟦ e₁ ⟧e state

-- Instruction, execute

data Instruction : Set where
  SKIP : Instruction
  Assignment : Vars → Expression → Instruction

⟦_⟧i : Instruction → State → State
⟦ SKIP ⟧i st = st
⟦ Assignment var value ⟧i st =
  λ x → if ⌊ x Data.Nat.≟ var ⌋ then ⟦ value ⟧e st else st x

data Predicate : Set where
  TRUE : Predicate
  FALSE : Predicate
  NOT : Predicate -> Predicate
  AND : Predicate -> Predicate -> Predicate
  OR : Predicate -> Predicate -> Predicate

⌝_ : Predicate → Predicate
⌝_ = NOT

infixr 6 _△_
_△_ : Predicate → Predicate → Predicate
_△_ = AND

infixr 5 _▽_
_▽_ : Predicate → Predicate → Predicate
_▽_ = OR

ConditionalInstruction : Set
ConditionalInstruction = (Predicate × Instruction)

ParallelProgram : Set
ParallelProgram = List ConditionalInstruction

Assertion : Set₁
Assertion = State → Set

⟦_⟧a : Predicate -> Assertion
⟦ TRUE ⟧a state = ⊤
⟦ FALSE ⟧a state = ⊥
⟦ NOT p ⟧a state = ¬ (⟦ p ⟧a state)
⟦ AND p p₁ ⟧a state = ((⟦ p ⟧a state) × (⟦ p₁ ⟧a state))
⟦ OR p p₁ ⟧a state = ((⟦ p ⟧a state) ⊎ (⟦ p₁ ⟧a state))

Condition : Set
Condition = State → Bool

⟦_⟧c : Predicate → Condition
⟦ TRUE ⟧c = const true
⟦ FALSE ⟧c = const false
⟦ NOT p ⟧c state = not (⟦ p ⟧c state)
⟦ AND p p₁ ⟧c state = (⟦ p ⟧c state) ∧ (⟦ p₁ ⟧c state)
⟦ OR p p₁ ⟧c state = (⟦ p ⟧c state) ∨ (⟦ p₁ ⟧c state)

--

STC_AND : {a b : Bool} → T a × T b → T (a ∧ b)
STC_AND {false} = proj₁
STC_AND {true} = proj₂

STC_OR : {a b : Bool} → T a ⊎ T b → T (a ∨ b)
STC_OR {false} {false} (inj₁ ())
STC_OR {false} {false} (inj₂ ())
STC_OR {false} {true} = const tt
STC_OR {true} = const tt

STC_NOT : {a : Bool} → ¬ (T a) → T (not a)
STC_NOT {false} = const tt
STC_NOT {true} ¬tt = ¬tt tt

CTS_AND : {a b : Bool} → T (a ∧ b) → T a × T b
CTS_AND {false} ()
CTS_AND {true} {false} ()
CTS_AND {true} {true} tt = (tt , tt)

CTS_OR : {a b : Bool} → T (a ∨ b) → T a ⊎ T b
CTS_OR {false} {false} ()
CTS_OR {false} {true} tt = inj₂ tt
CTS_OR {true} tt = inj₁ tt

CTS_NOT : {a : Bool} → T (not a) → ¬ (T a)
CTS_NOT {false} = const id
CTS_NOT {true} ()

assertionToCondition : {p : Predicate} → {st : State} → ⟦ p ⟧a st → T (⟦ p ⟧c st)
conditionToAssertion : {p : Predicate} → {st : State} → T (⟦ p ⟧c st) → ⟦ p ⟧a st

assertionToCondition {TRUE} ps_st = tt
assertionToCondition {FALSE} ()
assertionToCondition {NOT p} {st} ¬ps_st = STC_NOT (λ T_p₁c_st → ¬ps_st (conditionToAssertion T_p₁c_st))
assertionToCondition {AND p p₁} (ps_st , p₁s_st) =
  STC_AND (assertionToCondition {p} ps_st , assertionToCondition {p₁} p₁s_st)
assertionToCondition {OR p p₁} (inj₁ ps_st) = STC_OR (inj₁ (assertionToCondition ps_st))
assertionToCondition {OR p p₁} (inj₂ p₁s_st) = STC_OR (inj₂ (assertionToCondition p₁s_st))

conditionToAssertion {TRUE} {st} tt = tt
conditionToAssertion {FALSE} {st} ()
conditionToAssertion {NOT p} {st} T_not_pc_st ps_st = (CTS_NOT T_not_pc_st) (assertionToCondition ps_st)
conditionToAssertion {AND p p₁} {st} pc_st∧p₁c_st with (CTS_AND {⟦ p ⟧c st} pc_st∧p₁c_st)
conditionToAssertion {AND p p₁} {st} pc_st∧p₁c_st | (T_pc_st , T_p₁c_st) =
  (conditionToAssertion T_pc_st , conditionToAssertion T_p₁c_st)
conditionToAssertion {OR p p₁} {st} pc_st∧p₁c_st with (CTS_OR {⟦ p ⟧c st} pc_st∧p₁c_st)
conditionToAssertion {OR p p₁} {st} pc_st∧p₁c_st | inj₁ T_pc_st = inj₁ (conditionToAssertion T_pc_st)
conditionToAssertion {OR p p₁} {st} pc_st∧p₁c_st | inj₂ T_p₁c_st = inj₂ (conditionToAssertion T_p₁c_st)

conditionDecidability : {p : Predicate} → {st : State} → T (not (⟦ p ⟧c st) ∨ ⟦ p ⟧c st)
conditionDecidability {p} {st} with (⟦ p ⟧c st)
conditionDecidability {p} {st} | false = tt
conditionDecidability {p} {st} | true = tt

assertionDecidability : {p : Predicate} → {st : State} → ((¬ ⟦ p ⟧a st) ⊎ (⟦ p ⟧a st))
assertionDecidability {p} {st} = conditionToAssertion (conditionDecidability {p})

--

⟦_⟧ci : ConditionalInstruction → State → State
⟦ (p , i) ⟧ci st with ⟦ p ⟧c st
... | false = st
... | true = ⟦ i ⟧i st

--

_⊢_ : State -> Predicate -> Set
st ⊢ p = ⟦ p ⟧a st

_⊩_ : State -> Assertion -> Set
st ⊩ a = a st

_⊪_ : State → Predicate → Set
st ⊪ p = T (⟦ p ⟧c st)

_⊨_ : State → Predicate → Bool
st ⊨ p = ⟦ p ⟧c st

_⊫_ : State → Condition → Bool
st ⊫ c = c st
