module ORSI.Simple where

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
⟦ Const v ⟧e st = v
⟦ Var x ⟧e st = st x
⟦ Plus e1 e2 ⟧e st = ⟦ e1 ⟧e st + ⟦ e2 ⟧e st

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

ConditionalInstruction : Set
ConditionalInstruction = (Predicate × Instruction)

ParallelProgram : Set
ParallelProgram = List ConditionalInstruction

Statementt : Set₁
Statementt = State → Set

⟦_⟧s : Predicate -> Statementt
⟦ TRUE ⟧s state = ⊤
⟦ FALSE ⟧s state = ⊥
⟦ NOT p ⟧s state = ¬(⟦ p ⟧s state)
⟦ AND p₁ p₂ ⟧s state = ((⟦ p₁ ⟧s state) × (⟦ p₂ ⟧s state))
⟦ OR  p₁ p₂ ⟧s state = ((⟦ p₁ ⟧s state) ⊎ (⟦ p₂ ⟧s state))

Condition : Set
Condition = State → Bool

⟦_⟧c : Predicate → Condition
⟦ TRUE ⟧c = const true
⟦ FALSE ⟧c = const false
⟦ NOT p ⟧c state = not (⟦ p ⟧c state)
⟦ AND p₁ p₂ ⟧c state = (⟦ p₁ ⟧c state) ∧ (⟦ p₂ ⟧c state)
⟦ OR p₁ p₂ ⟧c state = (⟦ p₁ ⟧c state) ∨ (⟦ p₂ ⟧c state)

T∧ : {a b : Bool} → T a × T b → T (a ∧ b)
T∧ {false} {false} = proj₁
T∧ {false} {true} = proj₁
T∧ {true} {false} = proj₂
T∧ {true} {true} = λ _ → tt

T∨ : {a b : Bool} → T a ⊎ T b → T (a ∨ b)
T∨ {false} {false} = [_,_] (λ ()) (λ ())
T∨ {false} {true} = λ _ → tt
T∨ {true} {false} = λ _ → tt
T∨ {true} {true} = λ _ → tt

T¬ : {a : Bool} → ¬ (T a) → T (not a)
T¬ {false} = λ _ → tt
T¬ {true} f = f tt

¬T : {a : Bool} → T (not a) → ¬ (T a)
¬T {false} = λ _ ()
¬T {true} = λ ()

-- a ⊂ b, a' ⊂ b', b→a' ⊂ a→b'
-- ℤ → B ⊂ ℕ → B
-- ¬ A = A → ⊥
-- λ X → (ℕ → X)
-- map : (f : A → B) → (ℕ → A) → (ℕ → B)

-- λ X → (X → ℕ)
-- map : (f : A → B) → (B → ℕ) → (A → ℕ)


statementToCondition : {p : Predicate} → {st : State} → ⟦ p ⟧s st → T (⟦ p ⟧c st)
conditionToStatement : {p : Predicate} → {st : State} → T (⟦ p ⟧c st) → ⟦ p ⟧s st

statementToCondition {TRUE} ps_st = tt
statementToCondition {FALSE} ()
statementToCondition {NOT p} {st} ps_st = T¬ λ w → ps_st (conditionToStatement w)
statementToCondition {AND p p₁} (ps_st , p₁s_st) = T∧ (statementToCondition {p} ps_st , statementToCondition {p₁} p₁s_st) 
statementToCondition {OR p p₁} (inj₁ x) = T∨ (inj₁ (statementToCondition x))
statementToCondition {OR p p₁} (inj₂ y) = T∨ (inj₂ (statementToCondition y))

conditionToStatement {TRUE} {st} pc_st = pc_st
conditionToStatement {FALSE} {st} pc_st = pc_st
conditionToStatement {NOT p} {st} pc_st with (⟦ p ⟧c st)
conditionToStatement {NOT p} {st} pc_st | false = {! conditionToStatement {p} {st}  !}
conditionToStatement {AND p p₁} {st} pc_st = {!   !}
conditionToStatement {OR p p₁} {st} pc_st = {!   !}

predicateDecidability : {p : Predicate} → {st : State} → ((¬ ⟦ p ⟧s st) ⊎ (⟦ p ⟧s st))
predicateDecidability {p} {st} with ⟦ p ⟧c st
  where
    sajt = statementToCondition {p} {st} 
predicateDecidability {p} {st} | false = inj₁ λ ps_st → {! statementToCondition {p} {st} !}
predicateDecidability {p} {st} | true = inj₂ {!!}

⟦_⟧ci : ConditionalInstruction → State → State
⟦ (p , i) ⟧ci st with ⟦ p ⟧c st
... | false = st
... | true = ⟦ i ⟧i st

-- _⋈_ : State → Predicate → Set
-- st ⋈ p = T (⟦ p ⟧c st)

_⋈_ : State -> Predicate -> Set
st ⋈ p = ⟦ p ⟧s st

_⊢_ : State → Predicate → Bool
st ⊢ p = ⟦ p ⟧c st

_⊨_ : State → Condition → Bool
st ⊨ c = c st

f g : Bool → Set
f x = if x then ℕ else ℕ
g x = if x then ℕ else ℕ

fg : f ≡ g
fg = refl

{-
if : (C : Bool → Set) → C true → C false → (b : Bool) → C b

if _ 2 4 t

λ _ → ℕ :: Bool → Set



-}
