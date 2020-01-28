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

data Types : Set where
  Nat : Types
  ListNat : Types

evaluateType : Types → Set
evaluateType Nat = ℕ
evaluateType ListNat = List ℕ

defaultValue : (t : Types) → (evaluateType t)
defaultValue Nat = zero
defaultValue ListNat = []

Vars : Set
Vars = ℕ

module Program (VarTypes : ℕ → Types) where

  State : Set
  State = (i : Vars) → evaluateType (VarTypes i)

  emptyState : State
  emptyState = λ x → (defaultValue (VarTypes x))

  -- Expression, evaluate

  data Expression : Types → Set where
    ConstNat : ℕ → Expression Nat
    ConstListNat : List ℕ → Expression ListNat
    GetListNat : ℕ → List ℕ → Expression Nat
    SetListNat : ℕ → ℕ → List ℕ → Expression ListNat
    Var : (x : Vars) → Expression (VarTypes x)
    Plus : Expression Nat → Expression Nat → Expression Nat

  ⟦_⟧e : {t : Types} → Expression t → State → evaluateType t
  ⟦ ConstNat n ⟧e state = n
  ⟦ ConstListNat ln ⟧e state = ln

  ⟦ GetListNat i [] ⟧e state = 0
  ⟦ GetListNat zero (x ∷ ln) ⟧e state = x
  ⟦ GetListNat (suc i) (x ∷ ln) ⟧e state = ⟦ GetListNat i ln ⟧e state

  ⟦ SetListNat i n [] ⟧e state = []
  ⟦ SetListNat zero n (x ∷ ln) ⟧e state = n ∷ ln
  ⟦ SetListNat (suc i) n (x ∷ ln) ⟧e state = x ∷ ⟦ SetListNat i n ln ⟧e state

  ⟦ Var x ⟧e state = state x
  ⟦ Plus e e₁ ⟧e state = ⟦ e ⟧e state + ⟦ e₁ ⟧e state

  -- Instruction, execute

  VarValue : Set
  VarValue = Σ Vars (λ x → Expression (VarTypes x))

  data Instruction : Set where
    SKIP : Instruction
    Assignment : List VarValue → Instruction

  assign : List VarValue → State → State → State
  assign [] st₀ st = st
  assign ((var , value) ∷ rest) st₀ st =
    assign rest st₀ newState
      where
        newState : State
        newState x with (x Data.Nat.≟ var)
        -- newState x | yes refl = ⟦ value ⟧e st₀
        newState x | yes p rewrite p = ⟦ value ⟧e st₀
        newState x | no ¬p = st x

  ⟦_⟧i : Instruction → State → State
  ⟦ SKIP ⟧i st = st
  ⟦ Assignment varExpressionPairs ⟧i st = assign varExpressionPairs st st

  data Predicate : Set where
    TRUE : Predicate
    FALSE : Predicate
    NOT : Predicate → Predicate
    AND : Predicate → Predicate → Predicate
    OR : Predicate → Predicate → Predicate

    LTE : Expression Nat → Expression Nat → Predicate
    GTE : Expression Nat → Expression Nat → Predicate
    LT : Expression Nat → Expression Nat → Predicate
    GT : Expression Nat → Expression Nat → Predicate

  -- ⌝_ : Predicate → Predicate
  -- ⌝_ = NOT
  --
  -- infixr 6 _△_
  -- _△_ : Predicate → Predicate → Predicate
  -- _△_ = AND
  --
  -- infixr 5 _▽_
  -- _▽_ : Predicate → Predicate → Predicate
  -- _▽_ = OR

  ConditionalInstruction : Set
  ConditionalInstruction = (Predicate × Instruction)

  ParallelProgram : Set
  ParallelProgram = (ConditionalInstruction × List ConditionalInstruction)

  NonEmpty : ParallelProgram → Set
  NonEmpty (s0 , cis) = ¬ (cis ≡ [])

  Assertion : Set₁
  Assertion = State → Set

  ⟦_⟧a : Predicate → Assertion
  ⟦ TRUE ⟧a state = ⊤
  ⟦ FALSE ⟧a state = ⊥
  ⟦ NOT p ⟧a state = ¬ (⟦ p ⟧a state)
  ⟦ AND p p₁ ⟧a state = ((⟦ p ⟧a state) × (⟦ p₁ ⟧a state))
  ⟦ OR p p₁ ⟧a state = ((⟦ p ⟧a state) ⊎ (⟦ p₁ ⟧a state))

  ⟦ LTE e e₁ ⟧a state = ((⟦ e ⟧e state) Data.Nat.≤ (⟦ e₁ ⟧e state))
  ⟦ GTE e e₁ ⟧a state = ((⟦ e ⟧e state) Data.Nat.≥ (⟦ e₁ ⟧e state))
  ⟦ LT e e₁ ⟧a state = ((⟦ e ⟧e state) Data.Nat.< (⟦ e₁ ⟧e state))
  ⟦ GT e e₁ ⟧a state = ((⟦ e ⟧e state) Data.Nat.> (⟦ e₁ ⟧e state))

  Condition : Set
  Condition = State → Bool

  ⟦_⟧c : Predicate → Condition
  ⟦ TRUE ⟧c = const true
  ⟦ FALSE ⟧c = const false
  ⟦ NOT p ⟧c state = not (⟦ p ⟧c state)
  ⟦ AND p p₁ ⟧c state = (⟦ p ⟧c state) ∧ (⟦ p₁ ⟧c state)
  ⟦ OR p p₁ ⟧c state = (⟦ p ⟧c state) ∨ (⟦ p₁ ⟧c state)

  ⟦ LTE e e₁ ⟧c state = ⌊ ((⟦ e ⟧e state) Data.Nat.≤? (⟦ e₁ ⟧e state)) ⌋
  ⟦ GTE e e₁ ⟧c state = ⌊ ((⟦ e ⟧e state) Data.Nat.≥? (⟦ e₁ ⟧e state)) ⌋
  ⟦ LT e e₁ ⟧c state = ⌊ ((⟦ e ⟧e state) Data.Nat.<? (⟦ e₁ ⟧e state)) ⌋
  ⟦ GT e e₁ ⟧c state = ⌊ ((⟦ e ⟧e state) Data.Nat.>? (⟦ e₁ ⟧e state)) ⌋
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

  assertionToCondition {LTE e e₁} {st} ee≤e₁e with (⟦ e ⟧e st Data.Nat.≤? ⟦ e₁ ⟧e st)
  assertionToCondition {LTE e e₁} {st} ee≤e₁e | yes p = tt
  assertionToCondition {LTE e e₁} {st} ee≤e₁e | no ¬p = ¬p ee≤e₁e

  assertionToCondition {GTE e e₁} {st} ee≥e₁e with (⟦ e ⟧e st Data.Nat.≥? ⟦ e₁ ⟧e st)
  assertionToCondition {GTE e e₁} {st} ee≥e₁e | yes p = tt
  assertionToCondition {GTE e e₁} {st} ee≥e₁e | no ¬p = ¬p ee≥e₁e

  assertionToCondition {LT e e₁} {st} ee<e₁e with (⟦ e ⟧e st Data.Nat.<? ⟦ e₁ ⟧e st)
  assertionToCondition {LT e e₁} {st} ee<e₁e | yes p = tt
  assertionToCondition {LT e e₁} {st} ee<e₁e | no ¬p = ¬p ee<e₁e

  assertionToCondition {GT e e₁} {st} ee>e₁e with (⟦ e ⟧e st Data.Nat.>? ⟦ e₁ ⟧e st)
  assertionToCondition {GT e e₁} {st} ee>e₁e | yes p = tt
  assertionToCondition {GT e e₁} {st} ee>e₁e | no ¬p = ¬p ee>e₁e


  conditionToAssertion {TRUE} {st} tt = tt
  conditionToAssertion {FALSE} {st} ()
  conditionToAssertion {NOT p} {st} T_not_pc_st ps_st = (CTS_NOT T_not_pc_st) (assertionToCondition ps_st)
  conditionToAssertion {AND p p₁} {st} pc_st∧p₁c_st with (CTS_AND {⟦ p ⟧c st} pc_st∧p₁c_st)
  conditionToAssertion {AND p p₁} {st} pc_st∧p₁c_st | (T_pc_st , T_p₁c_st) =
    (conditionToAssertion T_pc_st , conditionToAssertion T_p₁c_st)
  conditionToAssertion {OR p p₁} {st} pc_st∧p₁c_st with (CTS_OR {⟦ p ⟧c st} pc_st∧p₁c_st)
  conditionToAssertion {OR p p₁} {st} pc_st∧p₁c_st | inj₁ T_pc_st = inj₁ (conditionToAssertion T_pc_st)
  conditionToAssertion {OR p p₁} {st} pc_st∧p₁c_st | inj₂ T_p₁c_st = inj₂ (conditionToAssertion T_p₁c_st)

  conditionToAssertion {LTE e e₁} {st} ee≤e₁e with (⟦ e ⟧e st Data.Nat.≤? ⟦ e₁ ⟧e st)
  conditionToAssertion {LTE e e₁} {st} ee≤e₁e | yes p = p

  conditionToAssertion {GTE e e₁} {st} ee≥e₁e with (⟦ e ⟧e st Data.Nat.≥? ⟦ e₁ ⟧e st)
  conditionToAssertion {GTE e e₁} {st} ee≥e₁e | yes p = p

  conditionToAssertion {LT e e₁} {st} ee<e₁e with (⟦ e ⟧e st Data.Nat.<? ⟦ e₁ ⟧e st)
  conditionToAssertion {LT e e₁} {st} ee<e₁e | yes p = p

  conditionToAssertion {GT e e₁} {st} ee>e₁e with (⟦ e ⟧e st Data.Nat.>? ⟦ e₁ ⟧e st)
  conditionToAssertion {GT e e₁} {st} ee>e₁e | yes p = p

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

  _⊢_ : State → Predicate → Set
  st ⊢ p = ⟦ p ⟧a st

  _⊩_ : State → Assertion → Set
  st ⊩ a = a st

  _⊪_ : State → Predicate → Set
  st ⊪ p = T (⟦ p ⟧c st)

  _⊨_ : State → Predicate → Bool
  st ⊨ p = ⟦ p ⟧c st

  _⊫_ : State → Condition → Bool
  st ⊫ c = c st

-- module NatOnly = Program (λ n → Nat)
