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
    GetListNat : Expression Nat → Expression ListNat → Expression Nat
    SetListNat : Expression Nat → Expression Nat → Expression ListNat → Expression ListNat
    Var : (x : Vars) → Expression (VarTypes x)
    Plus : Expression Nat → Expression Nat → Expression Nat

  infix 3 v[_]
  v[_] : (x : Vars) → Expression (VarTypes x)
  v[ x ] = Var x

  infix 3 _g[_]
  _g[_] : Expression ListNat → Expression Nat → Expression Nat
  eln g[ ei ] = GetListNat ei eln

  infixl 3 _s[_]=_
  _s[_]=_ : Expression ListNat → Expression Nat → Expression Nat → Expression ListNat
  eln s[ ei ]= em = SetListNat ei em eln

  getWithDefaultZero : ℕ → List ℕ → ℕ
  getWithDefaultZero i [] = 0
  getWithDefaultZero zero (n ∷ ln) = n
  getWithDefaultZero (suc i) (n ∷ ln) = getWithDefaultZero i ln

  setWithDefaultEmpty : ℕ → ℕ → List ℕ → List ℕ
  setWithDefaultEmpty i m [] = []
  setWithDefaultEmpty zero m (n ∷ ln) = m ∷ ln
  setWithDefaultEmpty (suc i) m (n ∷ ln) = n ∷ setWithDefaultEmpty i m ln

  ⟦_⟧e : {t : Types} → Expression t → State → evaluateType t
  ⟦ ConstNat n ⟧e state = n
  ⟦ ConstListNat ln ⟧e state = ln

  ⟦ GetListNat ei eln ⟧e state with ⟦ ei ⟧e state | ⟦ eln ⟧e state
  ... | i | ln = getWithDefaultZero i ln
  -- ⟦ GetListNat i eln ⟧e state | j | [] = 0
  -- ⟦ GetListNat i eln ⟧e state | zero | n ∷ ln = n
  -- ⟦ GetListNat i eln ⟧e state | suc j | n ∷ ln = ⟦ GetListNat (ConstNat j) (ConstListNat ln) ⟧e state

  ⟦ SetListNat ei em eln ⟧e state with ⟦ ei ⟧e state | ⟦ em ⟧e state | ⟦ eln ⟧e state
  ... | i | m | ln = setWithDefaultEmpty i m ln
  -- ⟦ SetListNat zero n (x ∷ ln) ⟧e state = n ∷ ln
  -- ⟦ SetListNat (suc i) n (x ∷ ln) ⟧e state = x ∷ ⟦ SetListNat i n ln ⟧e state

  ⟦ Var x ⟧e state = state x
  ⟦ Plus e e₁ ⟧e state = ⟦ e ⟧e state + ⟦ e₁ ⟧e state

  -- Instruction, execute

  VarValue : Set
  VarValue = Σ Vars (λ x → Expression (VarTypes x))

  data Instruction : Set where
    SKIP : Instruction
    Assignment : List VarValue → Instruction

  -- makeNewState : State → (x y : Var) → Dec (x ≡ y) → State
  makeNewState :
    State → State → (x : Vars) → (Expression (VarTypes x)) → State
  makeNewState st₀ st var value x with (x Data.Nat.≟ var)
  -- makeNewState st₀ var value x | yes refl = ⟦ value ⟧e st₀
  makeNewState st₀ st var value x | yes p rewrite p = ⟦ value ⟧e st₀
  makeNewState st₀ st var value x | no ¬p = st x

  assign : List VarValue → State → State → State
  assign [] st₀ st = st
  assign ((var , value) ∷ rest) st₀ st =
    assign rest st₀ (makeNewState st₀ st var value)

  -- assign : List VarValue → State → State → State
  -- assign [] st₀ st = st
  -- assign ((var , value) ∷ rest) st₀ st =
  --   assign rest st₀ newState
  --     where
  --       newState : State
  --       newState x with (x Data.Nat.≟ var)
  --       -- newState x | yes refl = ⟦ value ⟧e st₀
  --       newState x | yes p rewrite p = ⟦ value ⟧e st₀
  --       newState x | no ¬p = st x

  ⟦_⟧i : Instruction → State → State
  ⟦ SKIP ⟧i st = st
  ⟦ Assignment varExpressionPairs ⟧i st = assign varExpressionPairs st st

  data Predicate : Set where
    TRUE : Predicate
    FALSE : Predicate
    NOT : Predicate → Predicate
    AND : Predicate → Predicate → Predicate
    OR : Predicate → Predicate → Predicate

    EQ : Expression Nat → Expression Nat → Predicate

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

  ⟦ EQ e e₁ ⟧a state = ((⟦ e ⟧e state) ≡ (⟦ e₁ ⟧e state))

  ⟦ LTE e e₁ ⟧a state = ((⟦ e ⟧e state) Data.Nat.≤ (⟦ e₁ ⟧e state))
  ⟦ GTE e e₁ ⟧a state = ((⟦ e ⟧e state) Data.Nat.≥ (⟦ e₁ ⟧e state))
  ⟦ LT e e₁ ⟧a state = ((⟦ e ⟧e state) Data.Nat.< (⟦ e₁ ⟧e state))
  ⟦ GT e e₁ ⟧a state = ((⟦ e ⟧e state) Data.Nat.> (⟦ e₁ ⟧e state))

  Decision : Predicate → Set
  Decision p = (st : State) → Dec (⟦ p ⟧a st)

  decNot : {X : Set} → Dec X → Dec (¬ X)
  decNot (yes x) = no (λ ¬x → ¬x x)
  decNot (no ¬x) = yes ¬x

  decAnd : {X Y : Set} → Dec X → Dec Y → Dec (X × Y)
  decAnd (yes x) (yes y) = yes (x , y)
  decAnd (yes x) (no ¬y) = no (λ { (x , y) → ¬y y })
  decAnd (no ¬x) dy = no (λ { (x , y) → ¬x x })

  decOr : {X Y : Set} → Dec X → Dec Y → Dec (X ⊎ Y)
  decOr (yes x) dy = yes (inj₁ x)
  decOr (no ¬x) (yes y) = yes (inj₂ y)
  decOr (no ¬x) (no ¬y) = no λ { (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

  ⟦_⟧d : (p : Predicate) → Decision p
  ⟦ TRUE ⟧d = const (yes tt)
  ⟦ FALSE ⟧d = const (no (λ bot → bot))
  ⟦ NOT p ⟧d state = decNot (⟦ p ⟧d state)
  ⟦ AND p p₁ ⟧d state = decAnd (⟦ p ⟧d state) (⟦ p₁ ⟧d state)
  ⟦ OR p p₁ ⟧d state = decOr (⟦ p ⟧d state) (⟦ p₁ ⟧d state)

  ⟦ EQ e e₁ ⟧d state = ((⟦ e ⟧e state) Data.Nat.≟ (⟦ e₁ ⟧e state))

  ⟦ LTE e e₁ ⟧d state = ((⟦ e ⟧e state) Data.Nat.≤? (⟦ e₁ ⟧e state))
  ⟦ GTE e e₁ ⟧d state = ((⟦ e ⟧e state) Data.Nat.≥? (⟦ e₁ ⟧e state))
  ⟦ LT e e₁ ⟧d state = ((⟦ e ⟧e state) Data.Nat.<? (⟦ e₁ ⟧e state))
  ⟦ GT e e₁ ⟧d state = ((⟦ e ⟧e state) Data.Nat.>? (⟦ e₁ ⟧e state))

  Condition : Set
  Condition = State → Bool

  ⟦_⟧c : Predicate → Condition
  ⟦ p ⟧c st = ⌊ ⟦ p ⟧d st ⌋

  assertionDecidability : {P : Predicate} → {st : State} → ((¬ ⟦ P ⟧a st) ⊎ (⟦ P ⟧a st))
  assertionDecidability {P} {st} with (⟦ P ⟧d st)
  assertionDecidability {P} {st} | yes p = inj₂ p
  assertionDecidability {P} {st} | no ¬p = inj₁ ¬p

  -- decisionToAssertion :
  --   {P : Predicate} → {st : State} →
  --   ()

  --

  ⟦⟧ciHelper : Bool → Instruction → State → State
  ⟦⟧ciHelper false i st = st
  ⟦⟧ciHelper true i st = ⟦ i ⟧i st

  ⟦_⟧ci : ConditionalInstruction → State → State
  ⟦ (p , i) ⟧ci st = ⟦⟧ciHelper (⟦ p ⟧c st) i st
  -- ⟦ (p , i) ⟧ci st with ⟦ p ⟧c st
  -- ... | false = st
  -- ... | true = ⟦ i ⟧i st

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
