module Base where

-- Imports

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_)
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

data Types : Set
evaluateType : Types → Set
defaultValue : (t : Types) → (evaluateType t)


-- Queue with history using two lists

-- QueueWithHistory : Types → Set
-- QueueWithHistory A = List (evaluateType A) × List (evaluateType A)

-- hiext : {A : Types} → (evaluateType A) → QueueWithHistory A → QueueWithHistory A
-- hiext a (l , h) = (l ++ [ a ] , h ++ [ a ])

-- lorem : {A : Types} → QueueWithHistory A → QueueWithHistory A
-- lorem ([] , h) = ([] , h)
-- lorem (l ∷ ls , h) = (ls , h)

-- lov : {A : Types} → QueueWithHistory A → (evaluateType A)
-- lov {A} ([] , h) = defaultValue A
-- lov (l ∷ ls , h) = l

-- history : {A : Types} → QueueWithHistory A → QueueWithHistory A
-- history (l , h) = (h , h)


-- Queue using a binary tree

data Queue (A : Types) : Set where
  Leaf : Queue A
  Node : (evaluateType A) → Queue A → Queue A → Queue A

enqueue : {A : Types} → (evaluateType A) → Queue A → Queue A
enqueue a Leaf = Node a Leaf Leaf
enqueue a (Node x l r) = Node x (enqueue a l) r

peek : {A : Types} → Queue A → (evaluateType A)
peek {A} Leaf = defaultValue A
peek (Node x l Leaf) = x
peek (Node x l r@(Node _ _ _)) = peek r

dequeue : {A : Types} → Queue A → Queue A
dequeue {A} Leaf = Leaf
dequeue (Node x l Leaf) = l
dequeue (Node x l r@(Node _ _ _)) = Node x l (dequeue r)

historyToQueue : {A : Types} → List (evaluateType A) → Queue A
historyToQueue [] = Leaf
historyToQueue (x ∷ l) = enqueue x (historyToQueue l)


-- Queue with history

QueueWithHistory : Types → Set
QueueWithHistory A = Queue A × List (evaluateType A)

hiext : {A : Types} → (evaluateType A) → QueueWithHistory A → QueueWithHistory A
hiext a (q , h) = enqueue a q , a ∷ h

lorem : {A : Types} → QueueWithHistory A → QueueWithHistory A
lorem (q , h) = (dequeue q , h)

lov : {A : Types} → QueueWithHistory A → (evaluateType A)
lov (q , h) = peek q

history : {A : Types} → QueueWithHistory A → QueueWithHistory A
history (q , h) = (historyToQueue h , h)

len : {A : Types} → Queue A → ℕ
len Leaf = 0
len (Node x l r) = suc ((len l) + (len r))


-- Types

data Types where
  Nat : Types
  Array : Types → Types
  DataChannel : Types → Types

evaluateType Nat = ℕ
evaluateType (Array A) = ℕ → (evaluateType A)
evaluateType (DataChannel A) = QueueWithHistory A

defaultValue Nat = zero
defaultValue (Array A) = const (defaultValue A)
defaultValue (DataChannel A) = (Leaf , [])


module Program (varCount : ℕ) (varTypes : Fin varCount → Types) where

  Vars : Set
  Vars = Fin varCount

  State : Set
  State = (i : Vars) → evaluateType (varTypes i)

  emptyState : State
  emptyState = λ x → (defaultValue (varTypes x))

  -- Expression, evaluate

  data Expression : Types → Set where
    Const : {A : Types} → evaluateType A → Expression A
    -- ConstList : {A : Types} → (evaluateType (Array A)) → Expression (Array A)
    GetArray : {A : Types} → Expression Nat → Expression (Array A) → Expression A
    SetArray : {A : Types} → Expression Nat → Expression A → Expression (Array A) → Expression (Array A)
    Var : (x : Vars) → Expression (varTypes x)
    Plus : Expression Nat → Expression Nat → Expression Nat
    Hiext : {A : Types} → Expression A → Expression (DataChannel A) → Expression (DataChannel A)
    Lov : {A : Types} → Expression (DataChannel A) → Expression A
    Lorem : {A : Types} → Expression (DataChannel A) → Expression (DataChannel A)
    History : {A : Types} → Expression (DataChannel A) → Expression (DataChannel A)

  infix 3 v[_]
  v[_] : (x : Vars) → Expression (varTypes x)
  v[ x ] = Var x

  infix 3 _g[_]
  _g[_] : {A : Types} → Expression (Array A) → Expression Nat → Expression A
  el g[ ei ] = GetArray ei el

  infixl 3 _s[_]=_
  _s[_]=_ : {A : Types} → Expression (Array A) → Expression Nat → Expression A → Expression (Array A)
  el s[ ei ]= ev = SetArray ei ev el

  listToFunction : List ℕ → ℕ → ℕ
  listToFunction [] i = 0
  listToFunction (n ∷ ln) zero = n
  listToFunction (n ∷ ln) (suc i) = listToFunction ln i

  functionToList : ℕ → (ℕ → ℕ) → List ℕ
  functionToList len f = applyUpTo f len
  -- functionToList len f = Data.List.map f (upTo len)

  listEquality :
    {A : Set} → {a b : A} → {as bs : List A} →
    (a ≡ b) → (as ≡ bs) → (a ∷ as ≡ b ∷ bs)
  listEquality refl refl = refl

  listToFunction∘functionToList-test :
    (ln : List ℕ) → functionToList (length ln) (listToFunction ln) ≡ ln
  listToFunction∘functionToList-test [] = refl
  listToFunction∘functionToList-test (n ∷ ns) =
    listEquality refl (listToFunction∘functionToList-test ns)

  -- getWithDefaultZero : ℕ → List ℕ → ℕ
  -- getWithDefaultZero i [] = 0
  -- getWithDefaultZero zero (n ∷ ln) = n
  -- getWithDefaultZero (suc i) (n ∷ ln) = getWithDefaultZero i ln

  setListItem : {A : Types} → ℕ → evaluateType A → (ℕ → (evaluateType A)) → (ℕ → (evaluateType A))
  -- setListItem i n f j = if ⌊ j Data.Nat.≟ i ⌋ then n else (f j)
  setListItem i v f j with j Data.Nat.≟ i
  setListItem i v f j | yes p = v
  setListItem i v f j | no ¬p = f j
  -- then n else (f j)

  -- setListItem : ℕ → ℕ → List ℕ → List ℕ
  -- setListItem i m [] = []
  -- setListItem zero m (n ∷ ln) = m ∷ ln
  -- setListItem (suc i) m (n ∷ ln) = n ∷ setListItem i m ln

  ⟦_⟧e : {t : Types} → Expression t → State → evaluateType t
  ⟦ Const value ⟧e state = value
  -- ⟦ ConstArray ln ⟧e state = ln

  ⟦ GetArray ei eln ⟧e state with ⟦ ei ⟧e state | ⟦ eln ⟧e state
  ... | i | ln = ln i
  -- ⟦ GetArray i eln ⟧e state | j | [] = 0
  -- ⟦ GetArray i eln ⟧e state | zero | n ∷ ln = n
  -- ⟦ GetArray i eln ⟧e state | suc j | n ∷ ln = ⟦ GetArray (ConstNat j) (ConstArray ln) ⟧e state

  ⟦ SetArray ei em eln ⟧e state with ⟦ ei ⟧e state | ⟦ em ⟧e state | ⟦ eln ⟧e state
  ... | i | m | ln = setListItem i m ln
  -- ⟦ SetArray zero n (x ∷ ln) ⟧e state = n ∷ ln
  -- ⟦ SetArray (suc i) n (x ∷ ln) ⟧e state = x ∷ ⟦ SetArray i n ln ⟧e state

  ⟦ Var x ⟧e state = state x
  ⟦ Plus e e₁ ⟧e state = ⟦ e ⟧e state + ⟦ e₁ ⟧e state

  ⟦ Hiext e e₁ ⟧e state = hiext (⟦ e ⟧e state) (⟦ e₁ ⟧e state)
  ⟦ Lov e ⟧e state = lov (⟦ e ⟧e state)
  ⟦ Lorem e ⟧e state = lorem (⟦ e ⟧e state)
  ⟦ History e ⟧e state = history (⟦ e ⟧e state)


  -- Instruction and its semantics

  VarValue : Set
  VarValue = Σ Vars (λ x → Expression (varTypes x))

  data Instruction : Set where
    SKIP : Instruction
    Assignment : List VarValue → Instruction

  -- -- makeNewState : State → (x y : Var) → Dec (x ≡ y) → State
  -- makeNewState :
  --   State → State → (x : Vars) → (Expression (varTypes x)) → State
  -- makeNewState st₀ st var value x with (x Data.Nat.≟ var)
  -- -- makeNewState st₀ var value x | yes refl = ⟦ value ⟧e st₀
  -- makeNewState st₀ st var value x | yes p rewrite p = ⟦ value ⟧e st₀
  -- makeNewState st₀ st var value x | no ¬p = st x

  -- assign : List VarValue → State → State → State
  -- assign [] st₀ st = st
  -- assign ((var , value) ∷ rest) st₀ st =
  --   assign rest st₀ (makeNewState st₀ st var value)

  assign : List VarValue → State → State → State
  assign [] st₀ st = st
  assign ((var , value) ∷ rest) st₀ st =
    assign rest st₀ newState
      where
        newState : State
        newState x with (x Data.Fin.≟ var)
        -- newState x | yes refl = ⟦ value ⟧e st₀
        newState x | yes p rewrite p = ⟦ value ⟧e st₀
        newState x | no ¬p = st x

  ⟦_⟧i : Instruction → State → State
  ⟦ SKIP ⟧i st = st
  ⟦ Assignment varExpressionPairs ⟧i st = assign varExpressionPairs st st


  -- Predicate and its semantics

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

  ConditionalInstruction : Set
  ConditionalInstruction = (Predicate × Instruction)

  ⟦⟧ciHelper : Bool → Instruction → State → State
  ⟦⟧ciHelper false i st = st
  ⟦⟧ciHelper true i st = ⟦ i ⟧i st

  ⟦_⟧ci : ConditionalInstruction → State → State
  ⟦ (p , i) ⟧ci st = ⟦⟧ciHelper (⟦ p ⟧c st) i st
  -- ⟦ (p , i) ⟧ci st with ⟦ p ⟧c st
  -- ... | false = st
  -- ... | true = ⟦ i ⟧i st


  ParallelProgram : Set
  ParallelProgram = List ConditionalInstruction

  NonEmpty : ParallelProgram → Set
  NonEmpty S = ¬ (S ≡ [])

  InitializedProgram : Set
  InitializedProgram = (ConditionalInstruction × ParallelProgram)

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
