module Base where

-- Imports

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.Relation.Unary.All hiding (_∷_)
open import Function

-- Vars, Values, State, emptyState

data Types : Set
evaluateType : Types → Set
defaultValue : (A : Types) → (evaluateType A)

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

queueToList : {A : Types} → Queue A → List (evaluateType A)
queueToList Leaf = []
queueToList (Node x l r) = queueToList l ++ (x ∷ queueToList r)

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

len' : {A : Types} → QueueWithHistory A → ℕ
len' (q , h) = len q

-- Types

data Types where
  Nat : Types
  Array : Types → Types
  DataChannel : Types → Types

evaluateType Nat = ℕ
evaluateType (Array A) = Σ ℕ (λ l → (Fin l → (evaluateType A)))
evaluateType (DataChannel A) = QueueWithHistory A

defaultValue Nat = zero
defaultValue (Array A) = (0 , const (defaultValue A))
defaultValue (DataChannel A) = (Leaf , [])

--

ownEq : {A : Types} → (a b : evaluateType A) → Set

infix 4 _≋_
data _≋_ {A : Types} (a b : evaluateType A) : Set
-- _≋_ : {A : Types} → (a b : evaluateType A) → Set

finDownFrom : (n : ℕ) → List (Fin n)
finDownFrom zero = []
finDownFrom (suc n) = fromℕ n ∷ Data.List.map inject₁ (finDownFrom n)

finListEq : {A : Types} → (l : ℕ) → (f g : Fin l → evaluateType A) → Set
finListEq l f g = (i : Fin l) → (f i ≋ g i)

ownListEq : {A : Types} → (a b : List (evaluateType A)) → Set
ownListEq [] [] = ⊤
ownListEq [] (b ∷ bs) = ⊥
ownListEq (a ∷ as) [] = ⊥
ownListEq (a ∷ as) (b ∷ bs) = a ≋ b × (ownListEq as bs)

ownEq {Nat} a b = a ≡ b
ownEq {Array A} (la , as) (lb , bs) = Σ (la ≡ lb) λ { refl → finListEq la as bs }
ownEq {DataChannel A} a b = ownListEq (queueToList (proj₁ a)) (queueToList (proj₁ b))

data _≋_ {A} a b where
  ownRefl : (ownEq a b) → a ≋ b
-- a ≋ b = ownEq a b

--

infix 4 _≋?_
_≋?_ : {A : Types} → (a b : evaluateType A) → Dec (a ≋ b)

finListDec : {A : Types} → (l : ℕ) → (a b : Fin l → evaluateType A) → Dec (finListEq l a b)
finListDec zero a b = yes (λ ())
finListDec (suc l) a b with (a zero ≋? b zero) | (finListDec l (a ∘ suc) (b ∘ suc))
... | .true because ofʸ p | .true because ofʸ p₁ = yes (λ { zero → p ; (suc i) → p₁ i })
... | .true because ofʸ p | .false because ofⁿ ¬p = no (λ z → ¬p (z ∘ suc))
... | .false because ofⁿ ¬p | _ = no (λ z → ¬p (z zero))

arrayDecEq : {A : Types} → (a b : (evaluateType (Array A))) → Dec (ownEq {Array A} a b)
arrayDecEq (la , as) (lb , bs) with la Data.Nat.≟ lb
arrayDecEq (la , as) (lb , bs) | yes refl with (finListDec la as bs)
arrayDecEq (la , as) (la , bs) | yes refl | yes p = yes (refl , p)
arrayDecEq (la , as) (la , bs) | yes refl | no ¬p = no λ { (refl , ⌝leq) → ¬p ⌝leq }
arrayDecEq (la , as) (lb , bs) | no ¬p = no (λ z → ¬p (proj₁ z))

ownListDecEq : {A : Types} → (a b : List (evaluateType A)) → Dec (ownListEq a b)
ownListDecEq [] [] = yes tt
ownListDecEq [] (b ∷ bs) = no id
ownListDecEq (a ∷ as) [] = no id
ownListDecEq (a ∷ as) (b ∷ bs) with a ≋? b | ownListDecEq as bs
ownListDecEq (a ∷ as) (b ∷ bs) | yes p | yes p₁ = yes (p , p₁)
ownListDecEq (a ∷ as) (b ∷ bs) | yes p | no ¬p = no (λ z → ¬p (proj₂ z))
ownListDecEq (a ∷ as) (b ∷ bs) | no ¬p | y = no (λ z → ¬p (proj₁ z))

Queue≟ : {A : Types} → (q r : Queue A) → Dec (ownListEq (queueToList q) (queueToList r))
Queue≟ q r with queueToList q | queueToList r
Queue≟ q r | qq | rr = ownListDecEq qq rr

dataChannelDecEq :
  {A : Types} →
  (a b : (evaluateType (DataChannel A))) → Dec (ownEq {DataChannel A} a b)
dataChannelDecEq (aq , ah) (bq , bh) = Queue≟ aq bq

decEq : {A : Types} → (a b : evaluateType A) → Dec (ownEq a b)
decEq {Nat} = Data.Nat._≟_
decEq {Array A} = arrayDecEq
decEq {DataChannel A} = dataChannelDecEq

a ≋? b with (decEq a b)
... | no ¬p = no λ { (ownRefl z) → ¬p z }
... | yes p = yes (ownRefl p)

--

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
    Len : {A : Types} → Expression (DataChannel A) → Expression (Nat)

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

  listEquality :
    {A : Set} → {a b : A} → {as bs : List A} →
    (a ≡ b) → (as ≡ bs) → (a ∷ as ≡ b ∷ bs)
  listEquality refl refl = refl

  listToFunction∘functionToList-test :
    (ln : List ℕ) → functionToList (length ln) (listToFunction ln) ≡ ln
  listToFunction∘functionToList-test [] = refl
  listToFunction∘functionToList-test (n ∷ ns) =
    listEquality refl (listToFunction∘functionToList-test ns)

  -- getListItem : {A : Types} → {le : ℕ} → Fin le → (li : evaluateType (Array A)) → (proj₁ li ≡ le) → evaluateType A
  -- getListItem = {!!}

  setListItem : {A : Types} → {le : ℕ} → Fin le → evaluateType A → (li : evaluateType (Array A)) → (proj₁ li ≡ le) → evaluateType (Array A)
  setListItem i v (l , f) refl = (l , λ j → if isYes (i Data.Fin.≟ j) then v else (f j))
  -- setListItem i v (l , f) refl = (l , λ j → if ⌊ i Data.Fin.≟ j ⌋ then v else (f j))

  ⟦_⟧e : {A : Types} → Expression A → State → evaluateType A
  ⟦ Const value ⟧e state = value

  ⟦ GetArray ei el ⟧e state with ⟦ ei ⟧e state | ⟦ el ⟧e state
  ⟦ GetArray ei el ⟧e state | i | l , ls with i Data.Nat.<? l
  ⟦ GetArray ei el ⟧e state | i | l , ls | yes p = ls (fromℕ< p)
  ⟦ GetArray {A} ei el ⟧e state | i | l , ls | no ¬p = defaultValue A

  ⟦ SetArray ei ev el ⟧e state with ⟦ ei ⟧e state | ⟦ ev ⟧e state | ⟦ el ⟧e state
  ⟦ SetArray ei ev el ⟧e state | i | v | (l , f) with i Data.Nat.<? l
  ⟦ SetArray ei ev el ⟧e state | i | v | l , f | yes p = setListItem (fromℕ< p) v (l , f) refl
  ⟦ SetArray ei ev el ⟧e state | i | v | l , f | no ¬p = (l , f) -- setListItem i m ln

  ⟦ Var x ⟧e state = state x
  ⟦ Plus e e₁ ⟧e state = ⟦ e ⟧e state + ⟦ e₁ ⟧e state

  ⟦ Hiext e e₁ ⟧e state = hiext (⟦ e ⟧e state) (⟦ e₁ ⟧e state)
  ⟦ Lov e ⟧e state = lov (⟦ e ⟧e state)
  ⟦ Lorem e ⟧e state = lorem (⟦ e ⟧e state)
  ⟦ History e ⟧e state = history (⟦ e ⟧e state)
  ⟦ Len e ⟧e state = len' (⟦ e ⟧e state)


  -- Instruction and its semantics

  VarValue : Set
  VarValue = Σ Vars (λ x → Expression (varTypes x))

  data Instruction : Set where
    SKIP : Instruction
    Assignment : List VarValue → Instruction

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

    EQ : {A : Types} → Expression A → Expression A → Predicate

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

  ⟦ EQ e e₁ ⟧a state = ((⟦ e ⟧e state) ≋ (⟦ e₁ ⟧e state))

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

  ⟦ EQ e e₁ ⟧d state = ((⟦ e ⟧e state) ≋? (⟦ e₁ ⟧e state))

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
