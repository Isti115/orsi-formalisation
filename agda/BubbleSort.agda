open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])

module BubbleSort where

open import Simple
import Statements

varTypes : ℕ → Types
varTypes = (λ n → ListNat)

open module ListNatOnlySimple = Simple.Program varTypes
open module ListNatOnlyStatements = Statements varTypes

-- module Implementation (count : ℕ) where

  -- count : ℕ
  -- count = 4

  -- range : ℕ → ℕ → List ℕ
  -- range from zero = []
  -- range zero (suc to) = to ∷ range zero to
  -- range (suc from) (suc to) = {!!}

  -- range : ℕ → ℕ → List ℕ
  -- range from to =
  --   if ⌊ from Data.Nat.<? to ⌋
  --   then from ∷ range (suc from) to
  --   else []


makePredicate : ℕ → Predicate
makePredicate n = (
    GT (v[ 0 ] g[ ConstNat n ]) (v[ 0 ] g[ ConstNat (n + 1) ])
  )

makeInstruction : ℕ → Instruction
makeInstruction n = (
    Assignment [(
      0
      ,
      (
        v[ 0 ]
        s[ ConstNat n ]=(v[ 0 ] g[ ConstNat (n + 1) ])
        s[ ConstNat (n + 1) ]=(v[ 0 ] g[ ConstNat n ])
      )
    )]
  )

bubbleSort : ℕ → ParallelProgram
bubbleSort count =
  (
    (TRUE , SKIP)
    ,
    Data.List.map
      (λ x → (makePredicate x , makeInstruction x))
      (downFrom count)
      -- GT (GetListNat (ConstNat x) (Var 0)) ((GetListNat (ConstNat (x + 1)) (Var 0)))
    -- )) (range 1 count)
    -- )) (Data.List.filter (λ y → 0 Data.Nat.<? y) (downFrom count))
  )


-- module Proof where

--   open module Implementation

Before : Predicate
Before = EQ (v[ 0 ] g[ ConstNat 0 ]) (ConstNat 1)

After : Predicate
After = EQ (v[ 0 ] g[ ConstNat 0 ]) (ConstNat 0)

h1 : {x : ℕ} → suc (suc x) ≤ 1 → ⊥
h1 (s≤s ())

helper :
  (st ⊢ (Before △ ⌝ After)) →
  ⟦ makePredicate 0 ⟧a st →
  ⟦ makeInstruction 0 ⟧i st ⊢ (Before ▽ After)
helper {st} (before , after) gt with ((st 0) 1)
helper {st} (before , after) gt | zero = inj₂ refl
-- helper {st} (before , after) gt | zero with (st 0)
-- helper {st} (before , after) gt | zero | l ∷ ls = inj₂ refl
helper {st} (before , after) gt | suc x rewrite before = ⊥-elim (h1 gt)

test2 : Before ▷[ bubbleSort 1 ] After
test2 {st} =
  ▷-proof
    {Before}
    {After}
    ((λ {st} → (helper {st})) ∷ [])
    -- ((λ { (b , ⌝a) gt → {!!} }) ∷ [])
    {TRUE , SKIP}

set-get :
  {n x : ℕ} → {l : ℕ → ℕ} →
  (setListItem n x l) n ≡ x
set-get {n} {x} with n Data.Nat.≟ n
set-get {n} {x} | yes p = refl
set-get {n} {x} | no ¬p = ⊥-elim (¬p refl)

-- set-get {zero} {x} {[]} = {!!}
-- set-get {zero} {x} {x₁ ∷ l} = {!!}
-- set-get {suc n} {x} {[]} = {!!}
-- set-get {suc n} {x} {x₁ ∷ l} = {!!}

set-helper :
  {n m x y : ℕ} → {l : ℕ → ℕ} →
  (n ≢ m) → (l n ≡ x) →
  (setListItem m y l) n ≡ x
set-helper {n} {m} {x} {y} {f} neq refl with n Data.Nat.≟ m
set-helper {n} {m} {.(f n)} {y} {f} neq refl | yes p = ⊥-elim (neq p)
set-helper {n} {m} {.(f n)} {y} {f} neq refl | no ¬p = refl

-- set-helper {n} {m} {.0} {y} {[]} neq refl = refl
-- set-helper {zero} {zero} {.x} {y} {x ∷ l} neq refl = ⊥-elim (neq refl)
-- set-helper {zero} {suc m} {.x} {y} {x ∷ l} neq refl = refl
-- set-helper {suc n} {zero}
--   {.(l n)} {y} {x ∷ l} neq refl = refl
-- set-helper {suc n} {suc m}
--   {.(l n)} {y} {x ∷ l} neq refl =
--     set-helper {n} {m} {_} {_} {l} (λ eq → neq (cong suc eq)) refl

helper-n :
  (n : ℕ) →
  (st ⊢ (Before △ ⌝ After)) →
  ⟦ makePredicate n ⟧a st →
  ⟦ makeInstruction n ⟧i st ⊢ (Before ▽ After)
helper-n {st} zero (before , after) gt = helper {st} (before , after) gt
helper-n {st} (suc n) (before , after) gt = inj₁ before
  -- inj₁ (
  --   set-helper {_} {_} {_} {_} {
  --     setListItem (suc n) ((st 0) (suc (n + 1))) (st 0)
  --  } (λ ()) (
  --     set-helper {_} {_} {_} {_} {st 0} (λ ()) before
  --   )
  -- )

test3 : Before ▷[ bubbleSort 2 ] After
test3 {st} =
  ▷-proof
    {Before}
    {After}
    ((λ {st} → (helper-n {st} 1)) ∷ (λ {st} → (helper-n {st} 0)) ∷ [])
    {TRUE , SKIP}


-- test-n : (n : ℕ) → Before ▷[ bubbleSort n ] After
-- test-n n {st} =
--   ▷-proof
--     {Before}
--     {After}
--     {!Data.List.map (λ n → λ {st} → helper-n {st} n) (downFrom n)!}
--     {TRUE , SKIP}

-- test zero {st} (before , ⌝after) = []
-- test (suc n) {st} (before , ⌝after) = {!? ∷ ?!}

After' : Predicate
After' = EQ (v[ 0 ] g[ ConstNat 1 ]) (ConstNat 0)

helper' :
  (st ⊢ (Before △ ⌝ After')) →
  ⟦ makePredicate 0 ⟧a st →
  ⟦ makeInstruction 0 ⟧i st ⊢ (Before ▽ After')
helper' {st} (before , after) gt with ((st 0) 1)
helper' {st} (before , after) gt | zero = ⊥-elim (after refl)
helper' {st} (before , after) gt | suc x rewrite before = ⊥-elim (h1 gt)

test2' : Before ▷[ bubbleSort 1 ] After'
test2' {st} =
  ▷-proof
    {Before}
    {After'}
    ((λ {st} → helper' {st}) ∷ [])
    {TRUE , SKIP}

--

Ordered : ℕ → Predicate
Ordered zero = TRUE
Ordered (suc n) =
  LTE (v[ 0 ] g[ ConstNat n ]) (v[ 0 ] g[ ConstNat (suc n) ])
  △
  (Ordered n)

-- rp-h1 : {n m : ℕ} → ¬(m ≤ n) → n ≤ m
-- rp-h1 {zero} {m} nle = z≤n
-- rp-h1 {suc n} {zero} nle = ⊥-elim (nle z≤n)
-- rp-h1 {suc n} {suc m} nle = s≤s (rp-h1 (λ m≤n → nle (s≤s m≤n)))

-- Same as Data.Nat.Properties.≰⇒>
-- rp-h2 : {n m : ℕ} → ¬(m ≤ n) → (Data.Nat._<_ n m)
-- rp-h2 {m} {zero} nle = ⊥-elim (nle z≤n)
-- rp-h2 {zero} {suc m} nle = s≤s z≤n
-- rp-h2 {suc n} {suc m} nle = s≤s (rp-h2 (λ m≤n → nle (s≤s m≤n)))

-- rp-h3 :
--   {n : ℕ} →
--   st ≡ ⟦ makeInstruction n ⟧i st →
--   ⟦ v[ 0 ] g[ ConstNat n ] ⟧e st ≡ ⟦ v[ 0 ] g[ ConstNat (suc n) ] ⟧e st
-- rp-h3 {n} eq = {!!}

-- fx' :
--   {A B : Set} → {f g : A → B} → (a : A) →
--   (f ≡ g) → (f a ≡ g a)
-- fx' _ refl = refl

-- fx'' :
--   {A B : Set} → {f g : A → B} → (a : A) →
--   (f ≡ g) → (f a ≡ g a)
-- fx'' a = cong (_$ a)

rp-h3' :
  st ≡ ⟦ makeInstruction 0 ⟧i st →
  ⟦ v[ 0 ] g[ ConstNat 0 ] ⟧e st ≡ ⟦ v[ 0 ] g[ ConstNat 1 ] ⟧e st
rp-h3' = cong (_$ 0) ∘ (cong (_$ 0))
-- rp-h3' {st} eq = (fx' 0 (fx' 0 eq))

-- fx :
--   {f g : ℕ → ℕ} → {n : ℕ} →
--   (f ≡ g) → (f n ≡ g n)
-- fx refl = refl

-- rp-h3' :
--   st ≡ ⟦ makeInstruction 0 ⟧i st →
--   ⟦ v[ 0 ] g[ ConstNat 0 ] ⟧e st ≡ ⟦ v[ 0 ] g[ ConstNat 1 ] ⟧e st
-- rp-h3' {st} eq = {!fx {st 0} {⟦ makeInstruction 0 ⟧i st 0} {0}!}
-- rp-h3' {st} eq =
--   fx {st 0} {⟦ makeInstruction 0 ⟧i st 0}
--     {!!}

-- rp-h3' {st} eq rewrite eq =
  -- set-helper {0} {1}
  --   {(setListItem 1 ((st 0) 0) (setListItem 0 ((st 0) 1) (st 0))) 1}
  --   {((st 0) 0)}
  --   {(setListItem 0 ((st 0) 1) (st 0))}
  --   (λ ())
    -- {!!}

  -- set-helper {0} {1} {{!!}} {{!!}} {{!!}} (λ ()) {!!}


resultProof-1 : φ[ bubbleSort 1 ] ⇛ ⟦ Ordered 1 ⟧a
resultProof-1 {st} (fp ∷ []) with (ci-helper {st} {makePredicate 0} fp)
resultProof-1 {st} (fp ∷ []) | inj₁ x with (≰⇒> x)
resultProof-1 {st} (fp ∷ []) | inj₁ x | s≤s z = (z , tt)
resultProof-1 {st} (fp ∷ []) | inj₂ y =
  (≤-reflexive (rp-h3' y) , tt)

  -- let
  --   cih = ci-helper {st} {makePredicate 0} fp
  -- in
    -- (
    --   ?
    --   ,
    --   tt
    -- )
  -- where
  --   cih = ci-helper {st} {makePredicate 0} fp
