open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All

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
helper {st} (before , after) gt with (getWithDefaultZero 1 (st 0))
helper {st} (before , after) gt | zero with (st 0)
helper {st} (before , after) gt | zero | l ∷ ls = inj₂ refl
helper {st} (before , after) gt | suc x rewrite before = ⊥-elim (h1 gt)

test2 : Before ▷[ bubbleSort 1 ] After
test2 {st} =
  ▷-proof
    {Before}
    {After}
    ((λ {st} → (helper {st})) ∷ [])
    -- ((λ { (b , ⌝a) gt → {!!} }) ∷ [])
    {TRUE , SKIP}

set-helper :
  {n m x y : ℕ} → {l : List ℕ} →
  (n ≢ m) →
  (getWithDefaultZero n l ≡ x) →
  getWithDefaultZero n (setWithDefaultEmpty m y l) ≡ x
set-helper {n} {m} {.0} {y} {[]} neq refl = refl
set-helper {zero} {zero} {.x} {y} {x ∷ l} neq refl = ⊥-elim (neq refl)
set-helper {zero} {suc m} {.x} {y} {x ∷ l} neq refl = refl
set-helper {suc n} {zero}
  {.(getWithDefaultZero n l)} {y} {x ∷ l} neq refl = refl
set-helper {suc n} {suc m}
  {.(getWithDefaultZero n l)} {y} {x ∷ l} neq refl =
    set-helper {n} {m} {_} {_} {l} (λ eq → neq (cong suc eq)) refl

helper-n :
  (n : ℕ) →
  (st ⊢ (Before △ ⌝ After)) →
  ⟦ makePredicate n ⟧a st →
  ⟦ makeInstruction n ⟧i st ⊢ (Before ▽ After)
helper-n {st} zero (before , after) gt = helper {st} (before , after) gt
helper-n {st} (suc n) (before , after) gt =
  inj₁ (
    set-helper {_} {_} {_} {_} {
      setWithDefaultEmpty (suc n) (getWithDefaultZero (suc (n + 1)) (st 0)) (st 0)
   } (λ ()) (
      set-helper {_} {_} {_} {_} {st 0} (λ ()) before
    )
  )

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
helper' {st} (before , after) gt with (getWithDefaultZero 1 (st 0))
helper' {st} (before , after) gt | zero = ⊥-elim (after refl)
helper' {st} (before , after) gt | suc x rewrite before = ⊥-elim (h1 gt)

test2' : Before ▷[ bubbleSort 1 ] After'
test2' {st} =
  ▷-proof
    {Before}
    {After'}
    ((λ {st} → helper' {st}) ∷ [])
    {TRUE , SKIP}
