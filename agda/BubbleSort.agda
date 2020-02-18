open import Relation.Nullary.Decidable
open import Data.Bool
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

bubbleSort : ℕ → ParallelProgram
bubbleSort count =
  (
    (TRUE , SKIP)
    ,
    Data.List.map (λ x → (
      -- GT (GetListNat (ConstNat x) (Var 0)) ((GetListNat (ConstNat (x + 1)) (Var 0)))
      GT (v[ 0 ] g[ ConstNat x ]) (v[ 0 ] g[ ConstNat (x + 1) ])
      ,
      Assignment [(
        0
        ,
        (
          v[ 0 ]
          s[ ConstNat x ]=(v[ 0 ] g[ ConstNat (x + 1) ])
          s[ ConstNat (x + 1) ]=(v[ 0 ] g[ ConstNat x ])
        )
      )]
    -- )) (range 1 count)
    -- )) (Data.List.filter (λ y → 0 Data.Nat.<? y) (downFrom count))
    )) (downFrom count)
  )


-- module Proof where

--   open module Implementation

Before : Predicate
Before = EQ (v[ 0 ] g[ ConstNat 0 ]) (ConstNat 1)

After : Predicate
After = EQ (v[ 0 ] g[ ConstNat 0 ]) (ConstNat 0)

helper :
  (st ⊢ (Before △ ⌝ After)) →
  ⟦ GT (v[ 0 ] g[ ConstNat 0 ]) (v[ 0 ] g[ ConstNat 1 ]) ⟧c st ≡ true →
  (⟦ Assignment [(
        0
        ,
        (
          v[ 0 ]
          s[ ConstNat 0 ]=(v[ 0 ] g[ ConstNat (0 + 1) ])
          s[ ConstNat (0 + 1) ]=(v[ 0 ] g[ ConstNat 0 ])
        )
      )] ⟧i st) ⊢ (Before ▽ After)
helper bna gt = {!!}

test2 : Before ▷[ bubbleSort 1 ] After
test2 =
  ▷-proof
    {Before}
    {After}
    (helper ∷ [])
    -- ((λ { (b , ⌝a) gt → {!!} }) ∷ [])
    {TRUE , SKIP}


-- test2 {st} (before , ⌝after) with (⌊
--           ⟦ GetListNat (ConstNat 0) (Example.Var 0) ⟧e st
--           >?
--           ⟦ GetListNat (ConstNat 1) (Example.Var 0) ⟧e st
--           ⌋)
-- test2 {st} (before , ⌝after) | false = (inj₂ {!!}) ∷ []
-- test2 {st} (before , ⌝after) | true = (inj₂ {!!}) ∷ []

-- test2 {st} (before , ⌝after) with (⟦
--     GT
--       (v[ 0 ] g[ ConstNat 0 ])
--       (v[ 0 ] g[ ConstNat 1 ])
--   ⟧c st)
-- test2 {st} (before , ⌝after) | false = {!!} ∷ {!!}
-- test2 {st} (before , ⌝after) | true = {!!}

-- test2 {st} (before , ⌝after) with (⟦ GetListNat (ConstNat 1) (Var 0) ⟧e st)
-- test2 {st} (before , ⌝after) | zero = (inj₂ {!refl!}) ∷ []
-- test2 {st} (before , ⌝after) | suc x = (inj₁ {!!}) ∷ []
  -- {!!} ∷
  -- []

-- test3 : Before ▷[ bubbleSort 2 ] After
-- test3 {st} (before , ⌝after) =
--   {!!} ∷
--   {!!} ∷
--   []

-- test : (n : ℕ) → Before ▷[ bubbleSort n ] After
-- test zero {st} (before , ⌝after) = []
-- test (suc n) {st} (before , ⌝after) = {!? ∷ ?!}

