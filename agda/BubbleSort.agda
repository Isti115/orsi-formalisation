open import Relation.Nullary.Decidable
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.List

module BubbleSort (count : ℕ) where

open import Simple
-- open import Statements

open module ListNatOnly = Simple.Program (λ n → ListNat)

-- range : ℕ → ℕ → List ℕ
-- range from zero = []
-- range zero (suc to) = to ∷ range zero to
-- range (suc from) (suc to) = {!!}

-- range : ℕ → ℕ → List ℕ
-- range from to =
--   if ⌊ from Data.Nat.<? to ⌋
--   then from ∷ range (suc from) to
--   else []

bubbleSort : ParallelProgram
bubbleSort =
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
    )) (Data.List.filter (λ y → 0 Data.Nat.<? y) (downFrom count))
  )

