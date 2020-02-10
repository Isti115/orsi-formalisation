open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All

open import Relation.Binary.PropositionalEquality as Eq hiding ([_])

module ProofTest where

open import Simple
import Statements

varTypes : ℕ → Types
varTypes = (λ n → Nat)

open module NatOnlySimple = Simple.Program varTypes
open module NatOnlyStatements = Statements varTypes

asdf : (EQ v[ 0 ] (ConstNat 1)) ▷[
    (TRUE , SKIP)
    ,
    [ (TRUE , Assignment [(0 , Plus v[ 0 ] (ConstNat 1))]) ]
    -- [ (TRUE , Assignment [(0 , ConstNat 2)]) ]
  ] (EQ v[ 0 ] (ConstNat 2))
asdf {st} (before , ⌝after) rewrite before = inj₂ (cong (_+ 1) before) ∷ []
-- asdf {st} (before , ⌝after) = inj₂ {!!} ∷ []


qwerty : (n : ℕ) → n ≡ 1 → ⌊ n Data.Nat.<? 3 ⌋ ≡ true
qwerty .1 refl = refl

lemm2 :
  -- ∀ {i : Instruction} {st : State} →
  (i : Instruction) → (st : State) →
  (n : ℕ) → n ≡ 1 →
  ⟦⟧ciHelper ⌊ n Data.Nat.<? 3 ⌋ i st ≡ ⟦ i ⟧i st
-- lemm2 .1 refl = refl
lemm2 _ _ .1 refl = refl

lemm3 : {st0 st1 : State} → st0 ≡ st1 → st0 0 ≡ 2 → st1 0 ≡ 2
lemm3 refl p = p

-- lemm3 : 

inst : Instruction
inst = Assignment [(0 , Plus v[ 0 ] (ConstNat 1))]

asdf2 : (EQ v[ 0 ] (ConstNat 1)) ▷[
    (TRUE , SKIP)
    ,
    [ ((LT v[ 0 ] (ConstNat 3)) , Assignment [(0 , Plus v[ 0 ] (ConstNat 1))]) ]
    -- [ (TRUE , Assignment [(0 , ConstNat 2)]) ]
  ] (EQ v[ 0 ] (ConstNat 2))

-- asdf2 {st} (before , ⌝after) rewrite (qwerty (st 0) before) = inj₂ {!!} ∷ []
-- asdf2 {st} (before , ⌝after) rewrite (lemm2 inst st (st 0) before) = inj₂ {!!} ∷ []
-- asdf2 {st} (before , ⌝after) = inj₂ (trans {!(lemm2 inst st (st 0) before)!} {!!}) ∷ []
asdf2 {st} (before , ⌝after) =
  inj₂ (lemm3 (sym (lemm2 inst st (st 0) before)) (cong (_+ 1) before)) ∷ []

-- asdf2 {st} (before , ⌝after) with inspect (λ n → ⌊ n Data.Nat.<? 3 ⌋) (st 0)
-- asdf2 {st} (before , ⌝after) | Reveal_·_is_.[ eq ] = inj₁ {!!} ∷ []

-- asdf2 {st} (before , ⌝after) with st 0 Data.Nat.<? 3
-- asdf2 {st} (before , ⌝after) | yes p = inj₂ {!!} ∷ []
-- asdf2 {st} (before , ⌝after) | no ¬p = inj₁ {!!} ∷ []

-- asdf2 {st} (before , ⌝after) with ⌊ st 0 Data.Nat.<? 3 ⌋
-- asdf2 {st} (before , ⌝after) | false rewrite before = inj₁ {!!} ∷ []
-- asdf2 {st} (before , ⌝after) | true = inj₂ {!!} ∷ []

-- asdf2 {st} (before , ⌝after) with ⟦ (LT v[ 0 ] (ConstNat 3)) ⟧c st
-- asdf2 {st} (before , ⌝after) | false = inj₁ {!!} ∷ []
-- asdf2 {st} (before , ⌝after) | true = {!!} ∷ []
