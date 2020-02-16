open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding (_<_)
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

-- lemm2 :
--   (i : Instruction) → (st : State) → (n : ℕ) → n ≡ 1 →
--   ⟦⟧ciHelper ⌊ n Data.Nat.<? 3 ⌋ i st ≡ ⟦ i ⟧i st
-- lemm2 _ _ .1 refl = refl

-- lemm3 : {A B : Set} {f g : A → B} {a : A} {b : B} → f ≡ g → f a ≡ b → g a ≡ b
lemm3 : {X Y : Set} {f g : X → Y} {x : X} {y : Y} → f ≡ g → f x ≡ y → g x ≡ y
lemm3 refl p = p

-- ciProofHelper :
--   -- {i : Instruction} {P Q R : Predicate} {st : State} →
--   (st ⊢ (P △ ⌝ Q)) → ((⟦ R ⟧c st ≡ true → (⟦ (R , i) ⟧ci st) ⊢ (P ▽ Q))) →
--   ((⟦ (R , i) ⟧ci st) ⊢ (P ▽ Q))
-- ciProofHelper {st} {P} {Q} {R} p f with (⟦ R ⟧c st)
-- ciProofHelper {st} {P} {Q} {R} p f | false = inj₁ (proj₁ p)
-- ciProofHelper {st} {P} {Q} {R} p f | true = f refl

-- ciProofHelper2 :
--   (⟦ R ⟧c st ≡ true) → (⟦ R , i ⟧ci st ≡ ⟦ i ⟧i st)
-- ciProofHelper2 {R} {st} p with (⟦ R ⟧c st)
-- ciProofHelper2 {R} {st} p | true = refl

-- ciProofHelper3 :
--   {pq : st ⊢ (P △ ⌝ Q)} → ((⟦ R ⟧c st ≡ true → (⟦ i ⟧i st) ⊢ (P ▽ Q))) →
--   ((⟦ (R , i) ⟧ci st) ⊢ (P ▽ Q))
-- ciProofHelper3 {st} {P} {Q} {R} {i} {pq} f with (⟦ R ⟧c st)
-- ciProofHelper3 {st} {P} {Q} {R} {i} {pq} f | false = inj₁ (proj₁ pq)
-- ciProofHelper3 {st} {P} {Q} {R} {i} {pq} f | true = f refl

inst : Instruction
inst = Assignment [(0 , Plus v[ 0 ] (ConstNat 1))]

asdf2 : (EQ v[ 0 ] (ConstNat 1)) ▷[
    (TRUE , SKIP)
    ,
    [ ((LT v[ 0 ] (ConstNat 3)) , Assignment [(0 , Plus v[ 0 ] (ConstNat 1))]) ]
  ] (EQ v[ 0 ] (ConstNat 2))

asdf2 {st} (before , ⌝after) =
  ▷-proof
    {st}
    {EQ v[ 0 ] (ConstNat 1)}
    {EQ v[ 0 ] (ConstNat 2)}
    {_}
    {(TRUE , SKIP)}
    (before , ⌝after)
    (
      ((λ x → inj₂ (cong (_+ 1) before)))
    ∷ [])
    -- {!!}
--     {{!!}}
--     {{!!}}
--     {st}

-- asdf2 {st} (before , ⌝after) =
--   ▷-proofHelper
--     {st}
--     {EQ v[ 0 ] (ConstNat 1)}
--     {EQ v[ 0 ] (ConstNat 2)}
--     {LT v[ 0 ] (ConstNat 3)}
--     {_} -- {inst}
--     {before , ⌝after}
--     (λ x → inj₂ (cong (_+ 1) before))
--   ∷ []

  -- ciProofHelper
  --   -- {st}
  --   -- {(EQ v[ 0 ] (ConstNat 1))}
  --   -- {(EQ v[ 0 ] (ConstNat 2))}
  --   -- {(LT v[ 0 ] (ConstNat 3))}
  --   (before , ⌝after)
  --   (λ x → inj₂ (lemm3 (ciProofHelper2 x) (cong (_+ 1) before))) ∷ []

  -- inj₂ (lemm3 (sym (lemm2 inst st (st 0) before)) (cong (_+ 1) before)) ∷ []

  -- inj₂ ((λ { refl p → p }) (sym (lemm2 inst st (st 0) before)) (cong (_+ 1) before)) ∷ []

smaller : {n : ℕ} → n < 3 → n < 5
smaller (s≤s z≤n) = s≤s z≤n
smaller (s≤s (s≤s z≤n)) = s≤s (s≤s z≤n)
smaller (s≤s (s≤s (s≤s z≤n))) = s≤s (s≤s (s≤s z≤n))

sm-test : 2 < 5
sm-test = smaller (s≤s (s≤s (s≤s z≤n)))
