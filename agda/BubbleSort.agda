open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Fin hiding (_≤_)
open import Data.Fin.Patterns
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.Relation.Unary.All

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])

module BubbleSort where

import Base
open Base._≋_
import Statements

varTypes : Fin 1 → Base.Types
varTypes 0F = Base.Array Base.Nat

-- varTypes : Fin 1 → Base.Types
-- varTypes = (λ n → Base.Array Base.Nat)

open module BubbleSortEnvironment = Base.Environment 1 varTypes
open module ListNatOnlyStatements = Statements 1 varTypes

makePredicate : ℕ → Predicate
makePredicate n = GT (v[ 0F ] g[ Const n ]) (v[ 0F ] g[ Const (suc n) ])

makeInstruction : ℕ → Instruction
makeInstruction n =
  Assignment 0F
    (
      v[ 0F ]
      s[ Const n ]=(v[ 0F ] g[ Const (suc n) ])
      s[ Const (suc n) ]=(v[ 0F ] g[ Const n ])
    )

bubbleSort : ℕ → ParallelProgram
bubbleSort count =
  (
    Data.List.map
      (λ x → (makePredicate x , [ makeInstruction x ]))
      (downFrom count)
  )

-- a[0] = 1 ▷ a[0] = 0

Before : Predicate
Before = EQ (v[ 0F ] g[ Const 0 ]) (Const 1)

After : Predicate
After = EQ (v[ 0F ] g[ Const 0 ]) (Const 0)

h1 : {x : ℕ} → suc (suc x) ≤ 1 → ⊥
h1 (s≤s ())

helper :
  (st ⊢ (Before △ ⌝ After)) →
  ⟦ makePredicate 0 ⟧a st →
  ⟦ makeInstruction 0 ⟧i st ⊢ (Before ▽ After)
helper {st} (before , after) gt with (proj₂ (st 0F) 1)
helper {st} (before , after) gt | zero = inj₂ (ownRefl refl)
helper {st} (ownRefl before , after) gt | suc _ rewrite before = ⊥-elim (h1 gt)

-- set-get :
--   {n x : ℕ} → {l : (ℕ × (ℕ → ℕ))} →
--   proj₂ (setListItem n x l) n ≡ x
-- set-get {n} {x} with n Data.Nat.≟ n
-- set-get {n} {x} | yes p = refl
-- set-get {n} {x} | no ¬p = ⊥-elim (¬p refl)

-- set-helper :
--   {n m x y : ℕ} → {l : (ℕ × (ℕ → ℕ))} →
--   (n ≢ m) → (proj₂ l n ≡ x) →
--   proj₂ (setListItem m y l) n ≡ x
-- set-helper {n} {m} {x} {y} {f} neq refl with n Data.Nat.≟ m
-- set-helper {n} {m} {.(proj₂ f n)} {y} {f} neq refl | yes p = ⊥-elim (neq p)
-- set-helper {n} {m} {.(proj₂ f n)} {y} {f} neq refl | no ¬p = refl

helper-n :
  (n : ℕ) →
  (st ⊢ (Before △ ⌝ After)) →
  ⟦ makePredicate n ⟧a st →
  ⟦ makeInstruction n ⟧i st ⊢ (Before ▽ After)
helper-n {st} zero (before , after) gt = helper {st} (before , after) gt
helper-n {st} (suc n) (before , after) gt = inj₁ before

all-helper :
  (n : ℕ) →
  (All (λ { (R , il) →
    ({st : State} → st ⊢ (Before △ ⌝ After) → ⟦ R ⟧a st → (⟦ il ⟧il st) ⊢ (Before ▽ After))
  }) (bubbleSort n))
all-helper zero = []
all-helper (suc n) = ((λ {st} → helper-n {st} n) ∷ all-helper n)

test-n : (n : ℕ) → Before ▷[ bubbleSort n ] After
test-n n {st} = ▷-proof {Before} {After} (all-helper n)

-- test3 : Before ▷[ bubbleSort 2 ] After
-- test3 {st} =
--   ▷-proof
--     {Before}
--     {After}
--     ((λ {st} → (helper-n {st} 1)) ∷ (λ {st} → (helper-n {st} 0)) ∷ [])

-- After' : Predicate
-- After' = EQ (v[ 0F ] g[ Const 1 ]) (Const 0)

-- helper' :
--   (st ⊢ (Before △ ⌝ After')) →
--   ⟦ makePredicate 0 ⟧a st →
--   ⟦ makeInstruction 0 ⟧i st ⊢ (Before ▽ After')
-- helper' {st} (before , after) gt with (proj₂ (st 0F) 1)
-- helper' {st} (before , after) gt | zero = ⊥-elim (after (ownRefl refl))
-- helper' {st} (ownRefl before , after) gt | suc _ rewrite before = ⊥-elim (h1 gt)

-- test2' : Before ▷[ bubbleSort 1 ] After'
-- test2' {st} =
--   ▷-proof
--     {Before}
--     {After'}
--     ((λ {st} → helper' {st}) ∷ [])

-- Ordered

Ordered' : ℕ → Predicate
Ordered' n = LTE (v[ 0F ] g[ Const n ]) (v[ 0F ] g[ Const (suc n) ])

Ordered : ℕ → Predicate
Ordered zero = TRUE
Ordered (suc n) = Ordered' n △ (Ordered n)

-- rp-h1 : {n m : ℕ} → ¬(m ≤ n) → n ≤ m
-- rp-h1 {zero} {m} nle = z≤n
-- rp-h1 {suc n} {zero} nle = ⊥-elim (nle z≤n)
-- rp-h1 {suc n} {suc m} nle = s≤s (rp-h1 (λ m≤n → nle (s≤s m≤n)))

-- -- Same as Data.Nat.Properties.≰⇒>
-- rp-h2 : {n m : ℕ} → ¬(m ≤ n) → (Data.Nat._<_ n m)
-- rp-h2 {m} {zero} nle = ⊥-elim (nle z≤n)
-- rp-h2 {zero} {suc m} nle = s≤s z≤n
-- rp-h2 {suc n} {suc m} nle = s≤s (rp-h2 (λ m≤n → nle (s≤s m≤n)))

-- open import Relation.Nullary.Decidable
-- open import Function.Equivalence
-- open import Data.Bool.Properties hiding (≤-reflexive)

rp-h5 : {n : ℕ} →
  proj₂ (st 0F) n ≡ proj₂ (⟦ makeInstruction n ⟧i st 0F) n →
  ⟦ v[ 0F ] g[ Const n ] ⟧e st ≡ ⟦ v[ 0F ] g[ Const (suc n) ] ⟧e st
rp-h5 {st} {n} eq with n Data.Nat.≟ (suc n)
rp-h5 {st} {n} eq | no ¬p with n Data.Nat.≟ n
rp-h5 {st} {n} eq | no ¬p | yes p = eq
rp-h5 {st} {n} eq | no ¬p | no ¬p₁ = ⊥-elim (¬p₁ refl)

rp-h4 : {n : ℕ} →
  st ≡ ⟦ makeInstruction n ⟧i st →
  ⟦ v[ 0F ] g[ Const n ] ⟧e st ≡ ⟦ v[ 0F ] g[ Const (suc n) ] ⟧e st
rp-h4 {st} {n} eq = rp-h5 {st} (cong (λ z → (proj₂ (z 0F) n)) eq)
-- rp-h4 {st} {n} eq = rp-h5 {st} (cong (_$ n) (cong (_$ 0F) eq))

resultProof : {n : ℕ} →
  st ≡ ⟦ makePredicate n , [ makeInstruction n ] ⟧cb st →
  ⟦ Ordered' n ⟧a st
resultProof {st} {n} fp with (ci-helper {st} {makePredicate n} fp)
resultProof {st} {n} fp | inj₁ x with (≰⇒> x)
resultProof {st} {n} fp | inj₁ x | s≤s y = y
resultProof {st} {n} fp | inj₂ y = ≤-reflexive (rp-h4 y)

resultProof-n : {n : ℕ} → φ[ bubbleSort n ] ⇛ ⟦ Ordered n ⟧a
resultProof-n {zero} {st} [] = tt
resultProof-n {suc n} {st} (fp ∷ fps) =
  resultProof {st} {n} fp
  ,
  (resultProof-n {n} fps)
