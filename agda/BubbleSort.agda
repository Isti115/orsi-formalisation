open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Fin hiding (_≤_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])

module BubbleSort where

import Base
import Statements

varTypes : Fin 1 → Base.Types
varTypes = (λ n → Base.Array Base.Nat)

open module ListNatOnlyBase = Base.Program 1 varTypes
open module ListNatOnlyStatements = Statements 1 varTypes

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
    GT (v[ 0F ] g[ Const n ]) (v[ 0F ] g[ Const (suc n) ])
  )

makeInstruction : ℕ → Instruction
makeInstruction n = (
    Assignment [(
      0F
      ,
      (
        v[ 0F ]
        s[ Const n ]=(v[ 0F ] g[ Const (suc n) ])
        s[ Const (suc n) ]=(v[ 0F ] g[ Const n ])
      )
    )]
  )

bubbleSort : ℕ → ParallelProgram
bubbleSort count =
  (
    Data.List.map
      (λ x → (makePredicate x , makeInstruction x))
      (downFrom count)
      -- GT (GetListNat (Const x) (Var 0)) ((GetListNat (Const (x + 1)) (Var 0)))
    -- )) (range 1 count)
    -- )) (Data.List.filter (λ y → 0 Data.Nat.<? y) (downFrom count))
  )


-- module Proof where

--   open module Implementation

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
helper {st} (before , after) gt with ((st 0F) 1)
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
After' = EQ (v[ 0F ] g[ Const 1 ]) (Const 0)

helper' :
  (st ⊢ (Before △ ⌝ After')) →
  ⟦ makePredicate 0 ⟧a st →
  ⟦ makeInstruction 0 ⟧i st ⊢ (Before ▽ After')
helper' {st} (before , after) gt with ((st 0F) 1)
helper' {st} (before , after) gt | zero = ⊥-elim (after refl)
helper' {st} (before , after) gt | suc x rewrite before = ⊥-elim (h1 gt)

test2' : Before ▷[ bubbleSort 1 ] After'
test2' {st} =
  ▷-proof
    {Before}
    {After'}
    ((λ {st} → helper' {st}) ∷ [])
--

Ordered' : ℕ → Predicate
Ordered' n = LTE (v[ 0F ] g[ Const n ]) (v[ 0F ] g[ Const (suc n) ])

Ordered : ℕ → Predicate
Ordered zero = TRUE
Ordered (suc n) = Ordered' n △ (Ordered n)

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
--   ⟦ v[ 0F ] g[ Const n ] ⟧e st ≡ ⟦ v[ 0F ] g[ Const (suc n) ] ⟧e st
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
  ⟦ v[ 0F ] g[ Const 0 ] ⟧e st ≡ ⟦ v[ 0F ] g[ Const 1 ] ⟧e st
rp-h3' = cong (_$ 0F) ∘ (cong (_$ 0F))
-- rp-h3' {st} eq = (fx' 0 (fx' 0 eq))

open import Relation.Nullary.Decidable
open import Function.Equivalence
open import Data.Bool.Properties hiding (≤-reflexive)

-- rp-h4 : {n : ℕ} →
--   st ≡ ⟦ makeInstruction n ⟧i st →
--   ⟦ v[ 0F ] g[ Const n ] ⟧e st ≡ ⟦ v[ 0F ] g[ Const (suc n) ] ⟧e st
-- rp-h4 {st} {n} eq with (
--          -- Relation.Nullary.Decidable.map
--          -- (Function.Equivalence.equivalence (≡ᵇ⇒≡ n (suc n))
--          --  (≡⇒≡ᵇ n (suc n)))
--          -- (Data.Bool.Properties.T? (n ≡ᵇ suc n))
--          Relation.Nullary.Decidable.map
--            (equivalence (≡ᵇ⇒≡ n (suc n)) (≡⇒≡ᵇ n (suc n)))
--            (T? (n ≡ᵇ suc n))

--      )
-- rp-h4 {st} {n} eq | no ¬p = {!cong (_$ n) (cong (_$ 0) eq)!}

rp-h5 : {n : ℕ} →
  st 0F n ≡ ⟦ makeInstruction n ⟧i st 0F n →
  ⟦ v[ 0F ] g[ Const n ] ⟧e st ≡ ⟦ v[ 0F ] g[ Const (suc n) ] ⟧e st
rp-h5 {st} {n} eq with n Data.Nat.≟ (suc n)
rp-h5 {st} {n} eq | no ¬p with n Data.Nat.≟ n
rp-h5 {st} {n} eq | no ¬p | yes p = eq
rp-h5 {st} {n} eq | no ¬p | no ¬p₁ = ⊥-elim (¬p₁ refl)

rp-h4 : {n : ℕ} →
  st ≡ ⟦ makeInstruction n ⟧i st →
  ⟦ v[ 0F ] g[ Const n ] ⟧e st ≡ ⟦ v[ 0F ] g[ Const (suc n) ] ⟧e st
rp-h4 {st} {n} eq = rp-h5 {st} (cong (_$ n) (cong (_$ 0F) eq))
-- rp-h4 {st} {n} eq
--   with (cong (_$ n) (cong (_$ 0) eq))
--   -- | n Data.Nat.≟ (suc n)
--   |   Relation.Nullary.Decidable.map
--       (Function.Equivalence.equivalence (≡ᵇ⇒≡ n (suc n))
--       (≡⇒≡ᵇ n (suc n)))
--       (Data.Bool.Properties.T? (n ≡ᵇ suc n))
-- rp-h4 {st} {n} eq | eq' | no ¬p = {!!}
-- rp-h4 {st} {n} eq | no ¬p = {!cong (_$ n) (cong (_$ 0) eq)!}

-- rp-h4 {st} {n} eq with n Data.Nat.≟ (suc n)
-- rp-h4 {st} {n} eq | no ¬p = {!cong (_$ n) (cong (_$ 0) eq)!}
-- ... | asdf = {!cong (_$ n) (cong (_$ 0) eq)!}

-- fx :
--   {f g : ℕ → ℕ} → {n : ℕ} →
--   (f ≡ g) → (f n ≡ g n)
-- fx refl = refl

-- rp-h3' :
--   st ≡ ⟦ makeInstruction 0 ⟧i st →
--   ⟦ v[ 0F ] g[ Const 0 ] ⟧e st ≡ ⟦ v[ 0F ] g[ Const 1 ] ⟧e st
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

resultProof' : {n : ℕ} →
  st ≡ ⟦ makePredicate n , makeInstruction n ⟧ci st →
  ⟦ Ordered' n ⟧a st
resultProof' {st} {n} fp with (ci-helper {st} {makePredicate n} fp)
resultProof' {st} {n} fp | inj₁ x with (≰⇒> x)
resultProof' {st} {n} fp | inj₁ x | s≤s y = y
resultProof' {st} {n} fp | inj₂ y = ≤-reflexive (rp-h4 y)
  -- {! (cong (_$ n) (cong (_$ 0) y))!}
  -- {!  ≤-reflexive (cong (_$ n) (cong (_$ n) y))!}

resultProof-2 : φ[ bubbleSort 2 ] ⇛ ⟦ Ordered 2 ⟧a
resultProof-2 {st} (fp1 ∷ fp2 ∷ []) =
  resultProof' fp1 , (resultProof' fp2 , tt)
-- resultProof-2 {st} (fp1 ∷ fp2 ∷ []) with (ci-helper {st} {makePredicate 0} fp1)
-- resultProof-2 {st} (fp1 ∷ fp2 ∷ []) | inj₁ x with (≰⇒> x)
-- resultProof-2 {st} (fp1 ∷ fp2 ∷ []) | inj₁ x | s≤s z = (z , tt)
-- resultProof-2 {st} (fp1 ∷ fp2 ∷ []) | inj₂ y =
--   (≤-reflexive (rp-h3' y) , tt)

resultProof-n : {n : ℕ} → φ[ bubbleSort n ] ⇛ ⟦ Ordered n ⟧a
resultProof-n {zero} {st} [] = tt
resultProof-n {suc n} {st} (fp ∷ fps) =
  resultProof' {st} {n} fp
  ,
  (resultProof-n {n} fps)
  -- resultProof' fp1 , (resultProof' fp2 , tt)
