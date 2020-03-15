open import Agda.Primitive
open import Data.Unit
open import Data.Bool
open import Data.Bool.Properties
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (True)
open import Relation.Binary.PropositionalEquality as Eq
open import Function

import Base
import Statements

module Constructions (varCount : ℕ) (varTypes : Fin varCount → Base.Types) where

  open module ProgramInstance = Base.Program varCount varTypes
  open module StatementsInstance = Statements varCount varTypes

  variable
    S1 S2 : ParallelProgram

  private
    infixr 0 _↔_
    _↔_ : ∀{i j}(A : Set i)(B : Set j) → Set (i ⊔ j)
    A ↔ B = (A → B) × (B → A)

  -- Page 81.
  -- Union : ((a₀ , as) : ParallelProgram) → ((b₀ , bs) : ParallelProgram) → (a₀ ≡ b₀) → ParallelProgram

  -- Union : (a b : ParallelProgram) → (proj₁ a ≡ proj₁ b) → ParallelProgram
  -- Union (a₀ , as) (b₀ , bs) Refl = (a₀ , as ++ bs)

  Union : (a b : ParallelProgram) → (proj₁ a ≡ proj₁ b) → ParallelProgram
  Union (a₀ , as) (b₀ , bs) Refl = (a₀ , as ++ bs)

  ▷-Union-to : (s₀eq : proj₁ S1 ≡ proj₁ S2) → (P ▷[ S1 ] Q × P ▷[ S2 ] Q) → (P ▷[ Union S1 S2 s₀eq ] Q)
  -- ▷-Union-to {_ , []} {_ , []} refl (s1 , s2) (p , ⌝q) = []
  ▷-Union-to {_ , []} {_ , S2s} refl (▷s1 , ▷s2) (p , ⌝q) = ▷s2 (p , ⌝q)
  ▷-Union-to {_ , s1 ∷ S1s} {_ , S2s} refl (▷s1 , ▷s2) (p , ⌝q) with ▷s1 (p , ⌝q)
  -- ▷-Union-to {_ , s1 ∷ S1s} {_ , []} refl (▷s1 , ▷s2) (p , ⌝q) | px ∷ x = px ∷ ▷-Union-to refl (lessUnless {s₀ = (TRUE , SKIP)} ▷s1 , ▷s2) (p , ⌝q)
  ▷-Union-to {s₀ , s1 ∷ S1s} {_ , S2s} refl (▷s1 , ▷s2) (p , ⌝q) | px ∷ x =
    px ∷ ▷-Union-to {s₀ , _} refl (lessUnless {s₀ = s₀} ▷s1 , ▷s2) (p , ⌝q)
  -- ▷-Union-to {_ , s1 ∷ S1s} {_ , s2 ∷ S2s} refl (▷s1 , ▷s2) (p , ⌝q) = {!!}

  ▷-Union-from-1 : (s₀eq : proj₁ S1 ≡ proj₁ S2) → (P ▷[ Union S1 S2 s₀eq ] Q) → (P ▷[ S1 ] Q)
  ▷-Union-from-1 {_ , []} refl ▷u (p , ⌝q) = []
  ▷-Union-from-1 {_ , s1 ∷ S1s} refl ▷u (p , ⌝q) with ▷u (p , ⌝q)
  ▷-Union-from-1 {s₀ , s1 ∷ S1s} refl ▷u (p , ⌝q) | px ∷ x =
    px ∷ ▷-Union-from-1 {s₀ , _} refl (lessUnless {s₀ = s₀} ▷u) (p , ⌝q)

  ▷-Union-from-2 : (s₀eq : proj₁ S1 ≡ proj₁ S2) → (P ▷[ Union S1 S2 s₀eq ] Q) → (P ▷[ S2 ] Q)
  ▷-Union-from-2 {_ , []} {_ , S2} refl ▷u (p , ⌝q) = ▷u (p , ⌝q)
  ▷-Union-from-2 {_ , s1 ∷ S1s} {_ , S2} refl ▷u (p , ⌝q) with ▷u (p , ⌝q)
  ▷-Union-from-2 {s₀ , s1 ∷ S1s} {_ , S2} refl ▷u (p , ⌝q) | px ∷ x =
    ▷-Union-from-2 {s₀ , _} refl (lessUnless {s₀ = s₀} ▷u) (p , ⌝q)

  -- ▷-Union-from-2 {_ , x ∷ S1} {_ , x₁ ∷ S2} refl ▷u (p , ⌝q) = {!!}
  -- ▷-Union-from-2 {_ , s1 ∷ S1s} refl ▷u (p , ⌝q) with ▷u (p , ⌝q)
  -- ▷-Union-from-2 {s₀ , s1 ∷ S1s} refl ▷u (p , ⌝q) | px ∷ x =
  --   px ∷ ▷-Union-from-1 {s₀ , _} refl (lessUnless {s₀ = s₀} ▷u) (p , ⌝q)

  -- ▷-Union : (s₀eq : proj₁ S1 ≡ proj₁ S2) → (P ▷[ Union S1 S2 s₀eq ] Q) → (P ▷[ S1 ] Q × P ▷[ S2 ] Q)
  -- ▷-Union refl u =
  --   (λ { (p , ⌝q) → {!!} })
  --   ,
  --   (λ { (p , ⌝q) → {!!} })

  ▷-Union : (s₀eq : proj₁ S1 ≡ proj₁ S2) → (P ▷[ Union S1 S2 s₀eq ] Q) ↔ (P ▷[ S1 ] Q × P ▷[ S2 ] Q)
  ▷-Union {s₀ , _} refl =
    (
      λ x →
        (
          (▷-Union-from-1 {s₀ , _} refl x)
          ,
          (▷-Union-from-2 {s₀ , _} refl x)
        )
    )
    ,
    ▷-Union-to  {s₀ , _} refl

  -- ▷-Union : P ▷[ S1 ] Q ↔ P ▷[ S2 ] Q
  -- ▷-Union =
  --   (λ x x₁ → {!!})
  --   ,
  --   (λ x x₁ → {!!})
