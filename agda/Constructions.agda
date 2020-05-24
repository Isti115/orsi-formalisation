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
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as Eq
open import Function hiding (_↔_)

import Base
import Statements

module Constructions (varCount : ℕ) (varTypes : Fin varCount → Base.Types) where

  open module ProgramInstance = Base.Environment varCount varTypes
  open module StatementsInstance = Statements varCount varTypes

  variable
    S₁ S₂ : ParallelProgram

  private
    infixr 0 _↔_
    _↔_ : {i j : Level} (A : Set i) (B : Set j) → Set (i ⊔ j)
    A ↔ B = (A → B) × (B → A)

  -- Page 81.
  -- Union : ((a₀ , as) : ParallelProgram) → ((b₀ , bs) : ParallelProgram) → (a₀ ≡ b₀) → ParallelProgram

  -- Union : (a b : ParallelProgram) → {s₀eq : proj₁ a ≡ proj₁ b} → ParallelProgram
  -- Union (a₀ , as) (b₀ , bs) = (a₀ , as ++ bs)

  Union : (S₁ S₂ : ParallelProgram) → ParallelProgram
  Union S₁ S₂ = (S₁ ++ S₂)

  infixr 4 _∪_
  _∪_ : (S₁ S₂ : ParallelProgram) → ParallelProgram
  S₁ ∪ S₂ = Union S₁ S₂

  ▷-Union-to : (P ▷[ S₁ ] Q × P ▷[ S₂ ] Q) → (P ▷[ S₁ ∪ S₂ ] Q)
  ▷-Union-to {S₁ = []} (▷s₁ , ▷s₂) = ▷s₂
  ▷-Union-to {S₁ = _ ∷ _} (▷s₁ , ▷s₂) (p , ⌝q) with ▷s₁ (p , ⌝q)
  ▷-Union-to {S₁ = _ ∷ _} (▷s₁ , ▷s₂) (p , ⌝q) | px ∷ x =
    px ∷ ▷-Union-to (lessUnless ▷s₁ , ▷s₂) (p , ⌝q)

  ▷-Union-from-1 : (P ▷[ S₁ ∪ S₂ ] Q) → (P ▷[ S₁ ] Q)
  ▷-Union-from-1 {S₁ = []} ▷u = const []
  ▷-Union-from-1 {S₁ = _ ∷ _} ▷u (p , ⌝q) with ▷u (p , ⌝q)
  ▷-Union-from-1 {S₁ = _ ∷ _} ▷u (p , ⌝q) | px ∷ x =
    px ∷ ▷-Union-from-1 (lessUnless ▷u) (p , ⌝q)

  ▷-Union-from-2 : (P ▷[ S₁ ∪ S₂ ] Q) → (P ▷[ S₂ ] Q)
  ▷-Union-from-2 {S₁ = []} ▷u = ▷u
  ▷-Union-from-2 {S₁ = _ ∷ _} ▷u (p , ⌝q) = ▷-Union-from-2 (lessUnless ▷u) (p , ⌝q)

  func-times-distr : {X : Set} → {A B C : X → Set} → ({x : X} → A x → (B x × C x)) → (({x : X} → A x → B x) × ({x : X} → A x → C x))
  func-times-distr f = ((λ a → proj₁ (f a)) , (λ a → proj₂ (f a)))

  func-times-distr-imp : {X : Set} → {A B C : X → Set} → ({x : X} → A x → (B x × C x)) → (({x : X} → A x → B x) × ({x : X} → A x → C x))
  func-times-distr-imp f = ((λ a → proj₁ (f a)) , (λ a → proj₂ (f a)))

  -- ▷-Union-from : (P ▷[ Union S₁ S₂ ] Q) → (P ▷[ S₁ ] Q × P ▷[ S₂ ] Q)
  -- ▷-Union-from {S₁ = []} ▷u = ((const []) , ▷u)
  -- ▷-Union-from {S₁ = _ ∷ _} ▷u =
  --   func-times-distr λ { (p , ⌝q) → {! with ...!} } -- (λ x₁ → {!!}) , (λ x₁ → {!!}) -- func-times {!!} {!!}

  -- func-times : {A B C : Set} → ((A → B) × (A → C)) → A → (B × C)
  -- func-times (f , g) a = (f a , g a)

  -- ▷-Union-from : (s₀eq : proj₁ S₁ ≡ proj₁ S₂) → (P ▷[ Union S₁ S₂ ] Q) → (P ▷[ S₁ ] Q × P ▷[ S₂ ] Q)
  -- ▷-Union-from refl = λ x → {!!} , {!!}

  ▷-Union : (P ▷[ S₁ ∪ S₂ ] Q) ↔ (P ▷[ S₁ ] Q × P ▷[ S₂ ] Q)
  ▷-Union = (λ x → ((▷-Union-from-1 x) , (▷-Union-from-2 x))) , ▷-Union-to

-- 1 ≡ 2 ↔ 2 ≡ 1

  --

  -- ↦-Union : 
