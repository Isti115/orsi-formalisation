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
open import Relation.Nullary.Decidable
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
    _↔_ : {i j : Level} (A : Set i) (B : Set j) → Set (i ⊔ j)
    A ↔ B = (A → B) × (B → A)

  -- Page 81.
  -- Union : ((a₀ , as) : ParallelProgram) → ((b₀ , bs) : ParallelProgram) → (a₀ ≡ b₀) → ParallelProgram

  -- Union : (a b : ParallelProgram) → {s₀eq : proj₁ a ≡ proj₁ b} → ParallelProgram
  -- Union (a₀ , as) (b₀ , bs) = (a₀ , as ++ bs)

  Union : (a b : ParallelProgram) → ParallelProgram
  Union a b = (a ++ b)

  ▷-Union-to : (P ▷[ S1 ] Q × P ▷[ S2 ] Q) → (P ▷[ Union S1 S2 ] Q)
  ▷-Union-to {S1 = []} (▷s1 , ▷s2) = ▷s2
  ▷-Union-to {S1 = _ ∷ _} (▷s1 , ▷s2) (p , ⌝q) with ▷s1 (p , ⌝q)
  ▷-Union-to {S1 = _ ∷ _} (▷s1 , ▷s2) (p , ⌝q) | px ∷ x =
    px ∷ ▷-Union-to (lessUnless ▷s1 , ▷s2) (p , ⌝q)

  ▷-Union-from-1 : (P ▷[ Union S1 S2 ] Q) → (P ▷[ S1 ] Q)
  ▷-Union-from-1 {S1 = []} ▷u = const []
  ▷-Union-from-1 {S1 = _ ∷ _} ▷u (p , ⌝q) with ▷u (p , ⌝q)
  ▷-Union-from-1 {S1 = _ ∷ _} ▷u (p , ⌝q) | px ∷ x =
    px ∷ ▷-Union-from-1 (lessUnless ▷u) (p , ⌝q)

  ▷-Union-from-2 : (P ▷[ Union S1 S2 ] Q) → (P ▷[ S2 ] Q)
  ▷-Union-from-2 {S1 = []} ▷u = ▷u
  ▷-Union-from-2 {S1 = _ ∷ _} ▷u (p , ⌝q) = ▷-Union-from-2 (lessUnless ▷u) (p , ⌝q)

  func-times-distr : {X : Set} → {A B C : X → Set} → ({x : X} → A x → (B x × C x)) → (({x : X} → A x → B x) × ({x : X} → A x → C x))
  func-times-distr f = ((λ a → proj₁ (f a)) , (λ a → proj₂ (f a)))

  func-times-distr-imp : {X : Set} → {A B C : X → Set} → ({x : X} → A x → (B x × C x)) → (({x : X} → A x → B x) × ({x : X} → A x → C x))
  func-times-distr-imp f = ((λ a → proj₁ (f a)) , (λ a → proj₂ (f a)))

  ▷-Union-from : (P ▷[ Union S1 S2 ] Q) → (P ▷[ S1 ] Q × P ▷[ S2 ] Q)
  ▷-Union-from {S1 = []} ▷u = ((const []) , ▷u)
  ▷-Union-from {S1 = _ ∷ _} ▷u =
    func-times-distr λ { (p , ⌝q) → {! with ...!} } -- (λ x₁ → {!!}) , (λ x₁ → {!!}) -- func-times {!!} {!!}

  -- func-times : {A B C : Set} → ((A → B) × (A → C)) → A → (B × C)
  -- func-times (f , g) a = (f a , g a)

  -- ▷-Union-from : (s₀eq : proj₁ S1 ≡ proj₁ S2) → (P ▷[ Union S1 S2 ] Q) → (P ▷[ S1 ] Q × P ▷[ S2 ] Q)
  -- ▷-Union-from refl = λ x → {!!} , {!!}

  ▷-Union : (P ▷[ Union S1 S2 ] Q) ↔ (P ▷[ S1 ] Q × P ▷[ S2 ] Q)
  ▷-Union = (λ x → ((▷-Union-from-1 x) , (▷-Union-from-2 x))) , ▷-Union-to

  --

  -- ↦-Union : 
