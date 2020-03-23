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

  Union : (a b : ParallelProgram) → {s₀eq : proj₁ a ≡ proj₁ b} → ParallelProgram
  Union (a₀ , as) (b₀ , bs) = (a₀ , as ++ bs)

  ▷-Union-to : {s₀eq : proj₁ S1 ≡ proj₁ S2} → (P ▷[ S1 ] Q × P ▷[ S2 ] Q) → (P ▷[ Union S1 S2 {s₀eq} ] Q)
  ▷-Union-to {_ , []} (▷s1 , ▷s2) = ▷s2
  ▷-Union-to {_ , _ ∷ _} (▷s1 , ▷s2) (p , ⌝q) with ▷s1 (p , ⌝q)
  ▷-Union-to {s₀ , _ ∷ _} {s₀eq = s₀eq} (▷s1 , ▷s2) (p , ⌝q) | px ∷ x =
    px ∷ ▷-Union-to {s₀ , _} {s₀eq = s₀eq} (lessUnless {s₀ = s₀} ▷s1 , ▷s2) (p , ⌝q)

  ▷-Union-from-1 : {s₀eq : proj₁ S1 ≡ proj₁ S2} → (P ▷[ Union S1 S2 {s₀eq} ] Q) → (P ▷[ S1 ] Q)
  ▷-Union-from-1 {_ , []} ▷u = const []
  ▷-Union-from-1 {_ , _ ∷ _} ▷u (p , ⌝q) with ▷u (p , ⌝q)
  ▷-Union-from-1 {s₀ , _ ∷ _} {s₀eq = s₀eq} ▷u (p , ⌝q) | px ∷ x =
    px ∷ ▷-Union-from-1 {s₀ , _} {s₀eq = s₀eq} (lessUnless {s₀ = s₀} ▷u) (p , ⌝q)

  ▷-Union-from-2 : {s₀eq : proj₁ S1 ≡ proj₁ S2} → (P ▷[ Union S1 S2 {s₀eq} ] Q) → (P ▷[ S2 ] Q)
  ▷-Union-from-2 {_ , []} ▷u = ▷u
  ▷-Union-from-2 {_ , _ ∷ _} ▷u (p , ⌝q) with ▷u (p , ⌝q)
  ▷-Union-from-2 {s₀ , _ ∷ _} {s₀eq = s₀eq} ▷u (p , ⌝q) | px ∷ x =
    ▷-Union-from-2 {s₀ , _} {s₀eq = s₀eq} (lessUnless {s₀ = s₀} ▷u) (p , ⌝q)

  func-times-distr : {X : Set} → {A B C : X → Set} → ({x : X} → A x → (B x × C x)) → (({x : X} → A x → B x) × ({x : X} → A x → C x))
  func-times-distr f = ((λ a → proj₁ (f a)) , (λ a → proj₂ (f a)))

  func-times-distr-imp : {X : Set} → {A B C : X → Set} → ({x : X} → A x → (B x × C x)) → (({x : X} → A x → B x) × ({x : X} → A x → C x))
  func-times-distr-imp f = ((λ a → proj₁ (f a)) , (λ a → proj₂ (f a)))

  ▷-Union-from : (s₀eq : proj₁ S1 ≡ proj₁ S2) → (P ▷[ Union S1 S2 {s₀eq} ] Q) → (P ▷[ S1 ] Q × P ▷[ S2 ] Q)
  ▷-Union-from {_ , []} {_ , ss2} refl ▷u = ((const []) , ▷u)
  ▷-Union-from {_ , x ∷ ss1} {_ , ss2} refl ▷u =
    func-times-distr λ { (p , ⌝q) → {! with ...!} } -- (λ x₁ → {!!}) , (λ x₁ → {!!}) -- func-times {!!} {!!}

  -- func-times : {A B C : Set} → ((A → B) × (A → C)) → A → (B × C)
  -- func-times (f , g) a = (f a , g a)

  -- ▷-Union-from : (s₀eq : proj₁ S1 ≡ proj₁ S2) → (P ▷[ Union S1 S2 {s₀eq} ] Q) → (P ▷[ S1 ] Q × P ▷[ S2 ] Q)
  -- ▷-Union-from refl = λ x → {!!} , {!!}

  ▷-Union : {s₀eq : proj₁ S1 ≡ proj₁ S2} → (P ▷[ Union S1 S2 {s₀eq} ] Q) ↔ (P ▷[ S1 ] Q × P ▷[ S2 ] Q)
  ▷-Union {s₀ , _} {s₀eq = refl} =
    (
      λ x →
        (
          (▷-Union-from-1 {s₀ , _} {s₀eq = refl} x)
          ,
          (▷-Union-from-2 {s₀ , _} {s₀eq = refl} x)
        )
    )
    ,
    ▷-Union-to {s₀ , _} {s₀eq = refl}

  -- ▷-Union : P ▷[ S1 ] Q ↔ P ▷[ S2 ] Q
  -- ▷-Union =
  --   (λ x x₁ → {!!})
  --   ,
  --   (λ x x₁ → {!!})

  --

  -- ↦-Union : 
