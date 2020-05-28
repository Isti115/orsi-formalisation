-- module Statements where

-- {-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Bool
open import Data.Bool.Properties
open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (True)
open import Relation.Binary.PropositionalEquality as Eq
open import Function

open import Base
-- open module NatOnly = Base.Environment (λ n → Nat)

module Statements (varCount : ℕ) (varTypes : Fin varCount → Types) where

  open module ProgramInstance = Base.Environment varCount varTypes

  ⌝_ : Predicate → Predicate
  ⌝_ = NOT

  infixr 6 _△_
  _△_ : Predicate → Predicate → Predicate
  _△_ = AND

  infixr 5 _▽_
  _▽_ : Predicate → Predicate → Predicate
  _▽_ = OR

  -- open Base.NatOnly using (NatOnly)

  -- postulate
  --   VarTypes : ℕ → Types
  --
  -- module ProgramInstance = Base.Program VarTypes
  -- open ProgramInstance

  variable
    P P₁ Q Q₁ R V K : Predicate
    A B : Assertion
    C D : Condition
    W X Y Z : Set
    st : State
    i : Instruction
    -- s₀ il : List Instruction
    s₀ b : Batch
    cb : ConditionalBatch
    cbs : List ConditionalBatch
    S : ParallelProgram
    I : InitializedProgram

  Statement : Set₁
  Statement = Set

  --


  -- Predicate implication
  infix 4 _⇒_
  _⇒_ : Predicate → Predicate → Statement
  P ⇒ Q = ∀{st : State} → st ⊢ P → st ⊢ Q

  infix 4 _⇐_
  _⇐_ : Predicate → Predicate → Statement
  P ⇐ Q = Q ⇒ P

  ⇒-Reflexive : P ⇒ P
  ⇒-Reflexive p = p

  ⇒-⌝-Reverse : (P ⇒ Q) → ((⌝ Q) ⇒ (⌝ P))
  ⇒-⌝-Reverse p⇒q = λ ⌝q p → ⌝q (p⇒q p)

  ⇐-Reflexive : P ⇐ P
  ⇐-Reflexive p = p

  ⇐-⌝-Reverse : (P ⇐ Q) → ((⌝ Q) ⇐ (⌝ P))
  ⇐-⌝-Reverse p⇐q = λ ⌝p q → ⌝p (p⇐q q)

  -- Predicate Equivalence
  infix 4 _⇐⇒_
  _⇐⇒_ : Predicate → Predicate → Statement
  P ⇐⇒ Q = (P ⇒ Q) × (P ⇐ Q)

  ⇐⇒Symmetric : (P ⇐⇒ Q) → (Q ⇐⇒ P)
  ⇐⇒Symmetric (p⇒q , p⇐q) = (p⇐q , p⇒q)

  ⇐⇒-⌝-Compatible : (P ⇐⇒ Q) → ((⌝ P) ⇐⇒ (⌝ Q))
  ⇐⇒-⌝-Compatible (p⇒q , p⇐q) = ((⇒-⌝-Reverse p⇐q) , (⇒-⌝-Reverse p⇒q))


  -- Assertion implication

  infix 4 _⇛_
  _⇛_ : Assertion → Assertion → Statement
  A ⇛ B = ∀{st : State} → st ⊩ A → st ⊩ B

  infix 4 _⇚_
  _⇚_ : Assertion → Assertion → Statement
  A ⇚ B = B ⇛ A

  infix 4 _⇚⇛_
  _⇚⇛_ : Assertion → Assertion → Statement
  A ⇚⇛ B = (A ⇛ B) × (A ⇚ B)

  ⇚⇛-Symmetric : (A ⇚⇛ B) → (A ⇚⇛ B)
  ⇚⇛-Symmetric (a⇛b , b⇚a) = (a⇛b , b⇚a)

  ⇒-to-⇛ : P ⇒ Q → ⟦ P ⟧a ⇛ ⟦ Q ⟧a
  ⇒-to-⇛ = id
  -- ⇒-to-⇛ p⇒q = λ p → p⇒q p

  ⇛-to-⇒ : ⟦ P ⟧a ⇛ ⟦ Q ⟧a → P ⇒ Q
  ⇛-to-⇒ = id
  -- ⇛-to-⇒ p⇒q = λ p → p⇒q p

  --

  →Disjunctive : (Z → X ⊎ Y) → ((X → W) × (Y → W)) → (Z → W)
  →Disjunctive z→x⊎y (x→z , y→z) z with (z→x⊎y z)
  →Disjunctive z→x⊎y (x→z , y→z) z | inj₁ x = x→z x
  →Disjunctive z→x⊎y (x→z , y→z) z | inj₂ y = y→z y

  ⇒Disjunctive : (R ⇒ P ▽ Q) → (P ⇒ V × Q ⇒ V) → (R ⇒ V)
  ⇒Disjunctive r⇒p▽q (p⇒b , q⇒b) r with (r⇒p▽q r)
  ⇒Disjunctive r⇒p▽q (p⇒b , q⇒b) r | inj₁ p = p⇒b p
  ⇒Disjunctive r⇒p▽q (p⇒b , q⇒b) r | inj₂ q = q⇒b q

  ⇛Disjunctive : (R ⇒ P ▽ Q) → (⟦ P ⟧a ⇛ A × ⟦ Q ⟧a ⇛ A) → (⟦ R ⟧a ⇛ A)
  ⇛Disjunctive r⇒p▽q (p⇛a , q⇛a) r with (r⇒p▽q r)
  ⇛Disjunctive r⇒p▽q (p⇛a , q⇛a) r | inj₁ p = p⇛a p
  ⇛Disjunctive r⇒p▽q (p⇛a , q⇛a) r | inj₂ q = q⇛a q

  --

  orCommutative : P ▽ Q ⇒ Q ▽ P
  orCommutative (inj₁ p) = inj₂ p
  orCommutative (inj₂ q) = inj₁ q

  andCommutative : P △ Q ⇒ Q △ P
  andCommutative (p , q) = (q , p)

  --

  weaken : P ⇒ P ▽ Q
  weaken = inj₁

  strenghten : P △ Q ⇒ P
  strenghten = proj₁

  impliesOrLeft : P ⇒ R → P ▽ Q ⇒ R ▽ Q
  impliesOrLeft p⇒r (inj₁ p) = inj₁ (p⇒r p)
  impliesOrLeft p⇒r (inj₂ q) = inj₂ q

  impliesOrRight : Q ⇒ R → P ▽ Q ⇒ P ▽ R
  impliesOrRight q⇒r = orCommutative ∘ impliesOrLeft q⇒r ∘ orCommutative

  impliesAndLeft : P ⇒ R → P △ Q ⇒ R △ Q
  impliesAndLeft p⇒r (p , q) = (p⇒r p , q)

  impliesAndRight : Q ⇒ R → P △ Q ⇒ P △ R
  impliesAndRight q⇒r = andCommutative ∘ impliesAndLeft q⇒r ∘ andCommutative

  --

  weakenOrLeft : P ▽ Q ⇒ (P ▽ R) ▽ Q
  weakenOrLeft = impliesOrLeft weaken

  weakenOrRight : P ▽ Q ⇒ P ▽ (Q ▽ R)
  weakenOrRight = impliesOrRight weaken

  strenghtenOrLeft : (P △ R) ▽ Q ⇒ P ▽ Q
  strenghtenOrLeft = impliesOrLeft strenghten

  strenghtenOrRight : P ▽ (Q △ R) ⇒ P ▽ Q
  strenghtenOrRight = impliesOrRight strenghten

  weakenAndLeft : P △ Q ⇒ (P ▽ R) △ Q
  weakenAndLeft = impliesAndLeft weaken

  weakenAndRight : P △ Q ⇒ P △ (Q ▽ R)
  weakenAndRight = impliesAndRight weaken

  strenghtenAndLeft : (P △ R) △ Q ⇒ P △ Q
  strenghtenAndLeft = impliesAndLeft strenghten

  strenghtenAndRight : P △ (Q △ R) ⇒ P △ Q
  strenghtenAndRight = impliesAndRight strenghten

  --

  impliesTrans : (P ⇒ Q) → (Q ⇒ R) → (P ⇒ R)
  impliesTrans p⇒q q⇒r p = q⇒r (p⇒q p)

  strenghtenImpliesLeft : (P ⇒ Q) → (P △ R ⇒ Q)
  strenghtenImpliesLeft p⇒q p∧r = p⇒q (proj₁ p∧r)

  weakenImpliesRight : (P ⇒ Q) → (P ⇒ Q ▽ R)
  weakenImpliesRight p⇒q p = inj₁ (p⇒q p)

  -- Distributivity

  andDistributiveToLeft : (P △ (Q ▽ R)) ⇒ ((P △ Q) ▽ (P △ R))
  andDistributiveToLeft (p , inj₁ q) = inj₁ (p , q)
  andDistributiveToLeft (p , inj₂ r) = inj₂ (p , r)

  andDistributiveFromLeft : (P △ (Q ▽ R)) ⇐ ((P △ Q) ▽ (P △ R))
  andDistributiveFromLeft (inj₁ (p , q)) = (p , inj₁ q)
  andDistributiveFromLeft (inj₂ (p , r)) = (p , inj₂ r)

  andDistributiveLeft : (P △ (Q ▽ R)) ⇐⇒ ((P △ Q) ▽ (P △ R))
  andDistributiveLeft = (andDistributiveToLeft , andDistributiveFromLeft)

  --

  andDistributiveToRight : ((P ▽ Q) △ R) ⇒ ((P △ R) ▽ (Q △ R))
  andDistributiveToRight (inj₁ p , r) = inj₁ (p , r)
  andDistributiveToRight (inj₂ q , r) = inj₂ (q , r)

  andDistributiveFromRight : ((P ▽ Q) △ R) ⇐ ((P △ R) ▽ (Q △ R))
  andDistributiveFromRight (inj₁ (p , r)) = (inj₁ p , r)
  andDistributiveFromRight (inj₂ (q , r)) = (inj₂ q , r)

  andDistributiveRight : ((P ▽ Q) △ R) ⇐⇒ ((P △ R) ▽ (Q △ R))
  andDistributiveRight = (andDistributiveToRight , andDistributiveFromRight)

  --

  orDistributiveToLeft : (P ▽ (Q △ R)) ⇒ ((P ▽ Q) △ (P ▽ R))
  orDistributiveToLeft (inj₁ p) = (inj₁ p , inj₁ p)
  orDistributiveToLeft (inj₂ (q , r)) = (inj₂ q , inj₂ r)

  orDistributiveFromLeft : (P ▽ (Q △ R)) ⇐ ((P ▽ Q) △ (P ▽ R))
  orDistributiveFromLeft (inj₁ p , p∨r) = inj₁ p
  orDistributiveFromLeft (inj₂ q , inj₁ p) = inj₁ p
  orDistributiveFromLeft (inj₂ q , inj₂ r) = inj₂ (q , r)

  orDistributiveLeft : (P ▽ (Q △ R)) ⇐⇒ ((P ▽ Q) △ (P ▽ R))
  orDistributiveLeft = (orDistributiveToLeft , orDistributiveFromLeft)

  --

  orDistributiveToRight : ((P △ Q) ▽ R) ⇒ ((P ▽ R) △ (Q ▽ R))
  orDistributiveToRight (inj₁ (p , q)) = (inj₁ p , inj₁ q)
  orDistributiveToRight (inj₂ r) = (inj₂ r , inj₂ r)

  orDistributiveFromRight : ((P △ Q) ▽ R) ⇐ ((P ▽ R) △ (Q ▽ R))
  orDistributiveFromRight (inj₂ r , q∨r) = inj₂ r
  orDistributiveFromRight (inj₁ p , inj₂ r) = inj₂ r
  orDistributiveFromRight (inj₁ p , inj₁ q) = inj₁ (p , q)

  orDistributiveRight : ((P △ Q) ▽ R) ⇐⇒ ((P ▽ R) △ (Q ▽ R))
  orDistributiveRight = (orDistributiveToRight , orDistributiveFromRight)


  -- De Morgan

  notOrToAndNotNot : ⌝ (P ▽ Q) ⇒ (⌝ P) △ (⌝ Q)
  notOrToAndNotNot ¬_p∨q_ = ((¬_p∨q_ ∘ inj₁) , (¬_p∨q_ ∘ inj₂))

  notAndToOrNotNot : ⌝ (P △ Q) ⇒ (⌝ P) ▽ (⌝ Q)
  notAndToOrNotNot {P} ¬_p∧q_ with assertionDecidability P
  notAndToOrNotNot ¬_p∧q_ | inj₁ ¬p = inj₁ ¬p
  notAndToOrNotNot ¬_p∧q_ | inj₂ p = inj₂ (λ q → ¬_p∧q_ (p , q))

  --

  allImplies : {A : Set} → {f g : A → Set} → {l : List A} → ({a : A} → f a → g a) → All f l → All g l
  allImplies fa→ga [] = []
  allImplies fa→ga (fl ∷ fls) = (fa→ga fl) ∷ (allImplies fa→ga fls)

  anyImplies : {A : Set} → {f g : A → Set} → {l : List A} → ({a : A} → f a → g a) → Any f l → Any g l
  anyImplies fa→ga (here hl) = here (fa→ga hl)
  anyImplies fa→ga (there tl) = there (anyImplies fa→ga tl)

  --

  -- Weakest Precondition

  IWP : (Instruction × Predicate) → Assertion
  IWP (i , P) = λ st → (⟦ i ⟧i st) ⊢ P

  BWP : (Batch × Predicate) → Assertion
  BWP (b , P) = λ st → (⟦ b ⟧b st) ⊢ P

  CBWP : (ConditionalBatch × Predicate) → Assertion
  CBWP (cb , P) = λ st → (⟦ cb ⟧cb st) ⊢ P

  CBLWP : (ParallelProgram × Predicate) → Assertion
  CBLWP (S , P) = λ st → All (λ cb → st ⊩ (CBWP (cb , P))) S

  IWP-⇒-Compatible : P ⇒ Q → IWP (i , P) ⇛ IWP (i , Q)
  IWP-⇒-Compatible p⇒q wp = p⇒q wp

  IWP-⇐-Compatible : P ⇐ Q → IWP (i , P) ⇚ IWP (i , Q)
  IWP-⇐-Compatible p⇐q wp = p⇐q wp

  --

  impliesBCWP : P ⇒ Q → (CBWP (cb , P)) ⇛ (CBWP (cb , Q))
  impliesBCWP p⇒q Cbwp = p⇒q Cbwp

  lessCBLWP : CBLWP ((cb ∷ cbs) , P) ⇛ CBLWP (cbs , P)
  lessCBLWP (ci_prf ∷ cils_prfs) = cils_prfs

  -- moreCBLWP : ⟦ CBWP (cb , P) ⟧a → CBLWP (cbs , P) ⇛ CBLWP ((cb ∷ cbs) , P)
  -- moreCBLWP Cbwp cBLwp = ?

  impliesCBLWP : P ⇒ Q → CBLWP (S , P) ⇛ CBLWP (S , Q)
  impliesCBLWP p⇒q [] = []
  impliesCBLWP p⇒q (ci_prf ∷ cils_prfs) = p⇒q ci_prf ∷ impliesCBLWP p⇒q cils_prfs

  lessImpliesCBLWP : (⟦ P ⟧a ⇛ (CBLWP ((cb ∷ cbs) , Q))) → (⟦ P ⟧a ⇛ (CBLWP (cbs , Q)))
  lessImpliesCBLWP p⇛pbcwp = λ p → lessCBLWP (p⇛pbcwp p)

  --

  -- Strongest Postcondition

  ISP : (Instruction × Predicate) → Assertion
  ISP (i , P) = λ st → Σ State (λ st₀ → st₀ ⊢ P → ⟦ i ⟧i st₀ ≡ st)

  BSP : (Batch × Predicate) → Assertion
  BSP (b , P) = λ st → Σ State (λ st₀ → st₀ ⊢ P → ⟦ b ⟧b st₀ ≡ st)

  CBSP : (ConditionalBatch × Predicate) → Assertion
  CBSP (cb , P) = λ st → Σ State (λ st₀ → st₀ ⊢ P → ⟦ cb ⟧cb st₀ ≡ st)

  CBLSP : (ParallelProgram × Predicate) → Assertion
  CBLSP (S , P) = λ st → All (λ cb → st ⊩ (CBSP (cb , P))) S

  --

  Unless : ParallelProgram → Predicate → Predicate → Statement
  Unless S P Q = ⟦ (P △ (⌝ Q)) ⟧a ⇛ (CBLWP (S , P ▽ Q))

  infix 4 _▷[_]_
  _▷[_]_ : Predicate → ParallelProgram → Predicate → Statement
  P ▷[ S ] Q = Unless S P Q

  ▷-Reflexive : P ▷[ S ] P
  ▷-Reflexive (p , ¬p) = ⊥-elim (¬p p)

  ▷-from-⇒ : P ⇒ Q → P ▷[ S ] Q
  ▷-from-⇒ p⇒q (p , ⌝q) = ⊥-elim (⌝q (p⇒q p))

  ▷-⇐⇒-left : P ⇐⇒ Q → P ▷[ S ] R → Q ▷[ S ] R
  ▷-⇐⇒-left (p⇒q , p⇐q) p▷[s]r (q , ¬r) =
    impliesCBLWP (impliesOrLeft p⇒q) (p▷[s]r (p⇐q q , ¬r))


  lessUnless : (P ▷[ cb ∷ cbs ] Q) → (P ▷[ cbs ] Q)
  lessUnless p▷[cb∷cbs]q = λ p△⌝q → lessCBLWP (p▷[cb∷cbs]q p△⌝q)

  impliesUnlessRight : Q ⇒ R → (P ▷[ S ] Q) → (P ▷[ S ] R)
  impliesUnlessRight q⇒r p▷[s]q (p , ¬r) =
    impliesCBLWP (λ { (inj₁ p) → inj₁ p ; (inj₂ q) → inj₂ (q⇒r q) }) (p▷[s]q (p , ¬r ∘ q⇒r))

  -- impliesUnlessRight : Q ⇒ R → (P ▷[ S ] Q) → (P ▷[ S ] R)
  -- impliesUnlessRight q⇒r p▷[s]q (p , ⌝r) with (p▷[s]q (p , (λ q → ⌝r (q⇒r q))))
  -- ... | [] = []
  -- ... | inj₁ p_ ∷ rest = inj₁ p_ ∷ impliesUnlessRight q⇒r (lessUnless p▷[s]q) (p , ⌝r)
  -- ... | inj₂ q_ ∷ rest = (inj₂ (q⇒r q_ )) ∷ impliesUnlessRight q⇒r (lessUnless p▷[s]q) (p , ⌝r)

  weakenUnlessRight' : Q ⇒ R → (P ▷[ S ] Q) → (P ▷[ S ] (Q ▽ R))
  weakenUnlessRight' q⇒r p∧¬q⇛pbcwp (p , ¬_q∨r_) =
    impliesCBLWP weakenOrRight ((p∧¬q⇛pbcwp (p , (¬_q∨r_ ∘ inj₁))))

  weakenUnlessRight : (P ▷[ S ] Q) → (P ▷[ S ] (Q ▽ R))
  weakenUnlessRight = impliesUnlessRight weaken

  -- weakenUnlessRight : (P ▷[ S ] Q) → (P ▷[ S ] (OR Q R))
  -- weakenUnlessRight {P} {Q = Q} p∧¬q⇛pbcwp (p , ¬_q∨r_) =
  --   impliesCBLWP weakenOrRight (p∧¬q⇛pbcwp (p , (¬_q∨r_ ∘ inj₁)))
    -- λ { (p , ¬_q∨r_) → impliesCBLWP {OR P Q} weakenOrRight (p∧¬q⇛pbcwp (p , (λ q → ¬_q∨r_ (inj₁ q)) }

  unlessDisjunctive : ((P ▷[ S ] R) × (Q ▷[ S ] R)) → (P ▽ Q ▷[ S ] R)
  unlessDisjunctive (p▷[s]r , q▷[s]r) (inj₁ p , ⌝r) =
    impliesCBLWP (impliesOrLeft weaken) (p▷[s]r (p , ⌝r))
  unlessDisjunctive (p▷[s]r , q▷[s]r) (inj₂ q , ⌝r) =
    impliesCBLWP (impliesOrLeft (orCommutative ∘ weaken)) (q▷[s]r (q , ⌝r))

  -- FALSE
  -- impliesUnlessLeft : P ⇒ Q → Q ▷[ S ] R → P ▷[ S ] R
  -- impliesUnlessLeft p⇒q q▷[s]r (p , ⌝r) with q▷[s]r (p⇒q p , ⌝r)
  -- ... | [] = []
  -- ... | inj₁ q_ ∷ rest = {!   !} ∷ (impliesUnlessLeft p⇒q (lessUnless q▷[s]r) ((p , ⌝r)))
  -- ... | inj₂ r_ ∷ rest = (inj₂ r_) ∷ (impliesUnlessLeft p⇒q (lessUnless q▷[s]r) ((p , ⌝r)))

  unlessFromImplies : (P ⇒ Q) → (P ▷[ S ] Q)
  -- unlessFromImplies p⇒q (p , ¬q) = ⊥-elim (¬q (p⇒q p))
  unlessFromImplies p⇒q = impliesUnlessRight p⇒q ▷-Reflexive

  --

  ▷-proofHelper :
    (st ⊢ (P △ ⌝ Q)) →
    (⟦ R ⟧a st → (⟦ b ⟧b st) ⊢ (P ▽ Q)) →
    ((⟦ (R , b) ⟧cb st) ⊢ (P ▽ Q))
  ▷-proofHelper {st = st} {R = R} pq f with (⟦ R ⟧d st)
  ▷-proofHelper pq f | yes p = f p
  ▷-proofHelper pq f | no ¬p = inj₁ (proj₁ pq)

  -- ▷-proofHelper {st} {P} {Q} {R} {i} pq f with (⟦ R ⟧C st)
  -- ▷-proofHelper {st} {P} {Q} {R} {i} pq f | false = inj₁ (proj₁ pq)
  -- ▷-proofHelper {st} {P} {Q} {R} {i} pq f | true = f refl

  ▷-proof :
    (All (λ { (R , b) →
      ({st : State} → st ⊢ (P △ ⌝ Q) → ⟦ R ⟧a st → (⟦ b ⟧b st) ⊢ (P ▽ Q))
    }) S) →
    P ▷[ S ] Q
  ▷-proof [] (p , ⌝q) = []
  ▷-proof (prf ∷ prfs) (p , ⌝q) =
    ▷-proofHelper (p , ⌝q) (prf (p , ⌝q))
      ∷ (▷-proof prfs (p , ⌝q))

  --

  Stable : ParallelProgram → Predicate → Statement
  Stable S P = P ▷[ S ] FALSE

  -- allImplies : {A : Set} → {f g : A → Set} → (∀ a → f a → g a) → {as : List A} → All f as → All g as
  -- allImplies f→g {as = []} allf = []
  -- allImplies f→g {as = a ∷ as} (fa ∷ allf) = f→g a fa ∷ allImplies f→g allf

  allImplies2 : {A : Set} → {f g h : A → Set} → ({a : A} → f a → g a → h a) → {as : List A} → All f as → All g as → All h as
  allImplies2 f→g→h [] [] = []
  allImplies2 f→g→h (px ∷ allf) (px₁ ∷ allg) = f→g→h px px₁ ∷ allImplies2 f→g→h allf allg

  intersectUnlessWithStable : Stable S K → P ▷[ S ] Q → (P △ K) ▷[ S ] (Q △ K)
  intersectUnlessWithStable {S = []} _ _ _ = []
  intersectUnlessWithStable {S = cb ∷ cbs}
    {Q = Q} stable p▷[s]q {st = st} ((p , k) , ⌝q△k) with assertionDecidability Q
  ... | inj₁ ⌝q with (p▷[s]q (p , ⌝q)) | (stable (k , id))
  ...   | ∀p▽q | ks = allImplies2
    (λ
      { (inj₁ p) (inj₁ k) → inj₁ (p , k)
      ; (inj₂ q) (inj₁ k) → inj₂ (q , k)
      }
    )
    ∀p▽q ks
  intersectUnlessWithStable _ _ ((p , k) , ⌝q△k) | inj₂ q = ⊥-elim (⌝q△k (q , k))

  -- intersectUnlessWithStable : Stable S K → P ▷[ S ] Q → (P △ K) ▷[ S ] (Q △ K)
  -- intersectUnlessWithStable {Q = Q} stable p▷[s]q {st = st} ((p , k) , ⌝q△k) with assertionDecidability Q {st}
  -- intersectUnlessWithStable {Q = Q} stable p▷[s]q {st = st} ((p , k) , ⌝q△k) | inj₁ ⌝q with (p▷[s]q (p , ⌝q))
  -- intersectUnlessWithStable {S = []} stable p▷[s]q ((p , k) , ⌝q△k) | inj₁ ⌝q | ∀p▽q = []
  -- intersectUnlessWithStable {S = cb ∷ cbs} stable p▷[s]q ((p , k) , ⌝q△k) | inj₁ ⌝q | ∀p▽q with (stable (k , id))
  -- ... | ks = allImplies2 (λ { (inj₁ p) (inj₁ k) → inj₁ (p , k) ; (inj₂ q) (inj₁ k) → inj₂ (q , k) }) ∀p▽q ks
  -- intersectUnlessWithStable stable p▷[s]q ((p , k) , ⌝q△k) | inj₂ q = ⊥-elim (⌝q△k (q , k))

  -- "There exists a conditional instruction that moves from P△⌝Q to Q."
  Progress : ParallelProgram → Predicate → Predicate → Statement
  Progress S P Q = Any (λ cb → ⟦ P △ ⌝ Q ⟧a ⇛ (CBWP (cb , Q))) S

  infix 4 _↣[_]_
  _↣[_]_ : Predicate → ParallelProgram → Predicate → Statement
  P ↣[ S ] Q = Progress S P Q

  ↣-NonEmpty : P ↣[ S ] Q → NonEmpty S
  ↣-NonEmpty (here px) ()
  ↣-NonEmpty (there x) ()

  ↣-NonEmpty-Reflexive : NonEmpty S → P ↣[ S ] P
  -- ↣-NonEmpty-Reflexive nonEmptyS = ↣-NonEmpty-from-⇒ nonEmptyS ⇒-Reflexive
  ↣-NonEmpty-Reflexive {[]} nonEmptyS = ⊥-elim (nonEmptyS refl)
  ↣-NonEmpty-Reflexive {cb ∷ cbs} nonEmptyS = here (λ { (p , ⌝p) → ⊥-elim (⌝p p) })

  ↣-⇐-left : P ⇐ Q → P ↣[ S ] R → Q ↣[ S ] R
  ↣-⇐-left p⇐q p↣[s]r = anyImplies (λ { f (q , ⌝r) → f (p⇐q q , ⌝r) }) p↣[s]r

  ↣-NonEmpty-from-⇒ : NonEmpty S → P ⇒ Q → P ↣[ S ] Q
  -- ↣-NonEmpty-from-⇒ {s₀ , []} nonEmptyS p⇒q = ⊥-elim (nonEmptyS refl)
  -- ↣-NonEmpty-from-⇒ {s₀ , x ∷ snd} nonEmptyS p⇒q = here (λ { (p , ⌝q) → ⊥-elim (⌝q (p⇒q p)) })
  ↣-NonEmpty-from-⇒ nonEmptyS p⇒q =
    ↣-⇐-left p⇒q (↣-NonEmpty-Reflexive nonEmptyS)

  ↣-⇐⇒-left : P ⇐⇒ Q → P ↣[ S ] R → Q ↣[ S ] R
  ↣-⇐⇒-left (p⇒q , p⇐q) p↣[s]r = ↣-⇐-left p⇐q p↣[s]r

  --

  -- "Biztosítja"
  Ensures : ParallelProgram → Predicate → Predicate → Statement
  Ensures S P Q = (Unless S P Q × Progress S P Q)

  infix 4 _↦[_]_
  _↦[_]_ : Predicate → ParallelProgram → Predicate → Statement
  P ↦[ S ] Q = Ensures S P Q

  ↦-NonEmpty : P ↦[ S ] Q → NonEmpty S
  ↦-NonEmpty (p▷[s]q , p↣[s]q) = ↣-NonEmpty p↣[s]q

  ↦-NonEmpty-Reflexive : NonEmpty S → P ↦[ S ] P
  ↦-NonEmpty-Reflexive nonEmptyS =
    (▷-Reflexive , (↣-NonEmpty-Reflexive nonEmptyS))

  ↦-NonEmpty-from-⇒ : NonEmpty S → P ⇒ Q → P ↦[ S ] Q
  ↦-NonEmpty-from-⇒ nonEmptyS p⇒q =
    (▷-from-⇒ p⇒q , ↣-NonEmpty-from-⇒ nonEmptyS p⇒q)

  ↦-⇐⇒-left : P ⇐⇒ Q → P ↦[ S ] R → Q ↦[ S ] R
  ↦-⇐⇒-left p⇐⇒q (p▷[s]r , p↣[s]r) =
    (▷-⇐⇒-left p⇐⇒q p▷[s]r , ↣-⇐⇒-left p⇐⇒q p↣[s]r)

  -- FALSE
  -- impliesEnsuresLeft : P ⇒ Q → P ↦[ S ] R → Q ↦[ S ] R
  -- impliesEnsuresLeft p⇒q (p▷[s]r , progress) = {!   !}

  -- tmp' : (P ▽ Q) △ ⌝ R ⇒ (P △ ⌝ R) ▽ (Q △ ⌝ R)
  -- tmp' (inj₁ p , ⌝r) = inj₁ (p , ⌝r)
  -- tmp' (inj₂ q , ⌝r) = inj₂ (q , ⌝r)
  --
  -- tmp : (⟦ P △ ⌝ R ⟧a ⇛ CBWP (cb , R) × ⟦ Q △ ⌝ R ⟧a ⇛ CBWP (cb , R)) → ⟦ (P ▽ Q) △ ⌝ R ⟧a ⇛ CBWP (cb , R)
  -- tmp (x , y) = ⇛Disjunctive tmp' (x , y)

  -- FALSE
  -- ensuresDisjunctive : ((P ↦[ S ] R) × (Q ↦[ S ] R)) → (P ▽ Q ↦[ S ] R)
  -- ensuresDisjunctive ((P▷[S]R , existsP) , (Q▷[S]R , existsQ)) =
  --   (unlessDisjunctive (P▷[S]R , Q▷[S]R) , {!   !})

  -- -- ensuresDisjunctive : (P ↦[ S ] R) ⊎ (P ↦[ S ] R) → (P ▽ Q ↦[ S ] R)
  -- -- ensuresDisjunctive (inj₁ (P▷[S]R , exists)) = ({!   !} , anyImplies {!   !} exists)
  -- -- ensuresDisjunctive (inj₂ (Q▷[S]R , exists)) = ({!   !} , {!   !})

  --

  -- "Elkerülhetetlen / Inevitable"
  data Inevitable : ParallelProgram → Predicate → Predicate → Statement where
    FromEnsures : Ensures S P Q → Inevitable S P Q
    Transitivity : ((Inevitable S P Q) × (Inevitable S Q R)) → Inevitable S P R
    Disjunctivity :
      ((Inevitable S P R) × (Inevitable S Q R)) → Inevitable S (P ▽ Q) R

  infix 4 _↪[_]_
  _↪[_]_ : Predicate → ParallelProgram → Predicate → Statement
  P ↪[ S ] Q = Inevitable S P Q

  ↪-NonEmpty : P ↪[ S ] Q → NonEmpty S
  ↪-NonEmpty (FromEnsures p↦[s]q) = ↦-NonEmpty p↦[s]q
  ↪-NonEmpty (Transitivity (p↪[s]p₁ , p₁↪[s]q)) = ↪-NonEmpty p₁↪[s]q
  ↪-NonEmpty (Disjunctivity (p↪[s]q , p₁↪[s]q)) = ↪-NonEmpty p₁↪[s]q

  ↪-NonEmpty-Reflexive : NonEmpty S → P ↪[ S ] P
  ↪-NonEmpty-Reflexive nonEmptyS = FromEnsures (↦-NonEmpty-Reflexive nonEmptyS)

  ↪-NonEmpty-from-⇒ : NonEmpty S → P ⇒ Q → P ↪[ S ] Q
  ↪-NonEmpty-from-⇒ nonEmptyS p⇒q = FromEnsures (↦-NonEmpty-from-⇒ nonEmptyS p⇒q)

  ↪-⇐-left : P ⇐ Q → P ↪[ S ] R → Q ↪[ S ] R
  ↪-⇐-left p⇐q p↪[s]r = Transitivity (q↪[s]p , p↪[s]r)
    where
      nonEmptyS = ↪-NonEmpty p↪[s]r
      q↦[s]p = ↦-NonEmpty-from-⇒ nonEmptyS p⇐q
      q↪[s]p = FromEnsures q↦[s]p
  -- FromEnsures (↦-⇐⇒-left p⇐q p↦[s]r)
  -- ↪-⇐-left p⇐q (Transitivity (p↪[s]q , q↪[s]r)) = {!!} -- Transitivity (↪-⇐-left p⇐q p↪[s]q , q↪[s]r)
  -- ↪-⇐-left p⇐q (Disjunctivity (p↪[s]r , q↪[s]r)) = {!Disjunctivity {} (? , ?)!}


  ↪-⇐⇒-left : P ⇐⇒ Q → P ↪[ S ] R → Q ↪[ S ] R
  ↪-⇐⇒-left p⇐⇒q = ↪-⇐-left (proj₂ p⇐⇒q)
  -- ↪-⇐⇒-left p⇐⇒q (FromEnsures p↦[s]r) = FromEnsures (↦-⇐⇒-left p⇐⇒q p↦[s]r)
  -- -- ↪-⇐⇒-left p⇐⇒q (Transitivity (p↪[s]p₁ , p₁↪[s]r)) = Transitivity (↪-⇐⇒-left p⇐⇒q p↪[s]p₁ , p₁↪[s]r)
  -- ↪-⇐⇒-left p⇐⇒q (Transitivity (p↪[s]q , q↪[s]r)) = Transitivity (↪-⇐⇒-left p⇐⇒q p↪[s]q , q↪[s]r)
  -- ↪-⇐⇒-left p⇐⇒q (Disjunctivity (p↪[s]r , q↪[s]r)) = {!↪-⇐⇒-left p⇐⇒q Disjunctivity (p↪[s]r , q↪[s]r)!}
  -- ↪-⇐⇒-left p⇐⇒q (Disjunctivity (p↪[s]r , q↪[s]r)) = {!Disjunctivity {} (? , ?)!}

  -- impliesInevitableLeft : P ⇒ Q → P ↪[ S ] R → Q ↪[ S ] R
  -- impliesInevitableLeft p⇒q (FromEnsures ensures) = FromEnsures (impliesEnsuresLeft p⇒q ensures)
  -- impliesInevitableLeft p⇒q (Transitivity (p↪[s]p₁ , p₁↪[s]r)) = {!   !}
  -- impliesInevitableLeft p⇒q (Disjunctivity (p₁↪[s]r , p₂↪[s]r)) = {!   !}

  -- inv / INV

  -- P in invS(Q) = sp(s₀, Q) => P /\ P => lf(S, P)

  Invariant : InitializedProgram → Predicate → Predicate → Statement
  Invariant I@(s₀ , S) Q P = ((BSP (s₀ , Q)) ⇛ ⟦ P ⟧a) × (⟦ P ⟧a ⇛ CBLWP (S , P))

  infix 4 _∈inv[_/_]
  _∈inv[_/_] : Predicate → InitializedProgram → Predicate → Statement
  P ∈inv[ I / Q ] = Invariant I Q P

  -- Invariant : ParallelProgram -> Predicate -> Statement
  -- Invariant S P = ⟦ P ⟧a ⇛ (CBLWP (S , P))

  INVARIANT : InitializedProgram → Predicate → Assertion
  INVARIANT I Q = λ st → ∀{P} → Invariant I Q P → st ⊢ P

  infix 4 INV[_/_]
  INV[_/_] : InitializedProgram → Predicate → Assertion
  INV[ I / Q ] = INVARIANT I Q

  

  True : InitializedProgram → Predicate → Predicate → Statement
  True I P Q = INVARIANT I Q ⇛ ⟦ P ⟧a

  infix 4 _∈true[_/_]
  _∈true[_/_] : Predicate → InitializedProgram → Predicate → Statement
  P ∈true[ I / Q ] = True I P Q

  --

  -- init

  -- infix 4 _∈INIT
  -- _∈INIT : Predicate → Statement
  -- P ∈INIT = {!!}

  --

  Fixpoint : ParallelProgram → Assertion
  Fixpoint S = λ st → All (λ cb → st ≡ ⟦ cb ⟧cb st) S

  infix 4 φ[_]
  φ[_] : ParallelProgram → Assertion
  φ[ S ] = Fixpoint S

  cb-helper : (st ≡ ⟦ (P , b) ⟧cb st) → (¬(⟦ P ⟧a st) ⊎ (st ≡ ⟦ b ⟧b st))
  cb-helper {st} {P} eq with ⟦ P ⟧d st
  cb-helper eq | yes p = inj₂ eq
  cb-helper eq | no ¬p = inj₁ ¬p

  -- fixpoint-helper :
  --   φ[ S ] → All (λ { (p , i) → ¬ ⊎ })
  -- fixpoint-helper fp = ?

  --FP

  FIXPOINT : ParallelProgram → Predicate → Statement
  FIXPOINT S P = Fixpoint S ⇛ ⟦ P ⟧a

  infix 4 _∈FP[_]
  _∈FP[_] : Predicate → ParallelProgram → Statement
  P ∈FP[ S ] = FIXPOINT S P

  -- Termination

  Termination : ParallelProgram → Predicate → Statement
  Termination S P = Σ Predicate (λ Q → (P ↪[ S ] Q × ⟦ Q ⟧a ⇛ Fixpoint S))

  infix 4 _∈TERM[_]
  _∈TERM[_] : Predicate → ParallelProgram → Statement
  P ∈TERM[ S ] = Termination S P


  -- Specification, Conforms

  -- Specification : Set
  -- Specification = {!!}

  record Specification : Set where
    constructor mkSpecification
    field
      unless : List (Predicate × Predicate)
      ensures : List (Predicate × Predicate)
      inevitable : List (Predicate × Predicate)
      fixpoint : List Predicate
      termination : List Predicate
      initial : List Predicate
      invariant : List Predicate

  -- makeInitial : List Predicate → Set
  -- makeInitial [] = ⊤
  -- makeInitial (P ∷ Ps) = {!!} × makeInitial Ps

  -- makeInitial initial → {!( ? ? ? ? ? ? ? )!}

  Conforms : Specification → InitializedProgram → Set
  Conforms specification I@(s₀ , S) =
    let
      INIT : Predicate
      INIT = Data.List.foldr (λ acc curr → curr △ acc) TRUE initial
    in
      (
        All (λ { (P , Q) → P ▷[ S ] Q }) unless
        ×
        All (λ { (P , Q) → P ↦[ S ] Q }) ensures
        ×
        All (λ { (P , Q) → P ↪[ S ] Q }) inevitable
        ×
        All (λ { P → φ[ S ] ⇛ ⟦ P ⟧a }) fixpoint
        ×
        All (λ { P → P ∈TERM[ S ] }) termination
        ×
        All (λ { P → P ∈inv[ I / INIT ] }) invariant
      )
        where open Specification specification

  -- PSP

  pspFromEnsures₁ : P ▷[ S ] Q → R ▷[ S ] V → (P △ R) ▷[ S ] (Q △ R ▽ V)
  pspFromEnsures₁ p▷[s]q r▷[s]v _p△r_△⌝_q△r▽v_@((p , r) , ⌝_q△r▽v_)
    with (notOrToAndNotNot ⌝_q△r▽v_)
  ... | ⌝_q△r_ , ⌝v with (r▷[s]v (r , ⌝v))
  ...   | [] = []
  ...   | inj₁ r' ∷ rest with (p▷[s]q (p , λ q → ⌝_q△r_ (q , r)))
  ...     | inj₁ p' ∷ rest' =
              inj₁ (p' , r')
              ∷
              pspFromEnsures₁
                (lessUnless p▷[s]q) (lessUnless r▷[s]v) _p△r_△⌝_q△r▽v_
  ...     | inj₂ q' ∷ rest' =
              inj₂ (inj₁ (q' , r'))
              ∷
              pspFromEnsures₁
                (lessUnless p▷[s]q) (lessUnless r▷[s]v) _p△r_△⌝_q△r▽v_
  pspFromEnsures₁ p▷[s]q r▷[s]v _p△r_△⌝_q△r▽v_@((p , r) , ⌝_q△r▽v_) | ⌝_q△r_ , ⌝v -- ...
        | inj₂ v_ ∷ rest =
            inj₂ (inj₂ v_)
            ∷
            pspFromEnsures₁
              (lessUnless p▷[s]q) (lessUnless r▷[s]v) _p△r_△⌝_q△r▽v_

  pspFromEnsures₂ : P ▷[ S ] Q → R ▷[ S ] V → P ↣[ S ] Q → Progress S (P △ R) (Q △ R ▽ V)
  pspFromEnsures₂ {P} {S = (cb ∷ cbs)} {Q} {R} {V} p▷[s]q r▷[s]v (here p△⌝q⇛bcwp) = here f
    where
      f : ⟦ (P △ R) △ (⌝ (Q △ R ▽ V)) ⟧a ⇛ CBWP (cb , Q △ R ▽ V)
      f ((p , r) , ⌝_q△r▽v_) with (notOrToAndNotNot ⌝_q△r▽v_)
      ... | ⌝_q△r_ , ⌝v with (r▷[s]v (r , ⌝v))
      ...   | inj₁ r' ∷ rest with (p▷[s]q (p , λ q → ⌝_q△r_ (q , r)))
      ...     | inj₁ p' ∷ rest' = inj₁ (p△⌝q⇛bcwp (p , (λ q → ⌝_q△r_ (q , r))) , r')
      ...     | inj₂ q' ∷ rest' = inj₁ (q' , r')
      f ((p , r) , ⌝_q△r▽v_) | ⌝_q△r_ , ⌝v -- ...
            | inj₂ v_ ∷ rest = inj₂ v_
  pspFromEnsures₂ p▷[s]q r▷[s]v (there rest) =
    there (pspFromEnsures₂ (lessUnless p▷[s]q) (lessUnless r▷[s]v) rest)

  pspFromEnsures : P ↦[ S ] Q → R ▷[ S ] V → (P △ R) ↦[ S ] (Q △ R ▽ V)
  pspFromEnsures (p▷[s]q , p↣[s]q) r▷[s]v =
    (pspFromEnsures₁ p▷[s]q r▷[s]v , pspFromEnsures₂ p▷[s]q r▷[s]v p↣[s]q)

  --

  PSP : ((P ↪[ S ] Q) × (R ▷[ S ] V)) → (P △ R) ↪[ S ] ((Q △ R) ▽ V)

  -- pspFromTransitivity : (P ↪[ S ] P₁ × P₁ ↪[ S ] Q) → R ▷[ S ] V → (P △ R) ↪[ S ] ((Q △ R) ▽ V)
  -- pspFromTransitivity (p↪[s]p₁ , p₁↪[s]q) r▷[s]v =
  --     Transitivity (
  --       (PSP (p↪[s]p₁ , r▷[s]v))
  --       ,
  --       Disjunctivity (
  --         (PSP (p₁↪[s]q , r▷[s]v))
  --         ,
  --         (↪-NonEmpty-from-⇒ (↪-NonEmpty p↪[s]p₁) inj₂)
  --       )
  --     )

  -- pspFromDisjunctivity : (P ↪[ S ] Q × P₁ ↪[ S ] Q) → R ▷[ S ] V → ((P ▽ P₁) △ R) ↪[ S ] (Q △ R ▽ V)
  -- pspFromDisjunctivity {P} {S} {Q} {P₁} {R} (p₁↪[s]q , p₂↪[s]q) r▷[s]v =
  --   ↪-⇐⇒-left {(P △ R) ▽ (P₁ △ R)} {(P ▽ P₁) △ R}
  --     (⇐⇒Symmetric andDistributiveRight)
  --     (Disjunctivity (PSP (p₁↪[s]q , r▷[s]v) , PSP (p₂↪[s]q , r▷[s]v)))

  PSP (FromEnsures ensures , r▷[s]v) =
    FromEnsures (pspFromEnsures ensures r▷[s]v)

  -- PSP (Transitivity (p↪[s]p₁ , p₁↪[s]q) , r▷[s]v) = pspFromTransitivity transitivity r▷[s]v
  -- PSP (Disjunctivity disjunctivity , r▷[s]v) = pspFromDisjunctivity disjunctivity r▷[s]v

  PSP (Transitivity (p↪[s]p₁ , p₁↪[s]q) , r▷[s]v) =
    Transitivity (
      (PSP (p↪[s]p₁ , r▷[s]v))
      ,
      Disjunctivity (
        (PSP (p₁↪[s]q , r▷[s]v))
        ,
        (↪-NonEmpty-from-⇒ (↪-NonEmpty p↪[s]p₁) inj₂)
      )
    )

  PSP (Disjunctivity (p₁↪[s]q , p₂↪[s]q) , r▷[s]v) =
    ↪-⇐⇒-left
      (⇐⇒Symmetric andDistributiveRight)
      (Disjunctivity (PSP (p₁↪[s]q , r▷[s]v) , PSP (p₂↪[s]q , r▷[s]v)))
