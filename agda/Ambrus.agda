-- a ⊂ b, a' ⊂ b', b→a' ⊂ a→b'
-- ℤ → B ⊂ ℕ → B
-- ¬ A = A → ⊥
-- λ X → (ℕ → X)
-- map : (f : A → B) → (ℕ → A) → (ℕ → B)

-- λ X → (X → ℕ)
-- map : (f : A → B) → (B → ℕ) → (A → ℕ)


-- f g : Bool → Set
-- f x = if x then ℕ else ℕ
-- g x = if x then ℕ else ℕ
--
-- fg : f ≡ g
-- fg = refl


{-
if : (C : Bool → Set) → C true → C false → (b : Bool) → C b

if _ 2 4 t

λ _ → ℕ :: Bool → Set
-}


--
-- data Singleton {a} {A : Set a} (x : A) : Set a where
--   _with≡_ : (y : A) → x ≡ y → Singleton x
--
-- inspect' : ∀ {a} {A : Set a} (x : A) → Singleton x
-- inspect' x = x with≡ refl

open import Data.Product

func-times-distr : {A : Set}{B C : A → Set} → ((a : A) → (B a × C a)) → ((a : A) → B a) × ((a : A) → C a)
func-times-distr f = ((λ a → proj₁ (f a)) , (λ a → proj₂ (f a)))

func-times-distri : {A : Set}{B C : A → Set} → ((a : A) → (B a × C a)) → ({a : A} → B a) × ({a : A} → C a)
func-times-distri f = ((λ {a} → proj₁ (f a)) , (λ {a} → proj₂ (f a)))

func-times-distr2 : {X : Set} → {A B C : X → Set} → ({x : X} → A x → (B x × C x)) → (({x : X} → A x → B x) × ({x : X} → A x → C x))
func-times-distr2 f = func-times-distri λ _ → func-times-distr f
