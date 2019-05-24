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
