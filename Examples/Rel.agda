module Examples.Rel where
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

lte : ℕ → ℕ → Bool
lte zero n = true
lte (suc m) zero = false
lte (suc m) (suc n) = lte m n

data LteP : ℕ → ℕ → Bool → Set where
  yes : (n : ℕ) → LteP zero n true
  no : (m : ℕ) → LteP (suc m) zero false
  there : ∀{b m n} → LteP m n b → LteP (suc m) (suc n) b

data Lte : ℕ → ℕ → Set where
  here : (n : ℕ) → Lte zero n
  there : ∀{m n} → Lte m n → Lte (suc m) (suc n)

coherence : Set
coherence = ∀ m n → (lte m n ≡ true → Lte m n)
                  ×  (Lte m n → lte m n ≡ true)

Lteλ : ℕ → ℕ → Set
Lteλ zero n = ⊤
Lteλ (suc m) zero = ⊥
Lteλ (suc m) (suc n) = Lteλ m n
