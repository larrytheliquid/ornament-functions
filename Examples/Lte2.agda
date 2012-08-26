open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality
module Lte2 where

lte : ℕ → ℕ → Bool
lte zero n = true
lte (suc m) zero = false
lte (suc m) (suc n) = lte m n

isZero : ℕ → Bool
isZero zero = true
isZero (suc _) = false

data Lte (m : ℕ) : Bool → Set where
  zero : Lte m (isZero m)
  suc  : ∀ {b} → Lte (pred m) b → Lte m b

forget : ∀ {m b} → Lte m b → ℕ
forget zero = zero
forget (suc p) = suc (forget p)

coh : ∀ m {b} → (p : Lte m b) →
  lte m (forget p) ≡ b
coh zero zero = refl
coh (suc _) zero = refl
coh zero (suc p) = coh zero p
coh (suc n) (suc p) = coh n p

