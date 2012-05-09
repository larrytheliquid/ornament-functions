module Examples.List2 where
open import Data.Unit
open import Data.Fin
open import Data.Sum
open import Data.Product

open import Data.IDesc
open import Data.Fixpoint
open import Ornament.Ornament
open import Examples.Nat

ListD : (A : Set) → Fin 2 → IDesc (Fin 2)
ListD A zero = `1
ListD A (suc zero) = `Σ (Fin 2) λ i → `Σ A λ _ → `X i
ListD A (suc (suc ()))

infixr 4 _∷_

data List (A : Set) : Fin 2 → Set where
  [] : List A zero
  _∷_ : ∀ {i} → A → List A i → List A (suc zero)

eg : List ⊤ (suc zero)
eg = tt ∷ tt ∷ tt ∷ []
