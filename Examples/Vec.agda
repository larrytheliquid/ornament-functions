module Examples.Vec where
open import Data.Unit
open import Data.Fin
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.IDesc
open import Data.Fixpoint
open import Ornament.Ornament
open import Examples.Nat

VecD : (A : Set) → Nat → IDesc Nat
VecD A n  = `Σ (Fin 2) f
  where f : Fin 2 → IDesc Nat
        f zero = `Σ (n ≡ ze) λ _ → `1
        f (suc zero) = `Σ Nat λ n′ → `Σ (n ≡ su n′) λ _ → `Σ A λ _ → `X n′
        f (suc (suc ()))

Vec : ∀ A → Nat → Set
Vec A n = μ (VecD A) n
