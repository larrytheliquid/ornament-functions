module Examples.Lte where
open import Data.Unit
open import Data.Fin
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.IDesc
open import Data.Fixpoint
open import Ornament.Ornament
open import Examples.Nat

LteD : Nat × Nat → IDesc (Nat × Nat)
LteD (m , n)  = `Σ (Fin 2) f
  where f : Fin 2 → IDesc (Nat × Nat)
        f zero = `Σ (m ≡ ze) λ _ → `1
        f (suc zero) = `Σ Nat λ m′ → `Σ Nat λ n′ →
          `Σ (m ≡ su m′) λ _ → `Σ (n ≡ su n′) λ _ →
          `X (m′ , n′)
        f (suc (suc ()))

