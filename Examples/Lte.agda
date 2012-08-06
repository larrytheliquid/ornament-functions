module Examples.Lte where
open import Data.Unit
open import Data.Fin
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.IDesc
open import Data.Fixpoint
open import Ornament.Ornament
open import Data.Nat
open import Examples.Nat

LteO : Orn (λ (x : ℕ × ℕ) → tt) NatD
LteO (m , n) = insert (m ≡ zero) λ _ → `1 `+
  insert ℕ λ m′ → insert ℕ λ n′ →
  insert (m ≡ suc m′) λ _ → insert (n ≡ suc n′) λ _ →
  `X (inv (m′ , n′))

LteD' : ℕ × ℕ → IDesc (ℕ × ℕ)
LteD' (zero , n) = `1
LteD' (suc _ , zero) = `0
LteD' (suc m , suc n) = `X (m , n)

LteD'' : ℕ × ℕ → IDesc (ℕ × ℕ)
LteD'' (zero , n) = `1
LteD'' (suc m , n) =
  `Σ ℕ λ n′ → `Σ (n ≡ suc n′) λ _ →
  `X (m , n)

LteD : Nat × Nat → IDesc (Nat × Nat)
LteD (m , n)  = `Σ (Fin 2) f
  where f : Fin 2 → IDesc (Nat × Nat)
        f zero = `Σ (m ≡ ze) λ _ → `1
        f (suc zero) = `Σ Nat λ m′ → `Σ Nat λ n′ →
          `Σ (m ≡ su m′) λ _ → `Σ (n ≡ su n′) λ _ →
          `X (m′ , n′)
        f (suc (suc ()))

