module Examples.VecFunc where

open import Data.Unit
open import Data.Product
open import Data.Sum

open import Data.IDesc
open import Data.Fixpoint
open import Functions
open import Examples.NatFunc

open import Relation.Binary.PropositionalEquality

VecD : (A : Set) → ⟦ Nat ⟧Type → IDesc ⟦ Nat ⟧Type
VecD A (con (inj₁ tt)) = `1
VecD A (con (inj₂ n)) = `Σ A λ _ → `X n

nil : ∀ {I i} {R : I → IDesc I} → ⟦ `μ (VecD (μ R i)) ze ⟧Type
nil = con tt

cons : ∀ {I i} {R : I → IDesc I} →
  ⟦ `Π Nat (λ n → `μ R i `→ `μ (VecD (μ R i)) n `→ `μ (VecD (μ R i)) (su n)) ⟧Type
cons x xs = con (x , xs)
