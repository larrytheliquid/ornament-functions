module Examples.VecFunc where

open import Data.Unit
open import Data.Product
open import Data.Sum

open import Data.IDesc
open import Data.Fixpoint
open import FOrnament.Functions
open import Examples.NatFunc

open import Relation.Binary.PropositionalEquality

VecD : (A : Set) → Nat → IDesc Nat
VecD A (con (inj₁ tt) , tt) = `1
VecD A (con (inj₂ n) , tt) = `Σ A λ _ → `X (n , tt)

nil : ∀ {I i} {R : I → IDesc I} → ⟦ μ (VecD (μ R i)) [ ze ]× `⊤ ⟧Type
nil = (con tt) , tt

cons : ∀ {I i} {R : I → IDesc I} →
  ⟦ μ R [ i ]→ μ (VecD (μ R i)) [ ze ]→ μ (VecD (μ R i)) [ su (con (inj₁ tt)) ]× `⊤ ⟧Type
cons x xs = con (x , xs) , tt
