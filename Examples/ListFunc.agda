module Examples.ListFunc where

open import Data.Unit
open import Data.Product
open import Data.Sum

open import Data.IDesc
open import Data.Fixpoint
open import FOrnament.Functions

open import Relation.Binary.PropositionalEquality

ListD : (A : Set) → ⊤ → IDesc ⊤
ListD A i  = `1 `+ `Σ A (λ _ → `X i)

nil : ∀ {I i} {R : I → IDesc I} → ⟦ μ (ListD (μ R i)) [ tt ]× `⊤ ⟧Type
nil = (con (inj₁ tt)) , tt

cons : ∀ {I i} {R : I → IDesc I} →
  ⟦ μ R [ i ]→ μ (ListD (μ R i)) [ tt ]→ μ (ListD (μ R i)) [ tt ]× `⊤ ⟧Type
cons x xs = con (inj₂ (x , xs)) , tt
