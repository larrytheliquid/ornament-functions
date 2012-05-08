module FOrnament.Functions where

open import Data.Unit
open import Data.Product

open import Data.IDesc
open import Data.Fixpoint

infixr 20 μ_[_]→_
infixr 20 μ_[_]×_

data Type : Set₁ where
  μ_[_]→_ : {I : Set}(D : I → IDesc I)(i : I)(T : Type) → Type
  μ_[_]×_ : {I : Set}(D : I → IDesc I)(i : I)(T : Type) → Type
  `⊤ : Type

⟦_⟧Type : Type → Set
⟦ μ D [ i ]→ T ⟧Type = μ D i → ⟦ T ⟧Type
⟦ μ D [ i ]× T ⟧Type = μ D i × ⟦ T ⟧Type
⟦ `⊤ ⟧Type = ⊤

