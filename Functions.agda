module Functions where

open import Data.Unit
open import Data.Product

open import Data.IDesc
open import Data.Fixpoint

infixr 20 _`×_ _`→_

data Type : Set₁ where
  _`→_ _`×_ : (S T : Type) → Type
  `μ : {I : Set}(D : I → IDesc I)(i : I) → Type

⟦_⟧Type : Type → Set
⟦ S `→ T ⟧Type = ⟦ S ⟧Type → ⟦ T ⟧Type
⟦ S `× T ⟧Type = ⟦ S ⟧Type × ⟦ T ⟧Type
⟦ `μ D i ⟧Type = μ D i

