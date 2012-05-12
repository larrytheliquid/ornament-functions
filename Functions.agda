module Functions where

open import Data.Unit
open import Data.Product

open import Data.IDesc
open import Data.Fixpoint

open import Ornament.Ornament

infixr 20 _`×_ _`→_

data Type : Set₁
⟦_⟧Type : Type → Set

data Type where
  _`→_ _`×_ : (S T : Type) → Type
  `Π `Σ : (S : Type) (T : ⟦ S ⟧Type → Type) → Type
  `μ : {I : Set}(D : I → IDesc I)(i : I) → Type

⟦ S `→ T ⟧Type = ⟦ S ⟧Type → ⟦ T ⟧Type
⟦ S `× T ⟧Type = ⟦ S ⟧Type × ⟦ T ⟧Type
⟦ `Π S T ⟧Type = {s : ⟦ S ⟧Type} → ⟦ T s ⟧Type
⟦ `Σ S T ⟧Type = Σ[ s ∶ ⟦ S ⟧Type ] ⟦ T s ⟧Type
⟦ `μ D i ⟧Type = μ D i

data FunctionOrn : Type → Set₁ where
  _`→_ : ∀{S T}
    (U : FunctionOrn S) (V : FunctionOrn T) →
    FunctionOrn (S `→ T)

  `μ : ∀{I I⁺} {D} {i} {f : I⁺ → I}
    (O : Orn f D) (j : f ⁻¹ i) →
    FunctionOrn (`μ D i)

⟦_⟧FunctionOrn : ∀ {R} → FunctionOrn R → Set
⟦ U `→ V ⟧FunctionOrn = ⟦ U ⟧FunctionOrn → ⟦ V ⟧FunctionOrn
⟦ `μ {D = D} O (inv j) ⟧FunctionOrn = μ (⟦_⟧Orn₂ {D = D} O) j

