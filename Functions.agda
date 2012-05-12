module Functions where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Data.IDesc
open import Data.Fixpoint

open import Ornament.Ornament
open import Ornament.OrnamentalAlgebra

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

data FunOrn : Type → Set₁ where
  _`→_ : ∀{S T}
    (U : FunOrn S) (V : FunOrn T) →
    FunOrn (S `→ T)

  `μ : ∀{I I⁺} {D} {i} {f : I⁺ → I}
    (O : Orn f D) (j : f ⁻¹ i) →
    FunOrn (`μ D i)

⟦_⟧FunOrn : ∀ {R} → FunOrn R → Set
⟦ U `→ V ⟧FunOrn = ⟦ U ⟧FunOrn → ⟦ V ⟧FunOrn
⟦ `μ {D = D} O (inv j) ⟧FunOrn = μ ⟦ D ⁺ O ⟧Orn j

Coherence₁ : Set₁
Coherence₁ = {I J : Set} {j : J}
  {D : I → IDesc I} {re : J → I}
  {O : Orn re D}
  {f : μ D (re j) → μ D (re j)}
  {f′ : μ ⟦ D ⁺ O ⟧Orn j → μ ⟦ D ⁺ O ⟧Orn j}
  (x′ : μ ⟦ D ⁺ O ⟧Orn j) →
  f (forgetOrnament D re O x′) ≡ forgetOrnament D re O (f′ x′)

-- Coherence : ∀ {R} (R′ : FunOrn R) (f : ⟦ R ⟧Type) (f′ : ⟦ R′ ⟧FunOrn) → Set
-- Coherence (U `→ V) f f′ = {!!}
-- Coherence (`μ O j) f' f′ = {!!}
