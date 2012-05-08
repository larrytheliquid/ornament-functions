module FOrnament.FunOrnament where

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Data.IDesc
open import Data.Fixpoint

open import Ornament.Ornament
open import Ornament.OrnamentalAlgebra

open import FOrnament.Functions


-- * Universe of function ornaments

data FunctionOrn : Type → Set₂ where
  μ⁺[_,_]_[_]→_ : ∀{I I⁺} D {i T} →
                 (f : I⁺ → I)
                 (O : Orn f D)(i⁻¹ : f ⁻¹ i)
                 (T⁺ : FunctionOrn T) → FunctionOrn (μ D [ i ]→ T)
  μ⁺[_,_]_[_]×_ : ∀{I I⁺} D {i T} →
                 (f : I⁺ → I)
                 (O : Orn f D)(i⁻¹ : f ⁻¹ i)
                 (T⁺ : FunctionOrn T) → FunctionOrn (μ D [ i ]× T)
  `⊤ : FunctionOrn `⊤

-- * Projections

-- ** Lifted function

⟦_⟧FunctionOrn : ∀{T} → FunctionOrn T → Set
⟦ μ⁺[ D , f ] O [ inv i⁺ ]→ T⁺ ⟧FunctionOrn = μ (⟦ D ⁺ O ⟧Orn) i⁺ → ⟦ T⁺ ⟧FunctionOrn
⟦ μ⁺[ D , f ] O [ inv i⁺ ]× T⁺ ⟧FunctionOrn = μ (⟦ D ⁺ O ⟧Orn) i⁺ × ⟦ T⁺ ⟧FunctionOrn
⟦ `⊤ ⟧FunctionOrn = ⊤

-- ** Coherence proof

⟦_⟧Coherence : ∀{T} → (FO : FunctionOrn T) → ⟦ T ⟧Type → ⟦ FO ⟧FunctionOrn → Set
⟦ μ⁺[ D , f ] O [ inv i⁺ ]→ T⁺ ⟧Coherence fun fun⁺ = (x : μ ⟦ D ⁺ O ⟧Orn i⁺) → ⟦ T⁺ ⟧Coherence (fun (forgetOrnament D f O x)) (fun⁺ x)
⟦ μ⁺[ D , f ] O [ inv i⁺ ]× T⁺ ⟧Coherence (x , xs) (x⁺ , xs⁺) = x ≡ forgetOrnament D f O x⁺ × ⟦ T⁺ ⟧Coherence xs xs⁺ 
⟦ `⊤ ⟧Coherence tt tt = ⊤
