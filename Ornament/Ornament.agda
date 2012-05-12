module Ornament.Ornament where

open import Function

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product

open import Data.IDesc


data _⁻¹_ {A B : Set}(f : A → B) : B → Set where
  inv : (a : A) → f ⁻¹ (f a)

pick : ∀{A B}{f : A → B}{b} → f ⁻¹ b → A
pick (inv a) = a


data Ornament {I I⁺ : Set}(f : I⁺ → I) : IDesc I → Set₁ where
  -- Copy
  `1 : Ornament f `1
  _`×_ : ∀{D D'} → (D⁺ : Ornament f D)(D'⁺ : Ornament f D') → Ornament f (D `× D')
  _`+_ : ∀{D D'} → (D⁺ : Ornament f D)(D'⁺ : Ornament f D') → Ornament f (D `+ D')
  `Σ : ∀{S T} → (T⁺ : (s : S) → Ornament f (T s)) → Ornament f (`Σ S T)
  `Π : ∀{S T} → (T⁺ : (s : S) → Ornament f (T s)) → Ornament f (`Π S T)

  -- Refine
  `X : ∀{i} → (i⁻¹ : f ⁻¹ i) → Ornament f (`X i)

  -- Insert
  insert : ∀{D} → (S : Set) → (D⁺ : S → Ornament f D) → Ornament f D

  -- Delete
  deleteΣ : ∀{S T} → (replace : S)
                     (T⁺ : Ornament f (T replace))  →
                    Ornament f (`Σ S T)
  deleteInj₁ : ∀{P Q} → Ornament f P → Ornament f (P `+ Q)
  deleteInj₂ : ∀{P Q} → Ornament f Q → Ornament f (P `+ Q)


Orn : ∀{I I⁺} → (f : I⁺ → I)(D : I → IDesc I) → Set₁
Orn f D = (i⁺ : _) → Ornament f (D (f i⁺))


⟦_⟧Orn : ∀{I I⁺ f}{D : IDesc I} → Ornament f D → IDesc I⁺
⟦ `1 ⟧Orn = `1
⟦ T⁺ `× T'⁺ ⟧Orn = ⟦ T⁺ ⟧Orn `× ⟦ T'⁺ ⟧Orn 
⟦ T⁺ `+ T'⁺ ⟧Orn = ⟦ T⁺ ⟧Orn `+ ⟦ T'⁺ ⟧Orn
⟦ `Σ {S} T⁺ ⟧Orn = `Σ S ((λ D → ⟦ D ⟧Orn) ∘ T⁺)
⟦ `Π {S} T⁺ ⟧Orn = `Π S ((λ D → ⟦ D ⟧Orn) ∘ T⁺)
⟦ `X (inv i⁺) ⟧Orn = `X i⁺
⟦ insert S D⁺ ⟧Orn = `Σ S (λ s → ⟦ D⁺ s ⟧Orn)
⟦ deleteΣ replace T⁺ ⟧Orn = ⟦ T⁺ ⟧Orn 
⟦ deleteInj₁ P⁺ ⟧Orn = ⟦ P⁺ ⟧Orn  
⟦ deleteInj₂ Q⁺ ⟧Orn = ⟦ Q⁺ ⟧Orn 

⟦_⁺_⟧Orn : ∀{I I⁺ f} D → Orn{I}{I⁺} f D → I⁺ → IDesc I⁺
⟦ D ⁺ orn ⟧Orn i⁺ = ⟦ orn i⁺ ⟧Orn

⟦_⟧Orn₂ : ∀{I I⁺ f} {D} → Orn{I}{I⁺} f D → I⁺ → IDesc I⁺
⟦ O ⟧Orn₂ j = ⟦ O j ⟧Orn

