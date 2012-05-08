open import Function

open import Relation.Binary.PropositionalEquality

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.Fin

open import Data.IDesc
open import Data.Fixpoint
open import Data.Cata

open import Ornament.Ornament

module Ornament.OrnamentalAlgebra {I I⁺ : Set}
                         (R : I → IDesc I)
                         (f : I⁺ → I)
                         (O : Orn f R)
       where

forgetMap0 : ∀{X D} → (O : Ornament f D) → ⟦ ⟦ O ⟧Orn ⟧ (X ∘ f) → ⟦ D ⟧ X 
forgetMap0 `1 tt = tt
forgetMap0 (T⁺ `× T'⁺) (t , t') = forgetMap0 T⁺ t , forgetMap0 T'⁺ t'
forgetMap0 (T⁺ `+ T'⁺) (inj₁ t) = inj₁ (forgetMap0 T⁺ t)
forgetMap0 (T⁺ `+ T'⁺) (inj₂ t') = inj₂ (forgetMap0 T'⁺ t')
forgetMap0 (`Σ {S} {T} T⁺) (s , xs) = s , forgetMap0 (T⁺ s) xs
forgetMap0 (`Π {S} {T} T⁺) f = λ s → forgetMap0 (T⁺ s) (f s)
forgetMap0 .{D = `X (f i⁺)} (`X (inv i⁺)) x = x
forgetMap0 (insert S D⁺) (s , xs) = forgetMap0 (D⁺ s) xs
forgetMap0 (deleteΣ {S} {T} replace T⁺) xs = replace , forgetMap0 T⁺ xs
forgetMap0 (deleteInj₁ P⁺) xs = inj₁ (forgetMap0 P⁺ xs)
forgetMap0 (deleteInj₂ P⁺) xs = inj₂ (forgetMap0 P⁺ xs)

forgetMap : {X : I → Set}{i⁺ : I⁺} → ⟦ ⟦ R ⁺ O ⟧Orn i⁺ ⟧ (X ∘ f) → ⟦ R (f i⁺) ⟧ X
forgetMap {X}{i⁺} = forgetMap0 {D = R (f i⁺)} (O i⁺)

ornAlgebra : ∀{i⁺} → ⟦ ⟦ R ⁺ O ⟧Orn i⁺ ⟧ (μ R ∘ f) → μ R (f i⁺)
ornAlgebra xs = con (forgetMap xs)


forgetOrnament : ∀{i⁺} → μ ⟦ R ⁺ O ⟧Orn i⁺ → μ R (f i⁺)
forgetOrnament xs = foldID ⟦ R ⁺ O ⟧Orn ornAlgebra xs

