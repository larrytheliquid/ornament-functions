module Examples.Maybe where

open import Data.Unit
open import Data.Sum
open import Data.Product

open import Data.IDesc
open import Data.Fixpoint

open import Ornament.Ornament

open import Examples.Bool

open import Relation.Binary.PropositionalEquality


MaybeO : Set → Orn (λ tt → tt) BoolD
MaybeO A _ = insert A (λ _ → `1) `+ `1

Maybe : Set → Set
Maybe A = μ ⟦ BoolD ⁺ MaybeO A ⟧Orn tt

nothing : ∀{A} → Maybe A
nothing = con (inj₂ tt)

just : ∀{A} → A → Maybe A
just a = con (inj₁ (a , tt))