module Examples.List where

open import Data.Unit

open import Data.IDesc

open import Ornament.Ornament

open import Examples.Nat


ListO : Set → Orn (λ tt → tt) NatD
ListO A _ = `1 `+ insert A (λ _ → `X (inv tt))
