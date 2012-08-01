module Examples.Maybe2 where

open import Data.Unit
open import Data.Sum
open import Data.Product

open import Data.IDesc
open import Data.Fixpoint

open import Ornament.Ornament

open import Examples.Bool

open import Relation.Binary.PropositionalEquality

UnitD : ⊤ → IDesc ⊤
UnitD tt = `1

MaybeO : Set → Orn (λ { tt → tt }) BoolD
MaybeO A _ = insert A (λ _ → `1) `+ `1

