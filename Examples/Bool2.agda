module Examples.Bool2 where

open import Data.Unit
open import Data.Fin
open import Data.Sum
open import Data.Product

open import Data.IDesc
open import Data.Fixpoint

open import Ornament.Ornament

open import Relation.Binary.PropositionalEquality

UnitD : ⊤ → IDesc ⊤
UnitD tt = `1

BoolO : Orn (λ { tt → tt }) UnitD
BoolO tt = insert (Fin 2) f where
  f : Fin 2 → Ornament _ _
  f zero = `1
  f (suc zero) = `1
  f (suc (suc ()))

MaybeO : Set → Orn (λ { tt → tt }) UnitD
MaybeO A tt = insert (Fin 2) f where
  f : Fin 2 → Ornament _ _
  f zero = insert A (λ _ → `1)
  f (suc zero) = `1
  f (suc (suc ()))
