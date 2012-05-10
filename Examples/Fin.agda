module Examples.Fin where
open import Data.Unit
open import Data.Fin
open import Data.Sum
open import Data.Product
open import Data.IDesc
open import Data.Fixpoint
open import Ornament.Ornament
open import Examples.Nat
open import Data.Nat
open import Data.Empty

FinD : Nat → IDesc Nat
FinD n with Nat-view n
FinD ._ | see-ze = `0
FinD ._ | see-su n = `1 `+ `X n

`Fin : ℕ → Set
`Fin zero = ⊥
`Fin (suc n) = ⊤ ⊎ `Fin n
