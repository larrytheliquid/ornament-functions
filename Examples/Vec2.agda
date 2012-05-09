module Examples.Vec2 where
open import Data.Unit
open import Data.Fin
open import Data.Sum
open import Data.Product
open import Data.IDesc
open import Data.Fixpoint
open import Ornament.Ornament
open import Examples.Nat

VecD : (A : Set) → Nat → IDesc Nat
VecD A n with Nat-view n
VecD A ._ | see-ze = `1
VecD A ._ | see-su n = `Σ A λ _ → `X n

Vec : ∀ A → Nat → Set
Vec A n = μ (VecD A) n

open import Data.Nat
`Vec : (A : Set) → ℕ → Set
`Vec A zero = ⊤
`Vec A (suc n) = Σ[ x ∶ A ] `Vec A n

eg : `Vec ℕ 3
eg = 11 , 22 , 33 , tt
