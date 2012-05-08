module Examples.Nat where

open import Data.Unit
open import Data.Product
open import Data.Sum

open import Data.IDesc
open import Data.Fixpoint

open import Relation.Binary.PropositionalEquality


NatD : ⊤ → IDesc ⊤
NatD _ = `1 `+ `X tt

Nat : Set
Nat = μ NatD tt

ze : Nat
ze = con (inj₁ tt)

su : Nat → Nat
su n = con (inj₂ n)

data Nat-View : Nat → Set where
  see-ze : Nat-View ze
  see-su : (n : Nat) → Nat-View (su n)


Nat-view : (n : Nat) → Nat-View n
Nat-view (con (inj₁ tt)) = see-ze
Nat-view (con (inj₂ n)) = see-su n
