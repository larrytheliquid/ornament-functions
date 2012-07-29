module Examples.Bool where

open import Data.Unit
open import Data.Product
open import Data.Sum

open import Data.IDesc
open import Data.Fixpoint

open import Relation.Binary.PropositionalEquality


BoolD : ⊤ → IDesc ⊤
BoolD tt = `1 `+ `1

Bool : Set
Bool = μ BoolD tt

true : Bool
true = con (inj₁ tt)

false : Bool
false = con (inj₂ tt)

data Bool-View : Bool → Set where
  see-true : Bool-View true
  see-false : Bool-View false

Bool-view : (b : Bool) → Bool-View b
Bool-view (con (inj₁ tt)) = see-true
Bool-view (con (inj₂ tt)) = see-false

