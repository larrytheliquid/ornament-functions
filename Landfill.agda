open import Data.Empty
open import Data.Unit hiding ( _≟_ ; _≤?_ )
open import Data.Nat hiding ( _≟_ ; Ordering ; _+_ ; _*_ ; _∸_ )
open import Data.Integer hiding ( _≟_ )
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ ; lift ; inject ; _-_ )
open import Data.Fin.Props renaming ( _≟_ to _≟f_ )
open import Data.Vec hiding ( concat ; [_] )
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding ( map )
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PreorderReasoning
open import Function

module Landfill where

data Hole : ℤ → Set where
  `⊥ : Hole (+ 0)
  `? : Hole -[1+ 0 ]
  `⊤ : Hole (+ 1)
  _`⊎_ : ∀ {m n} (S : Hole m) (T : Hole n) → Hole (m + n)
  _`×_ : ∀ {m n} (S : Hole m) (T : Hole n) → Hole (m * n)

⟦_⟧ : ∀ {n} → Hole n → Set
⟦ `⊥ ⟧ = ⊥
⟦ `? ⟧ = ⊥
⟦ `⊤ ⟧ = ⊤
⟦ S `⊎ T ⟧ = ⟦ S ⟧ ⊎ ⟦ T ⟧
⟦ S `× T ⟧ = ⟦ S ⟧ × ⟦ T ⟧

_`-_ : ∀{m n} → Hole m → Hole n → Hole (m - n)
S `- T = {!!}


