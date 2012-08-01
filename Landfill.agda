open import Data.Empty
open import Data.Unit hiding ( _≟_ ; _≤?_ )
open import Data.Nat hiding ( _≟_ ; Ordering )
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ ; lift ; inject )
open import Data.Fin.Props renaming ( _≟_ to _≟f_ )
open import Data.Vec hiding ( concat ; [_] )
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding ( map )
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PreorderReasoning
open import Function

module Landfill where

data Type : ℕ → Set where
  `⊥ : Type 0
  `⊤ : Type 1
  _`⊎_ : ∀ {m n} (S : Type m) (T : Type n) → Type (m + n)
  _`×_ : ∀ {m n} (S : Type m) (T : Type n) → Type (m * n)

⟦_⟧ : ∀ {n} → Type n → Set
⟦ `⊥ ⟧ = ⊥
⟦ `⊤ ⟧ = ⊤
⟦ S `⊎ T ⟧ = ⟦ S ⟧ ⊎ ⟦ T ⟧
⟦ S `× T ⟧ = ⟦ S ⟧ × ⟦ T ⟧


