open import Data.Empty
open import Data.Unit hiding ( _≟_ ; _≤?_ )
open import Data.Nat hiding ( _≟_ ; Ordering )
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

module Diff where

data Type : Set where
  `⊥ : Type
  `⊤ : Type
  _`⊎_ : (S T : Type) → Type

⟦_⟧ : Type → Set
⟦ `⊥ ⟧ = ⊥
⟦ `⊤ ⟧ = ⊤
⟦ S `⊎ T ⟧ = ⟦ S ⟧ ⊎ ⟦ T ⟧

-- should look like ring axioms
_`∸_ : Type → Type → Type

S `∸ `⊥  = S
S `∸ (T₁ `⊎ T₂)  = (S `∸ T₁) `⊎ (S `∸ T₂)

(S₁ `⊎ S₂) `∸ ⊤  = (S₁ `∸ ⊤) `⊎ S₂

_ `∸ `⊤  = `⊥



