open import Function
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Maybe
open import Data.IDesc
open import Relation.Binary.PropositionalEquality
open import Ornament.Ornament

module Ornament.Diff where

-- TODO diff : {I : Set} (S T : IDesc I) → Maybe ((o : Ornament id S) × forgetOrnament o ≡ t)
diff : {I : Set} (S T : IDesc I) → Maybe (Ornament id S)

diff `1 `1 = just `1
diff `1 T = just {!insert !}
diff (`X i) (`X i′) = just (insert (i ≡ i′) (λ _ → `X (inv i)))
diff (S `× T) (S′ `× T′) with diff S S′ | diff T T′
... | just so | just to = just (so `× to)
... | _ | _ = nothing
diff (S `+ T) (S′ `+ T′) with diff S S′ | diff T T′
... | just so | just to = just (so `+ to)
... | _ | _ = nothing

diff _ _ = nothing


