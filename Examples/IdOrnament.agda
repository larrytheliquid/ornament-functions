module Examples.IdOrnament where

open import Data.IDesc

open import Ornament.Ornament



IdO : ∀{I} → (D : I → IDesc I) → Orn (λ i → i) D
IdO D i = help (D i)
  where help : ∀{I : Set} → (D : IDesc I) → Ornament (λ i → i) D
        help `1 = `1
        help (`X i) = `X (inv i)
        help (l `× r) = help l `× help r
        help (l `+ r) = help l `+ help r
        help (`Σ S T) = `Σ (λ s → help (T s))
        help (`Π S T) = `Π (λ s → help (T s))
