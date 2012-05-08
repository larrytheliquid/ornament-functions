open import Function

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality

open import Data.IDesc
open import Data.Fixpoint
open import Data.Cata
open import Data.Induction

open import Ornament.Ornament
import Ornament.OrnamentalAlgebra
import Ornament.AlgebraicOrnament



module Ornament.Reornament {I I⁺ : Set}
                           (D : I → IDesc I)
                           (f : I⁺ → I)
                           (O : Orn f D) where

open Ornament.OrnamentalAlgebra D f O

-- * 

forgetIdx : Σ I⁺ (μ D ∘ f) → I⁺
forgetIdx = proj₁ 

Added : ∀{D X} → Ornament f D → ⟦ D ⟧ X → Set
Added `1 tt = ⊤
Added (P `+ Q) (inj₁ x) = Added P x
Added (P `+ Q) (inj₂ y) = Added Q y
Added (P `× Q) (p , q) = Added P p × Added Q q 
Added (`Σ T⁺) (s , xs) = Added (T⁺ s) xs
Added (`Π {S} T⁺) f = (s : S) → Added (T⁺ s) (f s)
Added (`X (inv i⁺)) t = ⊤
Added (insert S D⁺) t = Σ[ s ∶ S ] Added (D⁺ s) t
Added {X = X} (deleteΣ {S}{T} replace T⁺) (s , t) = Σ[ q ∶ s ≡ replace ] Added T⁺ (subst (λ s → ⟦ T s ⟧ X) q t)
Added (deleteInj₁ P⁺) (inj₁ x) = Added P⁺ x
Added (deleteInj₁ P⁺) (inj₂ y) = ⊥
Added (deleteInj₂ Q⁺) (inj₁ x) = ⊥
Added (deleteInj₂ Q⁺) (inj₂ y) = Added Q⁺ y


Args : ∀{D' : IDesc I}(O : Ornament f D')(xs' : ⟦ D' ⟧ (μ D)) → Added O xs' → Ornament forgetIdx  (⟦ O ⟧Orn)
Args `1 tt tt = `1
Args (P⁺ `+ Q⁺) (inj₁ x) a = deleteInj₁ (Args P⁺ x a)
Args (P⁺ `+ Q⁺) (inj₂ y) a = deleteInj₂ (Args Q⁺ y a)
Args (P⁺ `× Q⁺) (p , q) (ap , aq) = Args P⁺ p ap `× Args Q⁺ q aq
Args (`Σ {S} {T} T⁺) (s , xs) a = deleteΣ s (Args (T⁺ s) xs a)
Args (`Π {S} {T} T⁺) f a = `Π (λ s → Args (T⁺ s) (f s) (a s)) 
Args .{`X (f i⁺)} (`X (inv i⁺)) t tt = `X (inv (i⁺ , t))
Args (insert S D⁺) xs (s , a) = deleteΣ s (Args (D⁺ s) xs a)
Args (deleteΣ {S} {T} replace T⁺) (.replace , xs) (refl , a) = Args T⁺ xs a
Args (deleteInj₁ P⁺) (inj₁ x) q = Args P⁺ x q
Args (deleteInj₁ P⁺) (inj₂ y) ()
Args (deleteInj₂ Q⁺) (inj₁ x) ()
Args (deleteInj₂ Q⁺) (inj₂ y) q = Args Q⁺ y q


ornamentalOrnament : Orn forgetIdx  ⟦ D ⁺ O ⟧Orn
ornamentalOrnament (i⁺ , con xs) = insert (Added (O i⁺) xs) λ ad → 
                                   Args (O i⁺) xs ad

ornamentalData : Σ I⁺ (μ D ∘ f) → IDesc (Σ I⁺ (μ D ∘ f))
ornamentalData = ⟦ ⟦ D ⁺ O ⟧Orn ⁺ ornamentalOrnament ⟧Orn


-- * 

forgetAll : ∀{ix t} → μ ornamentalData (ix , t) → μ D (f ix)
forgetAll {ix}{t} _  = t

forgetOrnAlg : ∀{ix t} → μ ornamentalData (ix , t) → μ ⟦ D ⁺ O ⟧Orn ix
forgetOrnAlg x = Ornament.OrnamentalAlgebra.forgetOrnament ⟦ D ⁺ O ⟧Orn proj₁ ornamentalOrnament x


-- Can't be bothered to reimplement
postulate 
  makeOrnAlg : ∀{i⁺} → (t : μ ⟦ D ⁺ O ⟧Orn i⁺) → μ ornamentalData (i⁺ , forgetOrnament t)

-- Can't be bothered to reimplement
postulate
  ornOAAO⊢ : ∀{i⁺}{t : μ D (f i⁺)} → (t⁺ : μ ornamentalData (i⁺ , t)) → t ≡ forgetOrnament (forgetOrnAlg t⁺)

