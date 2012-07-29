open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import Data.IDesc
open import Data.Fixpoint
open import Data.Cata
open import Data.Induction

open import Ornament.Ornament
import Ornament.OrnamentalAlgebra

module Ornament.AlgebraicOrnament 
           {I : Set}
           (D : I → IDesc I)
           (X : I → Set)
           (α : ∀{i} → ⟦ D i ⟧ X → X i)
  where

I⁺ : Set
I⁺ = Σ I X

forget : I⁺ → I
forget = proj₁

algOrnHelp : (D : IDesc I)(xs : ⟦ D ⟧ X) → Ornament forget D
algOrnHelp `0 ()
algOrnHelp `1 tt = `1
algOrnHelp (`X i') xs = `X (inv (i' , xs))
algOrnHelp (P `+ Q) (inj₁ x) = deleteInj₁ (algOrnHelp P x)
algOrnHelp (P `+ Q) (inj₂ y) = deleteInj₂ (algOrnHelp Q y)
algOrnHelp (P `× Q) (p , q) = algOrnHelp P p `× algOrnHelp Q q
algOrnHelp (`Σ S T) (s , xs) = deleteΣ s (algOrnHelp (T s) xs)
algOrnHelp (`Π S T) xs = `Π (λ s → algOrnHelp (T s) (xs s))

algOrn : Orn forget D
algOrn (i , i⁺) = insert (⟦ D i ⟧ X) λ xs → 
                  insert (α xs ≡ i⁺) λ q → 
                  algOrnHelp (D i) xs 

algData : I⁺ → IDesc I⁺
algData = ⟦ D ⁺ algOrn ⟧Orn

open Ornament.OrnamentalAlgebra D forget algOrn


-- Can't be bothered to reimplement
postulate 
  makeAlg : ∀{i} → (x : μ D i) → μ algData (i , foldID D α x)

-- Thanks to Andrea Vezzosi:
OAAO⊢ : ∀{i}{x : X i} → (t : μ algData (i , x)) → x ≡ foldID D α (forgetOrnament t)
OAAO⊢ {i} {x} = 
  induction algData motive 
            (λ { {j , .(α x)} (x , refl , t) hs → cong α (aux (D j) (x , t) hs)}) 
  where
    motive : {i' : Σ I X} → μ ⟦ D ⁺ algOrn ⟧Orn i' → Set
    motive {ij} t = proj₂ ij ≡ foldID D α (forgetOrnament t)
    aux : (E : IDesc I)
          (xs
           : Σ (⟦ E ⟧ X)
             (λ s →
                ⟦ ⟦ algOrnHelp E s ⟧Orn ⟧ (μ ⟦ D ⁺ algOrn ⟧Orn)))
          →
          □ ⟦ algOrnHelp E (proj₁ xs) ⟧Orn (proj₂ xs) motive →
          proj₁ xs ≡
          Fold.hyps D α E
          (forgetMap0 (algOrnHelp E (proj₁ xs))
           (Fold.hyps ⟦ D ⁺ algOrn ⟧Orn
            (ornAlgebra) ⟦ algOrnHelp E (proj₁ xs) ⟧Orn
            (proj₂ xs)))
    aux `0 (() , _) hs
    aux `1 (tt , tt) hs = refl
    aux (`X i0) (x' , con t) hs = hs
    aux (l `× r) (x' , t) hs = (cong₂ _,_ (aux l ((proj₁ x' , proj₁ t)) (proj₁ hs)) (aux r (proj₂ x' , proj₂ t) (proj₂ hs)))
    aux (l `+ r) (inj₁ x' , t) hs = cong inj₁ (aux l (x' , t) hs)
    aux (l `+ r) (inj₂ y , t) hs = cong inj₂ (aux r (y , t) hs)
    aux (`Σ S T) ((s , x') , t) hs = cong (_,_ s) (aux (T s) (x' , t) hs)
    aux (`Π S T) (x' , t) hs = ext λ s → aux (T s) (x' s , t s) (hs s) where
      postulate
        ext : ∀ {S : Set}{T : S -> Set} -> {f g : (x : S) -> T x} -> (∀ x -> f x ≡ g x) -> f ≡ g
