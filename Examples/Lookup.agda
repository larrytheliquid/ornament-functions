module Examples.Lookup where

open import Function

open import Data.Empty
open import Data.Product
open import Data.Bool
open import Data.Fin hiding (_<_)
open import Data.Nat hiding (_<_ ; _>_)
open import Data.List
open import Data.Vec hiding (lookup)
open import Data.Maybe

open import Relation.Binary.PropositionalEquality

-- * Ornaments

-- ** List: Ornament Nat

forgetList : {A : Set} → List A → ℕ
forgetList [] = 0
forgetList (a ∷ xs) = suc (forgetList xs)

-- ** Maybe: Ornament Bool

forgetMaybe : {A : Set} → Maybe A → Bool
forgetMaybe (just a) = true
forgetMaybe nothing = false

-- * Functions

ℕ-elim : (n : ℕ)(P : ℕ → Set) → P 0 → ((n : ℕ) → P n → P (suc n)) → P n
ℕ-elim 0 P ih0 ihn = ih0
ℕ-elim (suc n) P ih0 ihn = ihn n (ℕ-elim n P ih0 ihn)

-- ** _<_

_<_ : ℕ → ℕ → Bool
m < zero = false
zero < suc n = true
suc m < suc n = m < n


-- ** lookup + proof

lookup : {A : Set} → ℕ → List A → Maybe A
lookup n [] = nothing
lookup zero (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n xs

coh⊢ : {A : Set} → (m : ℕ)(xs : List A) → (forgetMaybe (lookup m xs)) ≡ (m < (forgetList xs))
coh⊢ m [] = refl
coh⊢ zero (x ∷ xs) = refl
coh⊢ (suc n) (x ∷ xs) rewrite coh⊢ n xs = refl

-- ** vlookup

vlookup : {A : Set}{n : ℕ} → Fin n → Vec A n → A
vlookup zero (x ∷ xs) = x
vlookup (suc i) (x ∷ xs) = vlookup i xs


-- ** Vec: OAAO List by length

makeVec : {A : Set}{n : ℕ} → Σ[ l ∶ List A ] (forgetList l ≡ n) → Vec A n
makeVec ([] , refl) = []
makeVec ((x ∷ xs) , refl) = x ∷ makeVec (xs , refl)

forgetVec : {A : Set}{n : ℕ} → Vec A n → Σ[ x ∶ List A ] forgetList x ≡ n
forgetVec [] = [] , refl
forgetVec (x ∷ vs) with forgetVec vs
... | (xs , pf) = x ∷ xs , cong suc pf

-- ** IMaybe: OAAO Maybe by (_ < n)

data IMaybe (A : Set) : Bool → Set where
  nothing : IMaybe A false
  just : (a : A) → IMaybe A true

forgetIMaybe : {A : Set}{b : Bool} → IMaybe A b → Σ[ m ∶ Maybe A ] (forgetMaybe m ≡ b)
forgetIMaybe nothing = nothing , refl
forgetIMaybe (just a) = just a , refl

makeIMaybe : {A : Set}{b : Bool} → Σ[ m ∶ Maybe A ] (forgetMaybe m ≡ b) → IMaybe A b
makeIMaybe (just x , refl) = just x
makeIMaybe (nothing , refl) = nothing

-- * Getting lookup from OAAO of lookup by _ < n

vlookup' : {A : Set}{n : ℕ} → (m : ℕ) → Vec A n → IMaybe A (m < n)
vlookup' {A} {zero} m [] = nothing
vlookup' {A} {suc n} zero (a ∷ vs) = just a
vlookup' {A} {suc n} (suc m) (_ ∷ vs) = vlookup' m vs 


ψ : ∀{A n} → ((m : ℕ) → IMaybe A (m < n)) → (Fin n → A) 
ψ {A} {zero} f ()
ψ {A} {suc n} f zero with f 0
ψ {A} {suc n} f zero | just a = a
ψ {A} {suc n} f (suc i) = ψ (f ∘ suc) i 

vlookup2 : ∀{A : Set}{n} → Fin n → Vec A n → A
vlookup2 k vs = ψ (λ m → vlookup' m vs) k

lookup' : {A : Set} → ℕ → List A → Maybe A
lookup' m xs = proj₁ (forgetIMaybe (vlookup' m (makeVec (xs , refl))))

coh'⊢ : {A : Set} (m : ℕ)(xs : List A) → forgetMaybe (lookup' m xs) ≡ m < (forgetList xs)
coh'⊢ m xs = proj₂ (forgetIMaybe (vlookup' m (makeVec (xs , refl))))

-- * Getting lookup of vlookup transported over OAAO lookup by _ < n

φ : ∀{A n} → (Fin n → A) → ((m : ℕ) → IMaybe A (m < n))
φ {A} {zero} f m = nothing
φ {A} {suc n} f zero = just (f zero)
φ {A} {suc n} f (suc m) = φ (f ∘ suc) m

lookup'' : {A : Set} → ℕ → List A → Maybe A
lookup'' m xs = proj₁ (forgetIMaybe (φ (λ m → vlookup m (makeVec (xs , refl))) m))

coh''⊢ : {A : Set} (m : ℕ)(xs : List A) → forgetMaybe (lookup'' m xs) ≡ m < (forgetList xs)
coh''⊢ m xs = proj₂ (forgetIMaybe (φ (λ m → vlookup m (makeVec (xs , refl))) m))

-- * Getting lookup "directly" from vlookup

data Either : ℕ → ℕ → Set where
  yes : ∀{n} → (k : Fin n) → Either (toℕ k) n
  no : ∀{m n} → (q : false ≡ m < n) → Either m n

forgetFin : ∀{n} → (k : Fin n) → true ≡ toℕ k < n
forgetFin zero = refl
forgetFin (suc i) = forgetFin i

makeFin : ∀{A} → (m : ℕ)(xs : List A) → Either m (forgetList xs)
makeFin m [] = no refl
makeFin zero (x ∷ xs) = yes zero
makeFin (suc m) (x ∷ xs) with forgetList xs | makeFin m xs 
makeFin (suc m) (x ∷ xs) | n | no q = no q
makeFin (suc .(toℕ k)) (x ∷ xs) | n | yes k = yes (suc k)

lookup3 :  {A : Set} → (m : ℕ)(xs : List A) → Σ[ ma ∶ Maybe A ] forgetMaybe ma ≡ m < (forgetList xs)
lookup3 m xs with inspect (forgetList xs) | makeFin m xs 
lookup3 .(toℕ k) xs | q | yes k = just (vlookup k (makeVec (xs , refl))) , forgetFin k
lookup3 m xs | q | no p = nothing , p

lookup0 :  {A : Set} → ℕ → List A → Maybe A
lookup0 m xs = proj₁ (lookup3 m xs)

coh0⊢ : {A : Set} → (m : ℕ)(xs : List A) → forgetMaybe (lookup0 m xs) ≡ m < (forgetList xs)
coh0⊢ m xs = proj₂ (lookup3 m xs)
