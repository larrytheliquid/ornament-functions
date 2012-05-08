module Examples.RenameKit where

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Bool

open import Relation.Binary.PropositionalEquality

open import Data.IDesc
open import Data.Fixpoint
open import Data.Cata
open import Data.Induction

open import Ornament.Ornament
open import Ornament.OrnamentalAlgebra



-- * Untyped Lambda-calculus

-- ** UContext

-- *** Definition

-- data UContext : Set where
--   ε : UContext
--   suc : (n : UContext) → UContext

data UContextConst : Set where
  `ε `∙∷ : UContextConst

UContextD : ⊤ → IDesc ⊤
UContextD tt = `Σ UContextConst help
  where help : UContextConst → IDesc ⊤
        help `ε = `1
        help `∙∷ = `X tt

UContext : Set
UContext = μ UContextD tt

-- *** Constructors

ε : UContext
ε = con (`ε , tt)

∙∷ : UContext → UContext
∙∷ n = con (`∙∷ , n )

-- *** View

data UContext-View : UContext → Set where
  see-ε : UContext-View ε
  see-∙∷ : (Γ : UContext) → UContext-View (∙∷ Γ)

UContext-view : (Γ : UContext) → UContext-View Γ
UContext-view (con (`ε , tt)) = see-ε
UContext-view (con (`∙∷ , Γ)) = see-∙∷ Γ

-- ** Variable:

-- *** Definition

-- data Var : UContext → Set where
--   here : ∀{Γ} → Var (suc Γ)
--   there : ∀{Γ} → (h : Var Γ) → Var (suc Γ)

data VarConst : Set where
  `here `there : VarConst

VarD : UContext → IDesc UContext
VarD Γ with UContext-view Γ 
VarD .(con (`ε , tt)) | see-ε = `Σ ⊥ λ _ → `1
VarD .(con (`∙∷ , Γ)) | see-∙∷ Γ = `1 `+ `X Γ

Var : UContext → Set
Var = μ VarD


-- *** Constructors

here : ∀{Γ} → Var (∙∷ Γ)
here = con (inj₁ tt)

there : ∀{Γ} → Var Γ → Var (∙∷ Γ)
there x = con (inj₂ x)


-- *** View

data Var-View : ∀{Γ} → Var Γ → Set where
  see-here : ∀{Γ} → Var-View {∙∷ Γ} here
  see-there : ∀{Γ} → (h : Var Γ) → Var-View (there h)

Var-view : ∀{Γ} → (v : Var Γ) → Var-View v
Var-view {Γ} v with UContext-view Γ 
Var-view (con (() , _)) | see-ε
Var-view (con (inj₁ tt)) | see-∙∷ Γ = see-here
Var-view (con (inj₂ x)) | see-∙∷ Γ = see-there x

-- ** Term:

-- *** Definition

-- data Term (n : UContext) : Set where
--   var : (v : Var n) → Term n
--   λam : (b : Term (suc n)) → Term n
--   _∙_ : (f s : Term n) → Term n

data TermConst : Set where
  `var `λam `∙ : TermConst

TermD : UContext → IDesc UContext
TermD Γ = `Σ TermConst help
  where help : TermConst → IDesc UContext
        help `var = `Σ (Var Γ) λ _ → `1
        help `λam = `X (∙∷ Γ)
        help `∙ = `X Γ `× `X Γ

Term : UContext → Set
Term = μ TermD

-- *** Constructors

var : {Γ : UContext} → (v : Var Γ) → Term Γ
var v = con (`var , v , tt)

λam : {Γ : UContext} → (b : Term (∙∷ Γ)) → Term Γ
λam b = con (`λam , b)

_∙_ : {Γ : UContext} → (f s : Term Γ) → Term Γ
f ∙ s = con (`∙ , f , s)

-- *** View

data Term-View {Γ : UContext} : Term Γ → Set where
  see-var : (v : Var Γ) → Term-View (var v)
  see-λam : (b : Term (∙∷ Γ)) → Term-View (λam b)
  see-∙ : (f s : Term Γ) → Term-View (f ∙ s)

Term-view : {Γ : UContext} → (tm : Term Γ) → Term-View tm
Term-view (con (`var , v , tt)) = see-var v
Term-view (con (`λam , b)) = see-λam b
Term-view (con (`∙ , f , s)) = see-∙ f s

-- **  Environment:

UEnv : (UContext → Set) → UContext → UContext → Set
UEnv T m n = Var m → T n

-- ** Substitution kit:

record Subst (T : UContext → Set) : Set where
  field
    mkVar : ∀{Γ} → Var Γ → T Γ
    mkAbs : ∀{Γ} → T Γ → T (∙∷ Γ)
    mkTerm : ∀{Γ} → T Γ → Term Γ
open Subst public


weaken : ∀{T Γ Δ} → Subst T → UEnv T Γ Δ → UEnv T (∙∷ Γ) (∙∷ Δ)
weaken S ρ v with Var-view v
weaken {T} {Γ} S ρ .(con (inj₁ tt)) | see-here = mkVar S here
weaken {T} {Γ} S ρ .(con (inj₂ h)) | see-there h = mkAbs S (ρ h)

action : ∀{T Γ Δ} → Subst T → UEnv T Γ Δ → Term Γ → Term Δ
action S ρ tm with Term-view tm 
action S ρ .(con (`var , v , tt)) | see-var v = mkTerm S (ρ v)
action S ρ .(con (`λam , b)) | see-λam b = λam (action S (weaken S ρ) b)
action S ρ .(con (`∙ , f , s)) | see-∙ f s = action S ρ f ∙ action S ρ s


renameKit : Subst Var 
renameKit = record { mkVar = \n → n 
                   ; mkAbs = there
                   ; mkTerm = var }

substKit : Subst Term
substKit = record { mkVar = var
                  ; mkAbs = action renameKit there
                  ; mkTerm = \tm → tm }


-- * Simply typed lambda-calculus

-- ** Types

infixr 50 _⇒_
--infixl 40 _∷_

data Type : Set where
  ■ : Type
  _⇒_ : (S T : Type) → Type

-- ** Context

-- *** Definition

-- data Context : Set where
--   ε : Context
--   _∷_ : (Γ : Context)(T : Type) → Context

ContextO : Orn (λ tt → tt) UContextD
ContextO tt = `Σ help
  where help : (s : UContextConst) → Ornament (λ tt → tt) _
        help `ε = `1
        help `∙∷ = insert Type (λ _ → `X (inv tt))

Context : Set
Context = μ ⟦ UContextD ⁺ ContextO ⟧Orn tt

-- *** Constructors

εC : Context 
εC = con (`ε , tt)

_∷_ : (Γ : Context)(T : Type) → Context
Γ ∷ T = con (`∙∷ , T , Γ)

-- *** View

data Context-View : Context → Set where
  see-ε : Context-View εC
  see-∷ : (Γ : Context)(T : Type) → Context-View (Γ ∷ T)

Context-view : (Γ : Context) → Context-View Γ
Context-view (con (`ε , tt)) = see-ε
Context-view (con (`∙∷ , T , Γ)) = see-∷ Γ T

-- *** Forget

forgetContext : Context → UContext
forgetContext = forgetOrnament UContextD (λ tt → tt) ContextO

-- ** Variable

-- *** Definition

-- TODO: Obtain by pullback?

-- data _∈_ (T : Type) : Context → Set where
--   here : ∀{Γ} → T ∈ Γ ∷ T
--   there : ∀{Γ T'} → (h : T ∈ Γ) → T ∈ Γ ∷ T'

forgetTVarIdx : Type × Context → UContext
forgetTVarIdx (T , Γ) = forgetContext Γ

TVarO : Orn forgetTVarIdx VarD
TVarO (T , Γ) with Context-view Γ 
TVarO (T , .(con (`ε , tt))) | see-ε = `Σ λ _ → `1
TVarO (T , .(con (`∙∷ , T' , Γ))) | see-∷ Γ T' = (insert (T' ≡ T) (λ _ → `1)) `+ `X (inv (T , Γ))


TVar : Type → Context → Set
TVar T Γ = μ ⟦ VarD ⁺ TVarO ⟧Orn (T , Γ)


-- *** Constructors

hereT : ∀{Γ : Context}{T} → TVar T (Γ ∷ T)
hereT {Γ}{T} = con (inj₁ (refl , tt))

thereT : ∀{Γ T T'} → TVar T Γ → TVar T (Γ ∷ T')
thereT {Γ}{T}{T'} h = con (inj₂ h)


-- *** View

data TVar-View {T : Type} : ∀{Γ} → TVar T Γ → Set where
  see-here : ∀{Γ} → TVar-View (hereT {Γ} {T})
  see-there : ∀{Γ T'} → (h : TVar T Γ) → TVar-View (thereT {Γ}{T}{T'} h)

TVar-view : ∀{T Γ} → (v : TVar T Γ) → TVar-View v
TVar-view {Γ = Γ} v with Context-view Γ 
TVar-view (con (() , _)) | see-ε
TVar-view {T} (con (inj₁ (refl , tt))) | see-∷ Γ .T = see-here
TVar-view (con (inj₂ h)) | see-∷ Γ T = see-there h

-- *** Forget

forgetTVar : ∀{T Γ} → TVar T Γ → Var (forgetContext Γ)
forgetTVar = forgetOrnament VarD forgetTVarIdx TVarO 

-- ** Term

-- *** Definition

-- data _⊢_ (Γ : Context) : Type → Set where
--   var : ∀{T} → (v : T ∈ Γ) → Γ ⊢ T
--   λam : ∀{S T} → (b : Γ ∷ S ⊢ T) → Γ ⊢ S ⇒ T
--   _∙_ : ∀{S T} → (f : Γ ⊢ S ⇒ T)(s : Γ ⊢ S) → Γ ⊢ T

forgetTermIdx : Context × Type → UContext
forgetTermIdx (Γ , T) = forgetContext Γ

TermTO : Orn forgetTermIdx TermD
TermTO (Γ , T) = `Σ help
  where help : (t : TermConst) → Ornament forgetTermIdx _
        help `var = insert (TVar T Γ) (λ v → deleteΣ (forgetTVar v) `1)
        help `λam = insert Type (λ A → 
                    insert Type (λ B → 
                    insert (T ≡ A ⇒ B) (λ _ → 
                    `X (inv (Γ ∷ A , B)))))
        help `∙ = insert Type (λ S →
                  `X (inv (Γ , S ⇒ T)) `× `X (inv (Γ , S)))

TermT : Context → Type → Set
TermT Γ T = μ ⟦ TermD ⁺ TermTO ⟧Orn (Γ , T)


-- *** Constructors

varT : ∀{Γ T} → TVar T Γ → TermT Γ T
varT v = con (`var , v , tt)

λamT : ∀{Γ S T} → TermT (Γ ∷ S) T → TermT Γ (S ⇒ T)
λamT b = con (`λam , _ , _ , refl , b)

_∙T_ : ∀{Γ S T} → TermT Γ (S ⇒ T) → TermT Γ S → TermT Γ T
f ∙T s = con (`∙ , _ , f , s)

-- *** View

data TermT-View {Γ : Context} : {T : Type} → TermT Γ T → Set where
  see-var : ∀{T} → (v : TVar T Γ ) → TermT-View (varT v)
  see-λam : ∀{S T} → (b : TermT (Γ ∷ S) T) → TermT-View (λamT b)
  see-∙ : ∀{S T} → (f : TermT Γ (S ⇒ T))(s : TermT Γ S) → TermT-View (f ∙T s)

TermT-view : ∀{Γ T} → (t : TermT Γ T) → TermT-View t 
TermT-view (con (`var , v , tt)) = see-var v
TermT-view {T = .(S ⇒ T)} (con (`λam , S , T , refl , b)) = see-λam b
TermT-view (con (`∙ , S , f , s)) = see-∙ f s

-- * Outro

-- Local Variables:
-- mode: outline-minor
-- outline-regexp: "-- [*\f]+"
-- outline-level: outline-level
-- End:                      
