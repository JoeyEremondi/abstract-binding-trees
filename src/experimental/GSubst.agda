open import Data.Nat using (ℕ; zero; suc; _+_)
open import experimental.Environment
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Var

module experimental.GSubst where

open Shiftable {{...}}

GSubst : ∀{ℓ} (V : Set ℓ) → Set ℓ
GSubst V = Var → V

↑ : (k : ℕ) → ∀{ℓ}{V : Set ℓ}{{_ : Shiftable V}} → GSubst {ℓ} V
↑ k x = var→val (k + x)

infixr 6 _•_
_•_ : ∀{ℓ}{V : Set ℓ}{{_ : Shiftable V}} → V → GSubst V → GSubst V
(v • σ) 0 = v
(v • σ) (suc x) = σ x

⟰ : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → GSubst V → GSubst V
⟰ σ x = ⇑ (σ x)

id : ∀ {ℓ}{V : Set ℓ}{{_ : Shiftable V}} → GSubst V
id = ↑ 0

ext : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → GSubst V → GSubst V
ext σ = (var→val 0) • ⟰ σ

{- obsolete, use • instead -}
_,_ : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → GSubst V → V → GSubst V
(σ , v) = v • ⟰ σ

postulate
  extensionality : ∀{ℓ₁ ℓ₂} {A : Set ℓ₁ }{B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

