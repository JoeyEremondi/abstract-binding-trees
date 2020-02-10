{-

  This is an example of using Abstract Binding Trees to define the
  untyped lambda calculus.

-}

module examples.Lambda where

import Syntax
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Op : Set where
  op-lam : Op
  op-app : Op

sig : Op → List ℕ
sig op-lam = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []

open Syntax Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; exts; _•_; id)
  renaming (ABT to Term)

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

sub-app : ∀ (L M : Term) (σ : Subst) → ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app = λ L M σ → refl

sub-lam : ∀ (N : Term) (σ : Subst) → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ exts σ ⟫ N)
sub-lam = λ N σ → refl 

_ : ∀ M L → ⟪ M • L • id ⟫ (` 0) ≡ M
_ = λ M L → refl

_ : ∀ M L → ⟪ M • L • id ⟫ (` 1) ≡ L
_ = λ M L → refl

_ : ∀ M L → ⟪ M • L • id ⟫ (` 2) ≡ ` 0
_ = λ M L → refl

_ : ∀ M L → ⟪ M • L • id ⟫ (` 3) ≡ ` 1
_ = λ M L → refl

_ : ∀ M L → ⟪ M • L • id ⟫ (` 1 · ` 0) ≡ L · M
_ = λ M L → refl

_ : ∀ M → ⟪ M • id ⟫ (` 1 · ` 0) ≡ ` 0 · M
_ = λ M → refl

_ : ∀ N L → ((` 1 · ` 0) [ N ] ) [ L ] ≡ (L · N [ L ])
_ = λ N L → refl

infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M : Term}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {L M M′ : Term}
    → M —→ M′
      ---------------
    → L · M —→ L · M′

  ξ-ƛ : ∀ {N N′ : Term}
    → N —→ N′
      ---------------
    → (ƛ N) —→ (ƛ N′)

  β-ƛ : ∀ {N M : Term}
      --------------------
    → (ƛ N) · M —→ N [ M ]

_ : ∀ L M → (ƛ ((ƛ (` 0 · ` 1)) · M)) · L
         —→ (ƛ (M · ` 0)) · L
_ = λ L M → ξ-·₁ (ξ-ƛ β-ƛ)
