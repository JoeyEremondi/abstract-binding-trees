{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.List using (List; []; _∷_; length; map; foldl)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties
    using (+-suc; ≤-trans; ≤-step; ≤-refl; ≤-reflexive; m≤m+n; ≤-pred;
    m≤m⊔n; n≤m⊔n; m≤n⇒m<n∨m≡n; m≤n⇒m≤o⊔n)
open import Data.Product
    using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec as Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Level using (levelOfType)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import ListAux
open import Sig
open import Var
open import Data.Maybe
open import Data.Vec.Relation.Unary.All

{----- Predicate on ABT's (e.g. type system for expressions) -----}

module NaryPredicate {ℓ}{I : Set ℓ}
  (Op : Set) (sig : Op → List Sig)
  (arity : ℕ)
  -- Relational representation of nary functions, or "indexed" relations
  -- We're ulimately building the relation f [t₁ ... tₙ] ≔ i : Vec ABT n -> I -> Set
  -- Variable case:
  -- 𝑉 : variable case
  -- f (x₁ ... xₙ) ≔ i
  -- i.e. output for n variables
  (𝑉 : List I → Vec Var arity → I → I → Set)
  -- 𝐵
  -- e.g. "base case" defaults where we can determine i : I simply from some of the op-codes
  (𝐵 : List I → Vec (Maybe Op) arity → I → Set)
  -- Recursive case
  -- Given an op-code, the index of the element-wise comparison of each child,
  -- and the index for each bound variable,
  -- and the overall index
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set) where

open import AbstractBindingTree Op sig
open import Data.Product

private
  variable
    x⃗ : Vec Var arity
    b : Sig
    A B : I
    A⃗ B⃗ : I
    Γ : List I
    M⃗ : Vec ABT arity

-- Given a (Maybe Op), check if either it's nothing, or the given ABT matches op
data MOps : ∀ {n}  -> Vec (Maybe Op) n -> Vec ABT n -> Set where
  JOp : ∀ {n op sig} {xs : Vec _ n} {ops : Vec _ n} -> MOps  ((just op) Vec.∷ ops) (op ⦅ sig ⦆ Vec.∷ xs)
  NOp : ∀ {n a} {ops : Vec _ n} {xs : Vec _ n} -> MOps (nothing Vec.∷ ops) (a Vec.∷ xs)
  []Op : MOps Vec.[] Vec.[]

data _⊢_𝑅_ : List I → Vec ABT arity → I → Set (levelOfType I)
data _∣_∣_⊢ₐ_𝑅_ : (b : Sig) → List I → BType I b → Vec (Arg b) arity → I
   → Set (levelOfType I)
data _∣_∣_⊢₊_𝑅_ : (bs : List Sig) → List I → BTypes I bs → Vec (Args bs) arity
                → Vec I (length bs) → Set (levelOfType I)

data _⊢_𝑅_ where
  var-r : All (λ x -> Γ ∋ x ⦂ A) x⃗
     →  𝑉 Γ x⃗ A B
     → Γ ⊢ (Vec.map `_ x⃗) 𝑅 B
  base-r : ∀ {Γ mop⃗ M⃗} -> MOps mop⃗ M⃗  -> 𝐵 Γ mop⃗ A -> Γ ⊢ M⃗ 𝑅 A
  op-r : ∀{op}{args⃗  : Vec ( Args (sig op)) arity}{As : Vec I (length (sig op))}
           {Bs : BTypes I (sig op)}
     → (sig op) ∣ Γ ∣ Bs  ⊢₊ args⃗ 𝑅 As
     → 𝑃 op As  Bs  A
     → Γ ⊢ Vec.map (λ args → op ⦅ args ⦆) args⃗ 𝑅 A

data _∣_∣_⊢ₐ_𝑅_ where
  ast-p : Γ ⊢ M⃗ 𝑅 A
     → ■ ∣ Γ ∣ tt ⊢ₐ Vec.map ast M⃗ 𝑅 A

  bind-p : ∀{b Bs arg⃗}
     → b ∣ (B ∷ Γ) ∣ Bs ⊢ₐ arg⃗ 𝑅 A
     → ν b ∣ Γ ∣ ⟨ B , Bs ⟩ ⊢ₐ Vec.map bind arg⃗ 𝑅 A

  clear-p : ∀{Bs arg⃗ }
     → b ∣ [] ∣ Bs ⊢ₐ arg⃗ 𝑅 A
     → ∁ b ∣ Γ ∣ Bs ⊢ₐ Vec.map clear arg⃗ 𝑅 A

data _∣_∣_⊢₊_𝑅_ where
  nil-p : [] ∣ Γ ∣ tt ⊢₊ Vec.replicate nil 𝑅 []̌
  cons-p : ∀{b bs}{arg⃗ args⃗}{As}{Bs}{Bss}
     → b ∣ Γ ∣ Bs ⊢ₐ arg⃗ 𝑅 A  →  bs ∣ Γ ∣ Bss ⊢₊ args⃗ 𝑅 As
     → (b ∷ bs) ∣ Γ ∣ ⟨ Bs , Bss ⟩ ⊢₊ (Vec.map cons arg⃗) Vec.⊛ args⃗ 𝑅 (A ∷̌ As) -- (b ∷ bs) ∣ Γ ∣ ⟨ Bs , Bss ⟩ ⊢₊ cons arg args 𝑅 (A ∷̌ As)
