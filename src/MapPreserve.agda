import ABTPredicate
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Environment
open import Function using (_∘_)
import Substitution
open import GenericSubstitution
{- open import ScopedTuple -}
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var

module MapPreserve (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import Fold Op sig
open import Map Op sig
open import Environment
open Shiftable {{...}}
open Quotable {{...}}
open Env {{...}}


{-------------------- MapEnv Preserves ABTPred ---------------------}

record MapPreservable (V I E : Set)
   {{_ : Shiftable V}}{{_ : Quotable V}}{{_ : Env E V}} : Set₁ where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        _⊢v_⦂_ : List I → V → I → Set
  open ABTPredicate Op sig 𝑉 𝑃 public
  field quote-⊢v : ∀{Γ v A} → Γ ⊢v v ⦂ A → Γ ⊢ “ v ” ⦂ A

open MapPreservable {{...}}

_⦂_⇒_ : ∀{V I E : Set}
   {{_ : Shiftable V}}{{_ : Quotable V}}{{_ : Env E V}}
   {{_ : MapPreservable V I E}}
   → E → List I → List I → Set
_⦂_⇒_ {V}{I}{E} σ Γ Δ = ∀(x : Var) (A : I) → Γ ∋ x ⦂ A  →  Δ ⊢v ⟅ σ ⟆ x ⦂ A


preserve-map : ∀ {E V I}{Γ Δ : List I}{σ : E}{A : I}
   {{_ : Shiftable V}}{{_ : Env E V}}{{_ : MapPreservable V I E}}
   (M : ABT)
   → Γ ⊢ M ⦂ A
   → σ ⦂ Γ ⇒ Δ
   → (∀{σ Γ Δ A} → σ ⦂ Γ ⇒ Δ → ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ))
   → Δ ⊢ map σ M ⦂ A

preserve-map (` x) (var-p ∋x 𝑉x) σ⦂ ext-pres = quote-⊢v (σ⦂ x ∋x)
preserve-map (op ⦅ args ⦆) (op-p ⊢args Pop) σ⦂ ext-pres =
    op-p (pres-args ⊢args σ⦂) Pop
    where  
    pres-arg : ∀{b Γ Δ}{arg : Arg b}{A σ Bs}
       → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A → σ ⦂ Γ ⇒ Δ
       → b ∣ Δ ∣ Bs ⊢ₐ map-arg σ {b} arg ⦂ A
    pres-args : ∀{bs Γ Δ}{args : Args bs}{As σ Bss}
       → bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As → σ ⦂ Γ ⇒ Δ
       → bs ∣ Δ ∣ Bss ⊢₊ map-args σ {bs} args ⦂ As
    pres-arg {zero} {arg = ast M} (ast-p ⊢M) σ⦂ =
        ast-p (preserve-map M ⊢M σ⦂ ext-pres)
    pres-arg {suc b} {arg = bind arg} (bind-p {B = B}{A = A} ⊢arg) σ⦂ =
        bind-p (pres-arg ⊢arg (ext-pres σ⦂))
    pres-args {[]} {args = nil} nil-p σ⦂ = nil-p
    pres-args {b ∷ bs} {args = cons arg args} (cons-p ⊢arg ⊢args) σ⦂ =
        cons-p (pres-arg ⊢arg σ⦂) (pres-args ⊢args σ⦂)


{-
map-pres-ext : ∀{σ Γ Δ A} → σ ⦂ Γ ⇒ Δ → ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  

module MapPreserveABTPred {V I : Set}
  (𝑉 : List I → Var → I → Set)
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set)
  (_⊢v_⦂_ : List I → V → I → Set)
  (quote-⊢v : ∀{Γ v A} → Γ ⊢v v ⦂ A → Γ ⊢ “ v ” ⦂ A)
  (ext-pres : ∀{σ Γ Δ A} → σ ⦂ Γ ⇒ Δ → ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ))
  where
  open ABTPredicate Op sig 𝑉 𝑃 public

{-
  𝐴 : List I → V → I → Set
  𝐴 Γ M A = ⊤
-}
  
-}

{-
{-------------------- Map Preserves ABTPred ---------------------}

record MapPreserveABTPred {V I : Set} (M : Map V) : Set₁ where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        _⊢v_⦂_ : List I → V → I → Set

  open Map M
  open Quotable V-is-Quotable
  open ABTPredicate Op sig 𝑉 𝑃 
 
  field shift-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
        quote-⊢v : ∀{Γ v A} → Γ ⊢v v ⦂ A → Γ ⊢ “ v ” ⦂ A
        ⊢v0 : ∀{B Δ} → (B ∷ Δ) ⊢v var→val 0 ⦂ B
                    
  open GSubstPred (Map.V-is-Shiftable M) _⊢v_⦂_ 
  open GenericSubst (Map.V-is-Shiftable M)

  ext-pres : ∀{σ Γ Δ A} → σ ⦂ Γ ⇒ Δ → ext-env σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-pres {σ} {Γ} {Δ} {A} σ⦂ {zero} {B} refl rewrite g-ext-def σ = ⊢v0
  ext-pres {σ} {Γ} {Δ} {A} σ⦂ {suc x} {B} ∋x
      rewrite g-ext-def σ | g-inc-shift σ x = shift-⊢v (σ⦂ {x}{B} ∋x)

  PME : MapEnvPreserveABTPred GSubst-is-MapEnv
  PME = record { 𝑉 = 𝑉 ; 𝑃 = 𝑃 ; _⊢v_⦂_ = _⊢v_⦂_ ; quote-⊢v = quote-⊢v
               ; ext-pres = ext-pres }
  open MapEnvPreserveABTPred PME hiding (ext-pres) public

-}
