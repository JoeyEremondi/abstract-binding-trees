{---------------------------

  Preservation of a predicate

      Let "I" be the kind for type-like things.

      A : I
      Γ Δ : List I

  preserve-fold : ∀{M σ Γ Δ A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ fold σ M ⦂ A

  preserve-map : ∀{M σ Γ Δ A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢ map-abt σ M ⦂ A

 ---------------------------}

open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)

module Preserve (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import GenericSubstitution
open import Data.Empty using (⊥)
open import Fold Op sig
open import Map Op sig
open import ScopedTuple
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
open import Var

_∋_⦂_ : ∀{I : Set} → List I → Var → I → Set
_∋_⦂_ {I} [] x A = ⊥
_∋_⦂_ {I} (B ∷ Γ) zero A = A ≡ B
_∋_⦂_ {I} (B ∷ Γ) (suc x) A = Γ ∋ x ⦂ A

∋++ : ∀{I}{Γ Δ : List I}{x A} →  Γ ∋ x ⦂ A  → (Δ ++ Γ) ∋ (length Δ + x) ⦂ A  
∋++ {I}{Γ} {[]} {x} {A} ∋ΔΓ = ∋ΔΓ
∋++ {I}{Γ} {B ∷ Δ} {x} {A} ∋ΔΓ = ∋++ {I}{Γ}{Δ}{x}{A} ∋ΔΓ

{--- types for bound variables ---}

BType : Set → ℕ → Set
BType I zero = ⊤
BType I (suc b) = I × BType I b

BTypes : Set → List ℕ → Set
BTypes I [] = ⊤
BTypes I (b ∷ bs) = BType I b × BTypes I bs

{----- Predicate on ABT's (e.g. type system for expressions) -----}

module ABTPred {I : Set}
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set) where

  data _⊢_⦂_ : List I → ABT → I → Set
  data _∣_∣_⊢a_⦂_ : (b : ℕ) → List I → BType I b → Arg b → I → Set 
  data _∣_∣_⊢as_⦂_ : (bs : List ℕ) → List I → BTypes I bs → Args bs
                  → Vec I (length bs) → Set
  
  data _⊢_⦂_ where
    var-p : ∀{Γ x A}
       → Γ ∋ x ⦂ A   {- use a predicate here too? -}
       → Γ ⊢ ` x ⦂ A
    op-p : ∀{Γ op}{args : Args (sig op)}{A}{As : Vec I (length (sig op))}
             {Bs : BTypes I (sig op)}
       → (sig op) ∣ Γ ∣ Bs ⊢as args ⦂ As
       → 𝑃 op As Bs A
       → Γ ⊢ op ⦅ args ⦆ ⦂ A

  data _∣_∣_⊢a_⦂_ where
    ast-a : ∀{Γ}{M}{A}  →  Γ ⊢ M ⦂ A  →  0 ∣ Γ ∣ tt ⊢a ast M ⦂ A
       
    bind-a : ∀{b}{B Bs Γ arg A} → b ∣ (B ∷ Γ) ∣ Bs ⊢a arg ⦂ A
       → (suc b) ∣ Γ ∣ ⟨ B , Bs ⟩ ⊢a bind arg ⦂ A

  data _∣_∣_⊢as_⦂_ where
    nil-a : ∀{Γ} → [] ∣ Γ ∣ tt ⊢as nil ⦂ []̌ 
    cons-a : ∀{b bs}{arg args}{Γ}{A}{As}{Bs}{Bss}
       → b ∣ Γ ∣ Bs ⊢a arg ⦂ A  →  bs ∣ Γ ∣ Bss ⊢as args ⦂ As
       → (b ∷ bs) ∣ Γ ∣ ⟨ Bs , Bss ⟩ ⊢as cons arg args ⦂ (A ∷̌ As)

{----- Predicate on result of fold (e.g. type system for values) -----}

module FoldPred {I : Set}{V C : Set}
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set)
  (𝐴 : List I → V → I → Set)
  (_⊢v_⦂_ : List I → V → I → Set) (_⊢c_⦂_ : List I → C → I → Set)
  (Env : Substable V) where
  open GenericSubst Env

  data _∣_∣_⊢r_⦂_ : (b : ℕ) → List I → BType I b → Bind V C b → I → Set where
    ast-r : ∀{Δ}{c}{A}  →  Δ ⊢c c ⦂ A  →  0 ∣ Δ ∣ tt ⊢r c ⦂ A
    bind-r : ∀{b A B Bs Δ f}
          → (∀{v} → (B ∷ Δ) ⊢v v ⦂ B → 𝐴 (B ∷ Δ) v B
                  → b ∣ (B ∷ Δ) ∣ Bs ⊢r (f v) ⦂ A)
          → (suc b) ∣ Δ ∣ ⟨ B , Bs ⟩ ⊢r f ⦂ A

  ⊢r→⊢c : ∀{Δ}{Bs}{c}{A}  →  0 ∣ Δ ∣ Bs ⊢r c ⦂ A  →  Δ ⊢c c ⦂ A
  ⊢r→⊢c {Δ}{Bs}{c}{A} (ast-r ⊢cc) = ⊢cc

  data _∣_∣_⊢rs_⦂_ : ∀(bs : List ℕ) → List I → BTypes I bs
                → Tuple bs (Bind V C) → Vec I (length bs) → Set where
    nil-r : ∀{Δ} → [] ∣ Δ ∣ tt ⊢rs tt ⦂ []̌ 
    cons-r : ∀{b bs r rs Δ A As Bs Bss} → b ∣ Δ ∣ Bs ⊢r r ⦂ A
        → bs ∣ Δ ∣ Bss ⊢rs rs ⦂ As
        → (b ∷ bs) ∣ Δ ∣ ⟨ Bs , Bss ⟩ ⊢rs ⟨ r , rs ⟩ ⦂ (A ∷̌ As)

  _⦂_⇒_ : GSubst V → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v ⧼ σ ⧽ x ⦂ A

{-------------------- Preserve Fold ---------------------}

record PreserveFold {V C I : Set} (F : Fold V C) : Set₁ where
  field 𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        𝐴 : List I → V → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        _⊢c_⦂_ : List I → C → I → Set

  open Fold F ; open Substable S ; open GenericSubst S 
  open ABTPred 𝑃 public ; open FoldPred 𝑃 𝐴 _⊢v_⦂_ _⊢c_⦂_ S public

  field ext-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
        ∋→⊢v-var→val : ∀{Γ x A} → Γ ∋ x ⦂ A → Γ ⊢v var→val x ⦂ A
        ret-pres : ∀{v}{Δ}{A} → Δ ⊢v v ⦂ A → Δ ⊢c (ret v) ⦂ A
        op-pres : ∀ {op}{Rs}{Δ}{A : I}{As : Vec I (length (sig op))}{Bs}
             → sig op ∣ Δ ∣ Bs ⊢rs Rs ⦂ As
             → 𝑃 op As Bs A
             → Δ ⊢c (fold-op op Rs) ⦂ A

  ext-env : ∀{v σ Γ Δ A} → (A ∷ Δ) ⊢v v ⦂ A → 𝐴 (A ∷ Δ) v A
           → σ ⦂ Γ ⇒ Δ → (g-extend v σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-env {v} {σ} {Γ} {Δ} {A} ⊢v⦂ Av σ⦂ {zero} {B} refl = ⊢v⦂
  ext-env {v} {σ} {Γ} {Δ} {A} ⊢v⦂ Av σ⦂ {suc x} {B} ∋x
      rewrite g-inc-shift σ x = ext-⊢v (σ⦂ {x}{B} ∋x)
  
  preserve-fold : ∀{M σ Γ Δ A} → Γ ⊢ M ⦂ A → σ ⦂ Γ ⇒ Δ → Δ ⊢c fold σ M ⦂ A
  pres-arg : ∀{b Γ Δ}{arg : Arg b}{A σ Bs} → b ∣ Γ ∣ Bs ⊢a arg ⦂ A → σ ⦂ Γ ⇒ Δ
     → b ∣ Δ ∣ Bs ⊢r fold-arg  σ {b} arg ⦂ A
  pres-args : ∀{bs Γ Δ}{args : Args bs}{As σ Bss} → bs ∣ Γ ∣ Bss ⊢as args ⦂ As
     → σ ⦂ Γ ⇒ Δ  →  bs ∣ Δ ∣ Bss ⊢rs fold-args σ args ⦂ As
  preserve-fold {` x} {σ} {Γ} {Δ} {A} (var-p ∋x) σ⦂ = ret-pres (σ⦂ ∋x)
  preserve-fold {op ⦅ args ⦆} {σ} {Γ} {Δ} {A} (op-p ⊢args 𝑃op) σΓΔ =
      op-pres  (pres-args  ⊢args σΓΔ) 𝑃op
  pres-arg {zero}{Γ}{Δ}{ast M}{A}{σ} (ast-a ⊢arg) σΓΔ =
      ast-r (preserve-fold ⊢arg σΓΔ)
  pres-arg {suc b}{Γ}{Δ}{bind arg}{A}{σ}{⟨ B , Bs ⟩} (bind-a {b}{B} ⊢arg)
      σΓΔ = bind-r G
      where G : ∀{v} → (B ∷ Δ) ⊢v v ⦂ B
               → 𝐴 (B ∷ Δ) v B
               → b ∣ B ∷ Δ ∣ Bs ⊢r fold-arg σ (bind arg) v ⦂ A
            G {v} ⊢v⦂B 𝐴Mv =
                pres-arg ⊢arg (λ {x} → ext-env {v}{σ}{Γ} ⊢v⦂B 𝐴Mv σΓΔ {x})
  pres-args {[]} {Γ} {Δ} {nil} {[]̌} ⊢args σΓΔ = nil-r 
  pres-args {b ∷ bs} {Γ} {Δ} {cons arg args} {A ∷̌ As}
      (cons-a ⊢arg ⊢args) σΓΔ =
      cons-r  (pres-arg {b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)

{-------------------- Preserve Fold ---------------------}

record PreserveMap {V I : Set} (M : Map V) : Set₁ where
  field 𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        ∋→⊢v-var→val : ∀{Γ x A} → Γ ∋ x ⦂ A
                   → Γ ⊢v Substable.var→val (Map.S M) x ⦂ A

  open Map M ; open Substable S ; open GenericSubst S
  open ABTPred 𝑃 public
 
  field ext-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
        ⊢v→⊢ : ∀{Γ v A} → Γ ⊢v v ⦂ A → Γ ⊢ “ v ” ⦂ A
        ⊢v0 : ∀{B Δ} → (B ∷ Δ) ⊢v var→val 0 ⦂ B
                    
  𝐴 : List I → V → I → Set
  𝐴 Γ M A = ⊤

  open FoldPred {I}{V}{V} 𝑃 𝐴 _⊢v_⦂_ _⊢v_⦂_ S public

  ext-env : ∀{σ Γ Δ A} → σ ⦂ Γ ⇒ Δ → (g-ext σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-env {σ} {Γ} {Δ} {A} σ⦂ {zero} {B} refl rewrite g-ext-def σ = ⊢v0
  ext-env {σ} {Γ} {Δ} {A} σ⦂ {suc x} {B} ∋x
      rewrite g-ext-def σ | g-inc-shift σ x = ext-⊢v (σ⦂ {x}{B} ∋x)

  preserve-map : ∀{M σ Γ Δ A}
        → Γ ⊢ M ⦂ A
        → σ ⦂ Γ ⇒ Δ
        → Δ ⊢ map-abt σ M ⦂ A
        
  pres-arg : ∀{b Γ Δ}{arg : Arg b}{A σ Bs}
        → b ∣ Γ ∣ Bs ⊢a arg ⦂ A → σ ⦂ Γ ⇒ Δ
        → b ∣ Δ ∣ Bs ⊢a map-arg σ {b} arg ⦂ A
  pres-args : ∀{bs Γ Δ}{args : Args bs}{As σ Bss}
        → bs ∣ Γ ∣ Bss ⊢as args ⦂ As → σ ⦂ Γ ⇒ Δ
        → bs ∣ Δ ∣ Bss ⊢as map-args σ {bs} args ⦂ As
  preserve-map {` x}{σ} (var-p ∋x) σ⦂ = ⊢v→⊢ (σ⦂ ∋x)
  preserve-map {op ⦅ args ⦆} (op-p ⊢args Pop) σ⦂ =
      op-p (pres-args ⊢args σ⦂) Pop
  pres-arg {zero} {arg = ast M} (ast-a ⊢M) σ⦂ = ast-a (preserve-map ⊢M σ⦂)
  pres-arg {suc b} {arg = bind arg} (bind-a {B = B}{A = A} ⊢arg) σ⦂ =
      bind-a (pres-arg ⊢arg (ext-env σ⦂))
  pres-args {[]} {args = nil} nil-a σ⦂ = nil-a
  pres-args {b ∷ bs} {args = cons arg args} (cons-a ⊢arg ⊢args) σ⦂ =
    cons-a (pres-arg ⊢arg σ⦂) (pres-args ⊢args σ⦂)

