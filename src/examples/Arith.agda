open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning

module examples.Arith where

  data Op : Set where
    op-num : ℕ → Op
    op-mult : Op
    op-let : Op
    op-bool : 𝔹 → Op
    op-if : Op

  sig : Op → List ℕ
  sig (op-num n) = []
  sig op-mult = 0 ∷ 0 ∷ []
  sig op-let = 0 ∷ 1 ∷ []
  sig (op-bool b) = []
  sig op-if = 0 ∷ 0 ∷ 0 ∷ []

  open import Fold Op sig
  open import ScopedTuple
  open import Syntax using (Substable; ↑)

  open import AbstractBindingTree Op sig
    renaming (ABT to AST)
  pattern $ n  = op-num n ⦅ nil ⦆
  infixl 7  _⊗_
  pattern _⊗_ L M = op-mult ⦅ cons (ast L) (cons (ast M) nil) ⦆
  pattern bind_｛_｝ L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆
  pattern cond_then_else_ L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆

  open import Data.Maybe using (Maybe; nothing; just)

  data Val : Set where
    v-num : ℕ → Val
    v-bool : 𝔹 → Val

  _>>=_ : Maybe Val → (Val → Maybe Val) → Maybe Val
  x >>= f
      with x
  ... | nothing = nothing
  ... | just n = f n

  num? : Val → (ℕ → Maybe Val) → Maybe Val
  num? mv f
      with mv
  ... | v-num n = f n
  ... | _ = nothing

  bool? : Val → (𝔹 → Maybe Val) → Maybe Val
  bool? mv f
      with mv
  ... | v-bool b = f b
  ... | _ = nothing

  eval-op : (op : Op) → Tuple (sig op) (Bind (Maybe Val) (Maybe Val))
          → Maybe Val
  eval-op (op-num n) tt = just (v-num n)
  eval-op op-mult ⟨ x , ⟨ y , tt ⟩ ⟩ = do
     v₁ ← x ; v₂ ← y 
     num? v₁ (λ n → num? v₂ (λ m → just (v-num (n * m))))
  eval-op op-let ⟨ x , ⟨ f , tt ⟩ ⟩ = do n ← x; f (just n)
  eval-op (op-bool b) tt = just (v-bool b)
  eval-op op-if ⟨ cnd , ⟨ thn , ⟨ els , tt ⟩ ⟩ ⟩ = do
     vᶜ ← cnd
     bool? vᶜ (λ b → if b then thn else els)

  Sub : Substable (Maybe Val)
  Sub = record { var→val = λ x → nothing ; shift = λ r → r
             ; var→val-suc-shift = refl }
  open Substable Sub

  Eval : Fold (Maybe Val) (Maybe Val) 
  Eval = record { S = Sub ; ret = λ x → x ; fold-op = eval-op }
  open Fold Eval

  eval : AST → Maybe Val
  eval = fold (↑ 0)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

  _ : eval ($ 2 ⊗ $ 21) ≡ just (v-num 42)
  _ = refl
  
  _ : eval (` 0) ≡ nothing
  _ = refl
  
  _ : eval (bind $ 21 ｛ $ 2 ⊗ ` 0 ｝) ≡ just (v-num 42)
  _ = refl

  _ : eval (bind ` 0 ｛ $ 2 ⊗ $ 21 ｝) ≡ nothing
  _ = refl


  {--- Type Safety ---}

  open import experimental.Preserve Op sig

  data Type : Set where
    t-nat : Type
    t-bool : Type

  𝑃 : (op : Op) → Vec Type (length (sig op))
     → BTypes Type (sig op) → Type → Set
  𝑃 (op-num x) []̌ Bss Tᵣ = Tᵣ ≡ t-nat
  𝑃 op-mult (T₁ ∷̌ T₂ ∷̌ []̌) Bss Tᵣ = T₁ ≡ t-nat × T₂ ≡ t-nat × Tᵣ ≡ t-nat
  𝑃 op-let (T₁ ∷̌ T₂ ∷̌ []̌) ⟨ tt , ⟨ ⟨ T₃ , tt ⟩ , tt ⟩ ⟩ Tᵣ =
      T₂ ≡ Tᵣ × T₁ ≡ T₃
  𝑃 (op-bool x) []̌ Bss Tᵣ = Tᵣ ≡ t-bool
  𝑃 op-if (Tᶜ ∷̌ Tᵗ ∷̌ Tₑ ∷̌ []̌) Bss Tᵣ = Tᶜ ≡ t-bool × Tᵗ ≡ Tₑ × Tₑ ≡ Tᵣ

  𝐴 : List Type → Maybe Val → Type → Set
  𝐴 Γ mv T = ⊤

  data ⊢_⦂_ : Val → Type → Set where
    ⊢-nat :  ∀{n} → ⊢ (v-num n) ⦂ t-nat
    ⊢-bool :  ∀{b} → ⊢ (v-bool b) ⦂ t-bool
    
  data _⊢v_⦂_ : List Type → Maybe Val → Type → Set where
    ⊢v-none : ∀{Γ A} → Γ ⊢v nothing ⦂ A
    ⊢v-just :  ∀{Γ v A} → ⊢ v ⦂ A → Γ ⊢v just v ⦂ A
  
  _⊢c_⦂_ : List Type → Maybe Val → Type → Set
  Γ ⊢c mv ⦂ A = Γ ⊢v mv ⦂ A

  {--- Type Safety via preserve-fold ---}
  
  open PreserveFold Eval 𝑃 𝐴 _⊢v_⦂_ _⊢c_⦂_
  open GenericSubstitution
  open GenericSubst Sub
  open import Var

  ext-⊢v : ∀{v A B Δ} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
  ext-⊢v {nothing} ⊢vσx = ⊢v-none
  ext-⊢v {just x₁} (⊢v-just ⊢v⦂) = ⊢v-just ⊢v⦂

  compress-⊢v : ∀{v A B Δ} → (B ∷ Δ) ⊢v v ⦂ A → Δ ⊢v v ⦂ A
  compress-⊢v {.nothing} ⊢v-none = ⊢v-none
  compress-⊢v {.(just _)} (⊢v-just x) = ⊢v-just x

  ret-pres : ∀{v}{Δ}{A} → Δ ⊢v v ⦂ A → Δ ⊢c (ret v) ⦂ A
  ret-pres ⊢v⦂ = ⊢v⦂
  
  op-pres : ∀ {op}{Rs}{Δ}{A : Type}{As : Vec Type (length (sig op))}{Bs}
            → sig op ∣ Δ ∣ Bs ⊢rs Rs ⦂ As
            → 𝑃 op As Bs A → Δ ⊢c (fold-op op Rs) ⦂ A
  op-pres {op-num n} nil-r refl = ⊢v-just ⊢-nat
  op-pres {op-mult} (cons-r (ast-r Px) (cons-r (ast-r Py) nil-r))
          ⟨ refl , ⟨ refl , refl ⟩ ⟩
      with Px | Py
  ... | ⊢v-none | _ = ⊢v-none
  ... | ⊢v-just ⊢v⦂ | ⊢v-none = ⊢v-none
  ... | ⊢v-just ⊢-nat | ⊢v-just ⊢-nat = ⊢v-just ⊢-nat
  op-pres {op-let} {A = Tᵣ}{As = T₁ ∷̌ T₂ ∷̌ []̆}
          (cons-r (ast-r{c = c} Prhs)
                  (cons-r (bind-r{b}{Δ = Δ}{f = f} Pbody) nil-r))
          ⟨ refl , refl ⟩
      with c
  ... | nothing = ⊢v-none
  ... | just v =
         let wtres : (T₁ ∷ Δ) ⊢c f (just v) ⦂ T₂
             wtres = ⊢r→⊢c (Pbody {just v} (ext-⊢v Prhs) tt) in
         compress-⊢v wtres
  op-pres {op-bool b} nil-r refl = ⊢v-just ⊢-bool
  op-pres {op-if} (cons-r (ast-r Pc) (cons-r (ast-r Pthn)
                                     (cons-r (ast-r Pels) nil-r)))
                  ⟨ refl , ⟨ refl , refl ⟩ ⟩
      with Pc
  ... | ⊢v-none = ⊢v-none
  ... | ⊢v-just (⊢-bool{b})
      with b
  ... | true = Pthn
  ... | false = Pels

  open ExtV (λ{σ}{A}{B}{Δ}{v} ⊢v⦂ → ext-⊢v{v}{A}{B}{Δ} ⊢v⦂)
  open Reqs ret-pres op-pres
  
  type-safety : ∀ M → [] ⊢ M ⦂ t-nat → [] ⊢c eval M ⦂ t-nat
  type-safety M ⊢M = preserve-fold ⊢M empty-env
