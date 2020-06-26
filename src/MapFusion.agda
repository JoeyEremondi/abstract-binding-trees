open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Environment
open import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Var

module MapFusion (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import Map Op sig
open import Renaming
open WithOpSig Op sig

open Shiftable {{...}}
open Quotable {{...}}
open Env  {{...}}

{- todo: simplify this -}
record FusableMap (V₁ E₁ V₂ E₂ V₃ E₃ : Set)
  {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}}{{S₃ : Shiftable V₃}}
  {{Q₁ : Quotable V₁}}{{Q₂ : Quotable V₂}}{{Q₃ : Quotable V₃}}
  : Set₁ where
  field quote-var→val₁ : ∀ x → “ (var→val{V₁} x) ” ≡ ` x
        quote-var→val₂ : ∀ x → “ (var→val{V₂} x) ” ≡ ` x
        quote-var→val₃ : ∀ x → “ (var→val{V₃} x) ” ≡ ` x
        quote-shift₁ : ∀ (v : V₁) → “ ⇑ v ” ≡ rename (↑ 1) “ v ”
        quote-shift₂ : ∀ (v : V₂) → “ ⇑ v ” ≡ rename (↑ 1) “ v ”
        quote-shift₃ : ∀ (v : V₃) → “ ⇑ v ” ≡ rename (↑ 1) “ v ”

open FusableMap {{...}}

map-rename-fusion : ∀{V₂ E₂ V₃ E₃}
  {{S₂ : Shiftable V₂}}{{S₃ : Shiftable V₃}} {{_ : Env E₂ V₂}} {{_ : Env E₃ V₃}}
  {{_ : Quotable V₂}} {{_ : Quotable V₃}}
  {{_ : FusableMap Var Rename V₂ E₂ V₃ E₃}}
  {σ₁ : Rename}{σ₂ : E₂}{σ₃ : E₃}
   → (M : ABT)
   → σ₂ ∘ σ₁ ≈ σ₃
   → map σ₂ (rename σ₁ M) ≡ map σ₃ M
map-rename-fusion {V₂}{E₂}{V₃}{E₃}{σ₁ = σ₁}{σ₂}{σ₃} M σ₂∘σ₁≈σ₃ =
  map-map-fusion-ext{Var}{Rename}{V₂}{E₂}{V₃}{E₃}{σ₁ = σ₁}{σ₂}{σ₃}
            M σ₂∘σ₁≈σ₃ map-ext
  where
  map-ext : ∀{σ₁ : Rename}{σ₂ : E₂}{σ₃ : E₃}
          → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃
  map-ext {σ₁} {σ₂} {σ₃} σ₂∘σ₁≈σ₃ zero rewrite lookup-0 σ₂ (var→val 0)
      | lookup-0 σ₃ (var→val 0) =
      trans (quote-var→val₂ 0) (sym (quote-var→val₃ 0))
  map-ext {σ₁} {σ₂} {σ₃} σ₂∘σ₁≈σ₃ (suc x) rewrite lookup-shift σ₁ x
      | lookup-suc σ₂ (var→val 0) (⟅ σ₁ ⟆ x)
      | lookup-suc σ₃ (var→val 0) x =
          trans (quote-shift₂ (⟅ σ₂ ⟆ (⟅ σ₁ ⟆ x)))
                (sym (trans (quote-shift₃ _)
                            (cong (rename (↑ 1)) (sym (σ₂∘σ₁≈σ₃ x)))))

rename-map-fusion : ∀{V₁ E₁ V₃ E₃}
  {{S₁ : Shiftable V₁}}{{S₃ : Shiftable V₃}} {{_ : Env E₁ V₁}} {{_ : Env E₃ V₃}}
  {{_ : Quotable V₁}} {{_ : Quotable V₃}}
  {{_ : FusableMap V₁ E₁ Var Rename V₃ E₃}}
  {σ₁ : E₁}{ρ₂ : Rename}{σ₃ : E₃}
   → (M : ABT)
   → ρ₂ ∘ σ₁ ≈ σ₃
   → rename ρ₂ (map σ₁ M) ≡ map σ₃ M
rename-map-fusion {V₁}{E₁}{V₃}{E₃}{σ₁ = σ₁}{ρ₂}{σ₃} M ρ₂∘σ₁≈σ₃ =
  map-map-fusion-ext{V₁}{E₁}{Var}{Rename}{V₃}{E₃}{σ₁ = σ₁}{ρ₂}{σ₃}
            M ρ₂∘σ₁≈σ₃ map-ext
  where
  map-ext : ∀{σ₁ : E₁}{ρ₂ : Rename}{σ₃ : E₃}
          → ρ₂ ∘ σ₁ ≈ σ₃ → ext ρ₂ ∘ ext σ₁ ≈ ext σ₃
  map-ext {σ₁} {ρ₂} {σ₃} ρ₂∘σ₁≈σ₃ zero rewrite lookup-0 σ₁ (var→val 0)
      | lookup-0 σ₃ (var→val 0) | quote-var→val₁ 0 | quote-var→val₃ 0 = refl
  map-ext {σ₁} {ρ₂} {σ₃} ρ₂∘σ₁≈σ₃ (suc x) rewrite lookup-suc σ₁ (var→val 0) x
      | lookup-suc σ₃ (var→val 0) x | quote-shift₁ (⟅ σ₁ ⟆ x)
      | quote-shift₃ (⟅ σ₃ ⟆ x) = begin
      rename (0 • inc ρ₂) (map (↑ 1) “ ⟅ σ₁ ⟆ x ”)
          ≡⟨ compose-rename (↑ 1) (0 • inc ρ₂) “ ⟅ σ₁ ⟆ x ” ⟩
      rename (↑ 1 ⨟ (0 • inc ρ₂)) “ ⟅ σ₁ ⟆ x ”
         ≡⟨ cong (λ □ → rename □ “ ⟅ σ₁ ⟆ x ”) (ren-tail (inc ρ₂) 0) ⟩
      rename (inc ρ₂) “ ⟅ σ₁ ⟆ x ”
         ≡⟨ cong (λ □ → rename □ “ ⟅ σ₁ ⟆ x ”) (inc=⨟ᵣ↑ ρ₂) ⟩
      rename (ρ₂ ⨟ ↑ 1) “ ⟅ σ₁ ⟆ x ”
         ≡⟨ sym (compose-rename ρ₂ (↑ 1) “ ⟅ σ₁ ⟆ x ”) ⟩
      rename (↑ 1) (rename ρ₂ “ ⟅ σ₁ ⟆ x ”)
         ≡⟨ cong (rename (↑ 1)) (ρ₂∘σ₁≈σ₃ x) ⟩
      map (↑ 1) “ ⟅ σ₃ ⟆ x ”
      ∎

map-map-fusion : ∀{V₁ E₁ V₂ E₂ V₃ E₃}
  {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}}{{S₃ : Shiftable V₃}}
  {{_ : Env E₁ V₁}} {{_ : Env E₂ V₂}} {{_ : Env E₃ V₃}}
  {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
  {{_ : FusableMap V₁ E₁ V₂ E₂ V₃ E₃}}
  {{_ : FusableMap V₂ E₂ Var Rename V₂ E₂}}
  {{_ : FusableMap Var Rename V₂ E₂ V₂ E₂}}
  {σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}
   → (M : ABT)
   → σ₂ ∘ σ₁ ≈ σ₃
   → (∀{σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}
      → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃)
   → map σ₂ (map σ₁ M) ≡ map σ₃ M
map-map-fusion (` x) σ₂∘σ₁≈σ₃ mf-ext = σ₂∘σ₁≈σ₃ x
map-map-fusion {V₁}{E₁}{V₂}{E₂}{V₃}{E₃}{{S₁}}{{S₂}}{{S₃}}
  (op ⦅ args ⦆) σ₂∘σ₁≈σ₃ mf-ext =
  cong (_⦅_⦆ op) (mmf-args args σ₂∘σ₁≈σ₃)
  where
  G : ∀{σ₂ : E₂} → _∘_≈_{Var}{Rename} (σ₂ , (var→val 0)) (↑ 1) (⟰ σ₂)
  G {σ₂} x rewrite lookup-suc σ₂ (var→val 0) x | lookup-shift σ₂ x = refl
  H : ∀{σ₂ : E₂} → ↑ 1 ∘ σ₂ ≈ ⟰ σ₂
  H {σ₂} x rewrite lookup-shift σ₂ x | quote-shift₂{V₁}{E₁} (⟅ σ₂ ⟆ x) = refl

  mm-fuse-ext : ∀{σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}
      → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃
  mm-fuse-ext {σ₁}{σ₂}{σ₃} σ₂∘σ₁≈σ₃ zero rewrite lookup-0 σ₁ (var→val 0)
      | lookup-0 σ₃ (var→val 0) =
      begin
          map (σ₂ , (var→val 0)) “ (var→val{V₁} 0) ”
                       ≡⟨ cong (map (σ₂ , (var→val{V₂} 0))) (quote-var→val₁ 0) ⟩
          map (σ₂ , (var→val 0)) (` 0)       ≡⟨⟩
          “ ⟅ σ₂ , (var→val 0) ⟆ 0 ”
                               ≡⟨ cong (λ □ → “ □ ”) (lookup-0 σ₂ (var→val 0)) ⟩
          “ (var→val{V₂} 0) ”        ≡⟨ (quote-var→val₂{V₁} 0) ⟩
          ` 0                        ≡⟨ sym (quote-var→val₃{V₁} 0) ⟩
          “ (var→val{V₃} 0) ”        ∎
  mm-fuse-ext {σ₁}{σ₂}{σ₃} σ₂∘σ₁≈σ₃ (suc x) rewrite lookup-suc σ₁ (var→val 0) x
      | lookup-suc σ₃ (var→val 0) x = begin
      map (σ₂ , (var→val 0)) “ ⇑ (⟅ σ₁ ⟆ x) ”
                    ≡⟨ cong (map (σ₂ , (var→val 0))) (quote-shift₁ (⟅ σ₁ ⟆ x)) ⟩
      map (σ₂ , (var→val 0)) (rename (↑ 1) “ ⟅ σ₁ ⟆ x ”)
                     ≡⟨ map-rename-fusion “ ⟅ σ₁ ⟆ x ” G ⟩
      map (⟰ σ₂) “ ⟅ σ₁ ⟆ x ”
                              ≡⟨ sym (rename-map-fusion “ ⟅ σ₁ ⟆ x ” H) ⟩
      rename (↑ 1) (map σ₂ “ ⟅ σ₁ ⟆ x ”) ≡⟨ cong (rename (↑ 1)) (σ₂∘σ₁≈σ₃ x) ⟩
      rename (↑ 1) “ ⟅ σ₃ ⟆ x ” ≡⟨ sym (quote-shift₃ (⟅ σ₃ ⟆ x)) ⟩
      “ ⇑ (⟅ σ₃ ⟆ x) ” ∎


  mmf-arg : ∀{σ₁ σ₂ σ₃ b} (arg : Arg b) → σ₂ ∘ σ₁ ≈ σ₃
     → map-arg σ₂ (map-arg σ₁ arg) ≡ map-arg σ₃ arg
  mmf-args : ∀{σ₁ σ₂ σ₃ bs} (args : Args bs) → σ₂ ∘ σ₁ ≈ σ₃
     → map-args σ₂ (map-args σ₁ args) ≡ map-args σ₃ args
  mmf-arg {b = zero} (ast M) σ₂∘σ₁≈σ₃ =
      cong ast (map-map-fusion M σ₂∘σ₁≈σ₃ mf-ext)
  mmf-arg {b = suc b} (bind arg) σ₂∘σ₁≈σ₃ =
      cong bind (mmf-arg arg (mf-ext σ₂∘σ₁≈σ₃))
  mmf-args {bs = []} nil σ₂∘σ₁≈σ₃ = refl
  mmf-args {bs = b ∷ bs} (cons arg args) σ₂∘σ₁≈σ₃ =
      cong₂ cons (mmf-arg arg σ₂∘σ₁≈σ₃) (mmf-args args σ₂∘σ₁≈σ₃)
