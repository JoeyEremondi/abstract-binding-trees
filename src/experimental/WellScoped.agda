
{- NEEDS TO BE UPDATED -}

open import Syntax
open import Generic

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)

module WellScoped (Op : Set) (sig : Op → List ℕ) where

  open OpSig Op sig hiding (rename)

  𝒫 : Op → List ⊤ → ⊤ → Set
  𝒫 op Γ A = ⊤

  mk-list : ℕ → List ⊤
  mk-list 0 = []
  mk-list (suc n) = tt ∷ mk-list n

  open ABTPred Op sig 𝒫
  
  WS : ℕ → ABT → Set
  WS n M = (mk-list n) ⊢ M ⦂ tt

  module RenamingPreserves where

    open Rename Op sig
    open RenamePres Op sig 𝒫

    WS-Rename : ℕ → Rename → ℕ → Set
    WS-Rename Γ ρ Δ = ρ ⦂ (mk-list Γ) ⇒ (mk-list Δ)

    WS-rename : ∀ {Γ Δ ρ M} → WS-Rename Γ ρ Δ → WS Γ M → WS Δ (rename ρ M)
    WS-rename {Γ}{Δ}{ρ}{M} ΓρΔ WSM =
        preserve {M}{ρ}{mk-list Γ}{mk-list Δ} WSM ΓρΔ

  module SubstPreserves where
  
    open Subst Op sig
    open SubstPres Op sig 𝒫

    WS-Subst : ℕ → Subst → ℕ → Set
    WS-Subst Γ σ Δ = σ ⦂ (mk-list Γ) ⇒ (mk-list Δ)
  
    WS-subst : ∀ {Γ Δ σ M} → WS-Subst Γ σ Δ → WS Γ M → WS Δ (subst σ M)
    WS-subst {Γ}{Δ}{σ}{M} ΓσΔ WSM =
        preserve {M}{σ}{mk-list Γ}{mk-list Δ} WSM ΓσΔ
