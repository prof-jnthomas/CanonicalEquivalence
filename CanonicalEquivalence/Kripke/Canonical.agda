module CanonicalEquivalence.Kripke.Canonical where

open import CanonicalEquivalence.Syntax
open import CanonicalEquivalence.ProofSystem
open import CanonicalEquivalence.Prelude

record IsCanonical (Γ : Theory) : Set where
  field
    closed     : ∀ {φ} → Γ ⊢ φ → Γ φ
    consistent : ¬ (Γ ⊢ 𝟘)
    prime      : ∀ {φ ψ} → Γ (φ ∨ ψ) → Γ φ ⊎ Γ ψ

record CanonicalWorld : Set₁ where
  field
    theory    : Theory
    canonical : IsCanonical theory

record KripkeModel : Set₁ where
  field
    𝑾     : Set
    _≤_   : 𝑾 → 𝑾 → Set
    _⊩_   : 𝑾 → Formula → Set

open CanonicalWorld
open IsCanonical

_⊩_ : CanonicalWorld → Formula → Set
Γ ⊩ φ = Γ .theory φ

⊢⇒⊩ : ∀ {Γ φ} → Γ .theory ⊢ φ → Γ ⊩ φ
⊢⇒⊩ {Γ} pf = Γ .canonical .closed pf

⊩⇒⊢ : ∀ {T φ} → T φ → T ⊢ φ
⊩⇒⊢ = assumption

completeness-for-canonical : ∀ {Γ φ} → Γ ⊩ φ → Γ .theory ⊢ φ
completeness-for-canonical pf = ⊩⇒⊢ pf

forcing-⊥ : ∀ {Γ} → Γ ⊩ 𝟘 → ⊥
forcing-⊥ {Γ} Γ⊩𝟘 =
  let Γᶜ = Γ .canonical
  in  Γᶜ .consistent (assumption Γ⊩𝟘)

forcing-∧ : ∀ {Γ φ ψ} → Γ ⊩ φ ∧ ψ → Γ ⊩ φ × Γ ⊩ ψ
forcing-∧ {Γ} {φ} {ψ} Γ∧ =
  let T = Γ .theory
      ⊢φ = ∧e¹ (⊩⇒⊢ {T} Γ∧)
      ⊢ψ = ∧e² (⊩⇒⊢ {T} Γ∧)
  in ⟪ Γ .canonical .closed ⊢φ , Γ .canonical .closed ⊢ψ ⟫

forcing-∨ : ∀ {Γ φ ψ} → Γ ⊩ φ ∨ ψ → Γ ⊩ φ ⊎ Γ ⊩ ψ
forcing-∨ {Γ} {φ} {ψ} Γ∨ = Γ .canonical .prime Γ∨

forcing-→ : ∀ {Γ φ ψ Δ} → Γ ⊩ φ ⟶ ψ → Γ .theory ⊆ Δ .theory → Δ ⊩ φ → Δ ⊩ ψ
forcing-→ {Γ} {φ} {ψ} {Δ} Γ→ Γ⊆Δ Δ⊩φ = Δ .canonical .closed (⟶ᵉ (Γ⊆Δ ↑ (⊩⇒⊢ {Γ .theory} Γ→)) (⊩⇒⊢ {Δ .theory} Δ⊩φ))
