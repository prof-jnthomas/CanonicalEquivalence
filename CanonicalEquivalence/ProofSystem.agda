module CanonicalEquivalence.ProofSystem where
open import CanonicalEquivalence.Prelude
open import CanonicalEquivalence.Syntax
open import CanonicalEquivalence.Helpers

-- Fixities
infix 5 _⊦_
infix 7 _↑_

data _⊦_ (Γ : Theory) : Formula → Set where
  assumption : ∀ {φ}         → Γ φ → Γ ⊦ φ
  -- Implication
  ⟶ⁱ         : ∀ {φ ψ}       → (φ :: Γ) ⊦ ψ → Γ ⊦ (φ ⟶ ψ)
  ⟶ᵉ         : ∀ {φ ψ}       → Γ ⊦ (φ ⟶ ψ) → Γ ⊦ φ → Γ ⊦ ψ
  -- Disjunction
  ∨i¹        : ∀ {φ ψ}       → Γ ⊦ φ → Γ ⊦ (φ ∨ ψ)
  ∨i²        : ∀ {φ ψ}       → Γ ⊦ ψ → Γ ⊦ (φ ∨ ψ)
  ∨ᵉ         : ∀ (φ ψ χ : Formula) → Γ ⊦ (φ ∨ ψ) → (φ :: Γ) ⊦ χ → (ψ :: Γ) ⊦ χ
                             → Γ ⊦ χ
  -- Conjunction
  ∧ⁱ         : ∀ {φ ψ}       → Γ ⊦ φ → Γ ⊦ ψ → Γ ⊦ (φ ∧ ψ)
  ∧e¹        : ∀ {φ ψ}       → Γ ⊦ (φ ∧ ψ) → Γ ⊦ φ
  ∧e²        : ∀ {φ ψ}       → Γ ⊦ (φ ∧ ψ) → Γ ⊦ ψ
  -- Bottom
  𝟘ᵉ         : ∀ {φ}         → Γ ⊦ 𝟘 → Γ ⊦ φ

-- Lifting derivations along subset inclusions
_↑_ : ∀ {Γ Δ φ} → Γ ⊆ Δ → Γ ⊦ φ → Δ ⊦ φ

_↑_ {Γ} {Δ} {φ} Γ⊆Δ (assumption pf) = assumption (Γ⊆Δ pf)

_↑_ {Γ} {Δ} {φ₁ ⟶ φ₂} Γ⊆Δ (⟶ⁱ x₁) = ⟶ⁱ ((extend-⊆ {Γ = Γ} {Δ = Δ} Γ⊆Δ) ↑ x₁)

_↑_ {Γ} {Δ} {φ₂} Γ⊆Δ (⟶ᵉ x₁ x₂) = ⟶ᵉ (Γ⊆Δ ↑ x₁) (Γ⊆Δ ↑ x₂)

_↑_ {Γ} {Δ} {φ} Γ⊆Δ (∨i¹ x₁) = ∨i¹ (Γ⊆Δ ↑ x₁)

_↑_ {Γ} {Δ} {φ} Γ⊆Δ (∨i² x₁) = ∨i² (Γ⊆Δ ↑ x₁)

_↑_ {Γ} {Δ} {φ} Γ⊆Δ (∨ᵉ φ₁ ψ χ x₁ x₂ x₃) = ∨ᵉ φ₁ ψ χ (Γ⊆Δ ↑ x₁) ((extend-⊆ {Γ = Γ} {Δ = Δ} Γ⊆Δ) ↑ x₂) ((extend-⊆ {Γ = Γ} {Δ = Δ} Γ⊆Δ) ↑ x₃)

_↑_ {Γ} {Δ} {φ} Γ⊆Δ (∧ⁱ x₁ x₂) = ∧ⁱ (Γ⊆Δ ↑ x₁) (Γ⊆Δ ↑ x₂)

_↑_ {Γ} {Δ} {φ} Γ⊆Δ (∧e¹ x₁) = ∧e¹ (Γ⊆Δ ↑ x₁)

_↑_ {Γ} {Δ} {φ} Γ⊆Δ (∧e² x₁) = ∧e² (Γ⊆Δ ↑ x₁)

_↑_ {Γ} {Δ} {φ} Γ⊆Δ (𝟘ᵉ x₁) = 𝟘ᵉ (Γ⊆Δ ↑ x₁)
