module CanonicalEquivalence.Helpers where
open import CanonicalEquivalence.Prelude
open import CanonicalEquivalence.Syntax

infix 8 _∁_

_∁_ : Theory → Formula → Theory
Δ ∁ φ = Δ ∩ (λ ψ → ψ ≡ φ) ᶜ

subset-restoration
  : ∀ {Δ φ} → let Δ′ = Δ ∩ (λ ψ → ψ ≡ φ) ᶜ in Δ ⊆ (φ :: Δ′)
subset-restoration {Δ} {φ} {ψ} ψ∈Δ with ψ ≃ φ
... | yes refl = inj₂ refl
... | no  neq  = inj₁ ⟪ ψ∈Δ , neq ⟫

subset-of-complement : ∀ {Γ φ} → (Γ ∁ φ) ⊆ Γ
subset-of-complement {Γ} {φ} {ψ} = proj₁

extend-⊆ : ∀ {Γ Δ φ} → Γ ⊆ Δ → (φ :: Γ) ⊆ (φ :: Δ)
extend-⊆   Γ⊆Δ (inj₁ p) = inj₁ (Γ⊆Δ p)
extend-⊆   Γ⊆Δ (inj₂ p) = inj₂ p

union-of-subsets
  : ∀ (X Y Z G : Theory)
  → X ⊆ G → Y ⊆ G → Z ⊆ G → (X ∪ (Y ∪ Z)) ⊆ G
union-of-subsets X Y Z G X⊆ Y⊆ Z⊆ {φ} =
  λ where
    (inj₁ φ∈X)        → X⊆ φ∈X
    (inj₂ (inj₁ φ∈Y)) → Y⊆ φ∈Y
    (inj₂ (inj₂ φ∈Z)) → Z⊆ φ∈Z
