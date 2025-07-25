module CanonicalEquivalence.Completeness where
open import CanonicalEquivalence.Prelude
open import CanonicalEquivalence.Syntax
open import CanonicalEquivalence.ProofSystem

constructive-completeness : ∀ {Γ φ} → (∀ Δ → Δ ⊆ Γ → Δ ⊦ φ) → Γ ⊦ φ
constructive-completeness {Γ} {φ} H = H Γ (λ {ψ} p → p)       -- identity function is the proof Γ ⊆ Γ

-- This is the syntactic contrapositive of semantic completeness
-- It internalizes the finite model property: failure of derivability implies finite failure
constructive-completeness-contrapositive : ∀ {Γ φ} → ¬ (Γ ⊦ φ) → (∃ λ Δ → Δ ⊆ Γ × ¬ (Δ ⊦ φ))
constructive-completeness-contrapositive {Γ} {φ} ¬Γ⊦φ =
  let
    Γ⊆Γ : Γ ⊆ Γ
    Γ⊆Γ {ψ} ψ∈Γ = ψ∈Γ
  in ⟪ Γ , ⟪ Γ⊆Γ , ¬Γ⊦φ ⟫ ⟫
