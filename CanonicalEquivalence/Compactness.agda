module CanonicalEquivalence.Compactness where
open import CanonicalEquivalence.Prelude
open import CanonicalEquivalence.Syntax
open import CanonicalEquivalence.Helpers
open import CanonicalEquivalence.ProofSystem

--------------------------------------------------------------------------------
-- Compactness Lemmata
--------------------------------------------------------------------------------

-- If a (possibly infinite) set of propositional formulas intuitionistically entails a contradiction (i.e., ⊢ from Γ ⊢ ⊥),
-- then there exists a finite subset Γ₀ ⊆ Γ such that Γ₀ ⊢ ⊥.

-- In other words: Entailment of ⊥ from an infinite set implies entailment of ⊥ from a finite subset.
-- Γ ⊢ 𝟘 → ∃Δ((Δ ⊆ Γ) ∧ (Δ ⊢ 𝟘))

-- More generally, for finitary derivability
-- Γ ⊢ φ → ∃Δ((Δ ⊆ Γ) ∧ (Δ ⊢ φ))

finitary-derivability : ∀ {Γ φ} → Γ ⊦ φ → (∃ λ Δ → Δ ⊆ Γ × Δ ⊦ φ)

-- Base case
finitary-derivability {Γ} {φ} (assumption p) = ⟪ Δ , ⟪ Δ⊆Γ , assumption φ∈Δ ⟫ ⟫
  where
    Δ : Theory
    Δ = ⌊ φ ∷ [] ⌋

    φ∈Δ : φ ∈ Δ
    φ∈Δ = inj₂ refl

    Δ⊆Γ : Δ ⊆ Γ
    Δ⊆Γ (inj₂ refl) = p

    baseCase : (Δ ⊆ Γ × Δ ⊦ φ)
    baseCase = ⟪ Δ⊆Γ , assumption φ∈Δ ⟫

finitary-derivability {Γ} {φ₁ ⟶ φ₂} (⟶ⁱ x) =
  let
    ⟪ Δ , ⟪ Δ⊆Γ₁ , pf₁ ⟫ ⟫ = finitary-derivability x
    Δ′ = Δ ∩ (λ ψ → ψ ≡ φ₁) ᶜ

    Δ′⊆Γ : Δ′ ⊆ Γ
    Δ′⊆Γ {ψ} ψ∈Δ′ = [ (λ ψ∈Γ → ψ∈Γ) , (λ eq  → ⊥-elim ((proj₂ ψ∈Δ′) eq)) ]′ (Δ⊆Γ₁ (proj₁ ψ∈Δ′))

    subIncl : Δ ⊆ (φ₁ :: Δ′)
    subIncl = subset-restoration {Δ = Δ} {φ = φ₁}

    pf = ⟶ⁱ (subIncl ↑ pf₁)

  in ⟪ Δ′ , ⟪ Δ′⊆Γ , pf ⟫ ⟫

finitary-derivability {Γ} {φ₂} (⟶ᵉ x₁ x₂) =
  let
    ⟪ Δ₁ , ⟪ Δ⊆Γ₁ , pf₁ ⟫ ⟫ = finitary-derivability x₁
    ⟪ Δ₂ , ⟪ Δ⊆Γ₂ , pf₂ ⟫ ⟫ = finitary-derivability x₂
    Δ = Δ₁ ∪ Δ₂

    Δ₁⊆Δ : Δ₁ ⊆ Δ
    Δ₁⊆Δ {φ} φ∈Δ₁ = inj₁ φ∈Δ₁

    Δ₂⊆Δ : Δ₂ ⊆ Δ
    Δ₂⊆Δ {φ} φ∈Δ₂ = inj₂ φ∈Δ₂

    Δ⊆Γ : Δ ⊆ Γ
    Δ⊆Γ {φ} φ∈Δ = [ (λ φ∈Δ₁ → Δ⊆Γ₁ φ∈Δ₁) , (λ φ∈Δ₂ → Δ⊆Γ₂ φ∈Δ₂) ]′ φ∈Δ

    pf = ⟶ᵉ (Δ₁⊆Δ ↑ pf₁) (Δ₂⊆Δ ↑ pf₂)
  in ⟪ Δ , ⟪ Δ⊆Γ , pf ⟫ ⟫

finitary-derivability {Γ} {φ₁ ∨ φ₂} (∨i¹ x) =
  let
    ⟪ Δ , ⟪ Δ⊆Γ , pf₁ ⟫ ⟫ = finitary-derivability x
    pf = ∨i¹ pf₁
  in ⟪ Δ , ⟪ Δ⊆Γ , pf ⟫ ⟫

finitary-derivability {Γ} {φ₁ ∨ φ₂} (∨i² x) =
  let
    ⟪ Δ , ⟪ Δ⊆Γ , pf₁ ⟫ ⟫ = finitary-derivability x
    pf = ∨i² pf₁
  in ⟪ Δ , ⟪ Δ⊆Γ , pf ⟫ ⟫

finitary-derivability {Γ} {χ} (∨ᵉ φ₁ φ₂ .χ x₁ x₂ x₃) =
  let
    ⟪ Δ₁ , ⟪ Δ⊆Γ₁ , pf₁ ⟫ ⟫ = finitary-derivability x₁
    ⟪ Δ₂ , ⟪ Δ⊆Γ₂ , pf₂ ⟫ ⟫ = finitary-derivability x₂
    ⟪ Δ₃ , ⟪ Δ⊆Γ₃ , pf₃ ⟫ ⟫ = finitary-derivability x₃

    Δ₂′ = Δ₂ ∩ (λ ψ → ψ ≡ φ₁) ᶜ
    Δ₃′ = Δ₃ ∩ (λ ψ → ψ ≡ φ₂) ᶜ

    Δ₂′⊆Γ : Δ₂′ ⊆ Γ
    Δ₂′⊆Γ {ψ} ψ∈Δ′ = [ (λ ψ∈Γ → ψ∈Γ) , (λ eq  → ⊥-elim ((proj₂ ψ∈Δ′) eq)) ]′ (Δ⊆Γ₂ (proj₁ ψ∈Δ′))

    Δ₃′⊆Γ : Δ₃′ ⊆ Γ
    Δ₃′⊆Γ {ψ} ψ∈Δ′ = [ (λ ψ∈Γ → ψ∈Γ) , (λ eq  → ⊥-elim ((proj₂ ψ∈Δ′) eq)) ]′ (Δ⊆Γ₃ (proj₁ ψ∈Δ′))

    Δ = Δ₁ ∪ (Δ₂′ ∪ Δ₃′)

    Δ₁⊆Δ : Δ₁ ⊆ Δ
    Δ₁⊆Δ {φ} φ∈Δ₁ = inj₁ φ∈Δ₁

    Δ₂′⊆Δ : Δ₂′ ⊆ Δ
    Δ₂′⊆Δ {φ} φ∈Δ₂ = inj₂ (inj₁ φ∈Δ₂)

    Δ₃′⊆Δ : Δ₃′ ⊆ Δ
    Δ₃′⊆Δ {φ} φ∈Δ₃ = inj₂ (inj₂ φ∈Δ₃)

    Δ⊆Γ : Δ ⊆ Γ
    Δ⊆Γ = union-of-subsets Δ₁ Δ₂′ Δ₃′ Γ Δ⊆Γ₁ Δ₂′⊆Γ Δ₃′⊆Γ

    Δ₂ᵣ : Δ₂ ⊆ (φ₁ :: Δ₂′)
    Δ₂ᵣ = subset-restoration {Δ = Δ₂} {φ = φ₁}

    subIncl₂ : Δ₂ ⊆ (φ₁ :: Δ)
    subIncl₂ {ψ} ψ∈Δ₂ = [ (λ ψ∈Δ₂′ → inj₁ (Δ₂′⊆Δ ψ∈Δ₂′)) , (λ refl → inj₂ refl) ]′ (Δ₂ᵣ ψ∈Δ₂)

    Δ₃ᵣ : Δ₃ ⊆ (φ₂ :: Δ₃′)
    Δ₃ᵣ = subset-restoration {Δ = Δ₃} {φ = φ₂}

    subIncl₃ : Δ₃ ⊆ (φ₂ :: Δ)
    subIncl₃ {φ} ψ∈Δ₃ = [ (λ ψ∈Δ₃′ → inj₁ (Δ₃′⊆Δ ψ∈Δ₃′)) , (λ refl → inj₂ refl) ]′ (Δ₃ᵣ ψ∈Δ₃)

    pf : Δ ⊦ χ
    pf = ∨ᵉ φ₁ φ₂ χ (Δ₁⊆Δ ↑ pf₁) (subIncl₂ ↑ pf₂) (subIncl₃ ↑ pf₃)

  in ⟪ Δ , ⟪ Δ⊆Γ , pf ⟫ ⟫

finitary-derivability {Γ} {φ₁ ∧ φ₂} (∧ⁱ x₁ x₂) =
  let
    ⟪ Δ₁ , ⟪ Δ⊆Γ₁ , pf₁ ⟫ ⟫ = finitary-derivability x₁
    ⟪ Δ₂ , ⟪ Δ⊆Γ₂ , pf₂ ⟫ ⟫ = finitary-derivability x₂

    Δ = Δ₁ ∪ Δ₂

    Δ₁⊆Δ : Δ₁ ⊆ Δ
    Δ₁⊆Δ {φ} φ∈Δ₁ = inj₁ φ∈Δ₁

    Δ₂⊆Δ : Δ₂ ⊆ Δ
    Δ₂⊆Δ {φ} φ∈Δ₂ = inj₂ φ∈Δ₂

    Δ⊆Γ : Δ ⊆ Γ
    Δ⊆Γ {φ} φ∈Δ = [ (λ φ∈Δ₁ → Δ⊆Γ₁ φ∈Δ₁) , (λ φ∈Δ₂ → Δ⊆Γ₂ φ∈Δ₂) ]′ φ∈Δ

    pf = ∧ⁱ (Δ₁⊆Δ ↑ pf₁) (Δ₂⊆Δ ↑ pf₂)
  in ⟪ Δ , ⟪ Δ⊆Γ , pf ⟫ ⟫

finitary-derivability {Γ} {φ₁} (∧e¹ x) =
  let
    ⟪ Δ , ⟪ Δ⊆Γ , pf₁ ⟫ ⟫ = finitary-derivability x
    pf = ∧e¹ pf₁
  in ⟪ Δ , ⟪ Δ⊆Γ , pf ⟫ ⟫

finitary-derivability {Γ} {φ₂} (∧e² x) =
  let
    ⟪ Δ , ⟪ Δ⊆Γ , pf₁ ⟫ ⟫ = finitary-derivability x
    pf = ∧e² pf₁
  in ⟪ Δ , ⟪ Δ⊆Γ , pf ⟫ ⟫

finitary-derivability {Γ} {φ} (𝟘ᵉ x) =
  let
    ⟪ Δ , ⟪ Δ⊆Γ , pf₁ ⟫ ⟫ = finitary-derivability x
    pf = 𝟘ᵉ pf₁
  in ⟪ Δ , ⟪ Δ⊆Γ , pf ⟫ ⟫

compactness-of-inconsistency : ∀ {Γ} → Γ ⊦ 𝟘 → (∃ λ Δ → Δ ⊆ Γ × Δ ⊦ 𝟘)
compactness-of-inconsistency = finitary-derivability

compact-consistency : ∀ {Γ} → (∀ Δ → Δ ⊆ Γ → ¬ (Δ ⊦ 𝟘)) → ¬ (Γ ⊦ 𝟘)

compact-consistency {Γ} 𝒞Γ Γ⊦𝟘 =
  let
    ⟪ Δ , ⟪ Δ⊆Γ , Δ⊦𝟘 ⟫ ⟫ = finitary-derivability Γ⊦𝟘
    ¬Δ⊦𝟘 = (𝒞Γ Δ) Δ⊆Γ
  in ¬Δ⊦𝟘 Δ⊦𝟘
