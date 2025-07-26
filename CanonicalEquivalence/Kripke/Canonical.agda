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

record KripkeModel : Set₂ where
  field
    𝑾     : Set₁
    _≤_   : 𝑾 → 𝑾 → Set
    _⊩_   : 𝑾 → Formula → Set

open CanonicalWorld
open IsCanonical

_⊩_ : CanonicalWorld → Formula → Set
Γ ⊩ φ = Γ .theory φ

_≤_ : CanonicalWorld → CanonicalWorld → Set
wₘ ≤ wₙ = wₘ .theory ⊆ wₙ .theory

CanonicalKripkeModel : KripkeModel
CanonicalKripkeModel = record
  { 𝑾  = CanonicalWorld
  ; _≤_ = _≤_
  ; _⊩_ = _⊩_
  }

--------------------------------------------------------------------------
--- Equivalence Lemmata --------------------------------------------------
--------------------------------------------------------------------------

-- Soundness
⊢⊆⊩ : ∀ {Γ φ} → Γ .theory ⊢ φ → Γ ⊩ φ
⊢⊆⊩ {Γ} pf = Γ .canonical .closed pf

-- Completeness
⊩⊆⊢ : ∀ {T φ} → T φ → T ⊢ φ
⊩⊆⊢ = assumption

truth-lemma-from : ∀ {Γ φ} → Γ ⊩ φ → Γ .theory ⊢ φ
truth-lemma-from = ⊩⊆⊢

truth-lemma-to : ∀ {Γ φ} → Γ .theory ⊢ φ → Γ ⊩ φ
truth-lemma-to {Γ} pf = ⊢⊆⊩ {Γ} pf

completeness-for-canonical : ∀ {Γ φ} → Γ ⊩ φ → Γ .theory ⊢ φ
completeness-for-canonical pf = ⊩⊆⊢ pf

canonical-satisfies : ∀ {Γ φ Δ} → Γ .theory ⊢ φ → Γ ≤ Δ → Δ ⊩ φ
canonical-satisfies {Γ} {φ} {Δ} ⊢φ Γ≤Δ = ⊢⊆⊩ {Δ} (Γ≤Δ ↑ ⊢φ)

persistence : ∀ {Γ Δ φ} → Γ ≤ Δ → Γ ⊩ φ → Δ ⊩ φ
persistence  {Γ} {Δ} Γ≤Δ Γ⊩φ = ⊢⊆⊩ {Δ} (Γ≤Δ ↑ (⊩⊆⊢ {Γ .theory} Γ⊩φ))

--------------------------------------------------------------------------
--- Forcing Lemmata ------------------------------------------------------
--------------------------------------------------------------------------

forcing-from : ∀ {Γ φ} → Γ ⊩ φ → Γ .theory φ
forcing-from pf = pf

forcing-to : ∀ {Γ φ} → Γ .theory φ → Γ ⊩ φ
forcing-to pf = pf


forcing-⊥ : ∀ {Γ} → Γ ⊩ 𝟘 → ⊥
forcing-⊥ {Γ} Γ⊩𝟘 =
  let Γᶜ = Γ .canonical
  in  Γᶜ .consistent (assumption Γ⊩𝟘)

forcing→∧ : ∀ {Γ φ ψ} → Γ ⊩ φ ∧ ψ → (Γ ⊩ φ × Γ ⊩ ψ)
forcing→∧ {Γ} {φ} {ψ} Γ∧ =
  let T = Γ .theory
      ⊢φ = ∧e¹ (⊩⊆⊢ {T} Γ∧)
      ⊢ψ = ∧e² (⊩⊆⊢ {T} Γ∧)
  in ⟪ Γ .canonical .closed ⊢φ , Γ .canonical .closed ⊢ψ ⟫

forcing←∧ : ∀ {Γ φ ψ} → (Γ ⊩ φ × Γ ⊩ ψ) → Γ ⊩ φ ∧ ψ
forcing←∧ {Γ} {φ} {ψ} h = ?

forcing-∨ : ∀ {Γ φ ψ} → Γ ⊩ φ ∨ ψ → Γ ⊩ φ ⊎ Γ ⊩ ψ
forcing-∨ {Γ} {φ} {ψ} Γ∨ = Γ .canonical .prime Γ∨

forcing-→ : ∀ {Γ φ ψ Δ} → Γ ⊩ φ ⊃ ψ → Γ ≤ Δ → Δ ⊩ φ → Δ ⊩ ψ
forcing-→ {Γ} {φ} {ψ} {Δ} Γ→ Γ⊆Δ Δ⊩φ = Δ .canonical .closed (⊃ᵉ (Γ⊆Δ ↑ (⊩⊆⊢ {Γ .theory} Γ→)) (⊩⊆⊢ {Δ .theory} Δ⊩φ))

kripke-soundness : ∀ {Γ φ} → Γ ⊢ φ → (w : CanonicalWorld) → (∀ ψ → ψ ∈ Γ → w ⊩ ψ) → w ⊩ φ

kripke-soundness (assumption φ∈Γ) w hyp = hyp _ φ∈Γ

kripke-soundness {Γ} {φ} (𝟘ᵉ Γ⊢𝟘) w hyp = ⊥-elim (w .canonical .consistent (⊩⊆⊢ (kripke-soundness Γ⊢𝟘 w hyp)))

kripke-soundness {Γ} {imp} (⊃ⁱ pf) w hyp =
  let
    deduct = ⊃ⁱ pf
    h = hyp imp
  in kripke-soundness (⊩⊆⊢ {!!}) w hyp

kripke-soundness (⊃ᵉ x₁ x₂) w x = {!!}

kripke-soundness (∨i¹ x₁) w x = {!!}

kripke-soundness (∨i² x₁) w x = {!!}

kripke-soundness (∨ᵉ φ ψ _ x₁ x₂ x₃) w x = {!!}

kripke-soundness (∧ⁱ x₁ x₂) w x = {!!}

kripke-soundness (∧e¹ x₁) w x = {!!}

kripke-soundness (∧e² x₁) w x = {!!}
-- kripke-soundness-assumption : ∀ {Γ : Theory} → ∀ {φ} → (w : CanonicalWorld) → φ ∈ Γ → (∀ ψ → ψ ∈ Γ → w ⊩ ψ) → w ⊩ φ
-- kripke-soundness-assumption {Γ} {φ} w φ∈Γ hyp = (hyp φ) φ∈Γ

-- kripke-soundness-⊃ᵉ : ∀ {Γ : Theory} → ∀ {φ ψ} → (w : CanonicalWorld) → Γ ⊢ φ ⊃ ψ → Γ ⊢ φ → (∀ χ → χ ∈ Γ → w ⊩ χ) → w ⊩ ψ
-- kripke-soundness-⊃ᵉ{Γ} {φ} {ψ} w φ⊃ψ Γ⊢φ hyp =
--   let Γ⊢ψ = ⊃ᵉ φ⊃ψ Γ⊢φ
--   in (hyp ψ) {!!}

-- kripke-soundness-⊃ⁱ :
--   ∀ {Γ φ ψ w} →
--   Γ ∪ ｛ φ ｝ ⊢ ψ →
--   (∀ χ → χ ∈ Γ → w ⊩ χ) →
--   w ⊩ φ ⊃ ψ
-- kripke-soundness-⊃ⁱ = {!!}

-- kripke-soundness-∧ⁱ :
--   ∀ {Γ φ ψ w} →
--   Γ ⊢ φ →
--   Γ ⊢ ψ →
--   (∀ χ → χ ∈ Γ → w ⊩ χ) →
--   w ⊩ φ ∧ ψ
-- kripke-soundness-∧ⁱ = {!!}

-- kripke-soundness-∧e¹ :
--   ∀ {Γ φ ψ w} →
--   Γ ⊢ φ ∧ ψ →
--   (∀ χ → χ ∈ Γ → w ⊩ χ) →
--   w ⊩ φ
-- kripke-soundness-∧e¹ = {!!}

-- kripke-soundness-∧e² :
--   ∀ {Γ φ ψ w} →
--   Γ ⊢ φ ∧ ψ →
--   (∀ χ → χ ∈ Γ → w ⊩ χ) →
--   w ⊩ ψ
-- kripke-soundness-∧e² = {!!}

-- kripke-soundness-∨ⁱ₁ :
--   ∀ {Γ φ ψ w} →
--   Γ ⊢ φ →
--   (∀ χ → χ ∈ Γ → w ⊩ χ) →
--   w ⊩ φ ∨ ψ
-- kripke-soundness-∨ⁱ₁ = {!!}

-- kripke-soundness-∨ⁱ₂ :
--   ∀ {Γ φ ψ w} →
--   Γ ⊢ ψ →
--   (∀ χ → χ ∈ Γ → w ⊩ χ) →
--   w ⊩ φ ∨ ψ
-- kripke-soundness-∨ⁱ₂ = {!!}

-- kripke-soundness-∨ᵉ :
--   ∀ {Γ φ ψ χ w} →
--   Γ ⊢ φ ∨ ψ →
--   Γ ∪ ｛ φ ｝ ⊢ χ →
--   Γ ∪ ｛ ψ ｝ ⊢ χ →
--   (∀ ξ → ξ ∈ Γ → w ⊩ ξ) →
--   w ⊩ χ
-- kripke-soundness-∨ᵉ = {!!}

-- kripke-soundness-exfalso :
--   ∀ {Γ φ w} →
--   Γ ⊢ 𝟘 →
--   (∀ χ → χ ∈ Γ → w ⊩ χ) →
--   w ⊩ φ
-- kripke-soundness-exfalso = {!!}
