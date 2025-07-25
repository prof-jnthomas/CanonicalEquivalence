module CanonicalEquivalence.Syntax where
open import CanonicalEquivalence.Prelude

-- Fixities
infix   4 ⌊_⌋
infix   6 _≃_
infixr 30 _⟶_
infixr 40 _∨_
infixr 50 _∧_

-- Minimal intuitionistic propositional calculus
data Formula : Set where
  𝟘   : Formula
  Var : ℕ → Formula
  _⟶_ : Formula → Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula

Theory : Set₁
Theory = Pred Formula _

_::_ : Formula → Theory → Theory
φ :: Γ = λ ψ → Γ ψ ⊎ (ψ ≡ φ)

-- Lists ↔ theories
⌊_⌋ : List Formula → Theory
⌊ [] ⌋       = λ _ → ⊥
⌊ (φ ∷ xs) ⌋ = φ :: ⌊ xs ⌋

_⊆ˡ_ : List Formula → Theory → Set
xs ⊆ˡ Γ = All (λ φ → Γ φ) xs

-- Decidable syntactic equality
_≃_ : ∀ (φ ψ : Formula) → Dec (φ ≡ ψ)
Var m ≃ Var n with m ≟ n
... | yes refl = yes refl
... | no  p    = no (λ {refl → p refl})

𝟘 ≃ 𝟘 = yes refl
𝟘 ≃ Var n = no λ()
Var n ≃ 𝟘 = no λ()
𝟘 ≃ ψ ⟶ ψ₁ = no λ()
𝟘 ≃ ψ ∧ ψ₁ = no λ()
𝟘 ≃ ψ ∨ ψ₁ = no λ()
φ ⟶ φ₁ ≃ 𝟘 = no λ()
φ ∧ φ₁ ≃ 𝟘 = no λ()
φ ∨ φ₁ ≃ 𝟘 = no λ()
φ ⟶ φ₁ ≃ Var n = no λ()
φ ∧ φ₁ ≃ Var n = no λ()
φ ∨ φ₁ ≃ Var n = no λ()
Var x ≃ ψ ⟶ ψ₁ = no λ()
Var x ≃ ψ ∧ ψ₁ = no λ()
Var x ≃ ψ ∨ ψ₁ = no λ()
φ ⟶ φ₁ ≃ ψ ∧ ψ₁ = no λ()
φ ⟶ φ₁ ≃ ψ ∨ ψ₁ = no λ()
φ ∧ φ₁ ≃ ψ ⟶ ψ₁ = no λ()
φ ∧ φ₁ ≃ ψ ∨ ψ₁ = no λ()
φ ∨ φ₁ ≃ ψ ⟶ ψ₁ = no λ()
φ ∨ φ₁ ≃ ψ ∧ ψ₁ = no λ()
φ ⟶ φ₁ ≃ ψ ⟶ ψ₁ with φ ≃ ψ | φ₁ ≃ ψ₁
... | yes refl | yes refl = yes refl
... | no ¬p    | _         = no λ {refl → ¬p refl}
... | _        | no ¬q     = no λ {refl → ¬q refl}

φ ∧ φ₁ ≃ ψ ∧ ψ₁  with φ ≃ ψ | φ₁ ≃ ψ₁
... | yes refl | yes refl = yes refl
... | no ¬p    | _         = no λ {refl → ¬p refl}
... | _        | no ¬q     = no λ {refl → ¬q refl}

φ ∨ φ₁ ≃ ψ ∨ ψ₁  with φ ≃ ψ | φ₁ ≃ ψ₁
... | yes refl | yes refl = yes refl
... | no ¬p    | _         = no λ {refl → ¬p refl}
... | _        | no ¬q     = no λ {refl → ¬q refl}
