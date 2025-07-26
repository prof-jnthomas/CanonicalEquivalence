module CanonicalEquivalence.Prelude where

open import Data.Sum.Base public using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Nat public using (ℕ; suc)
open import Data.Nat.Properties  public using (_≟_)
open import Relation.Binary.PropositionalEquality as ≡ public using (_≡_; refl; sym; _≢_; cong)
open import Relation.Unary public using (_∈_; _⊆_; _∪_; _∩_; Pred; ∅; ｛_｝) renaming (∁ to _ᶜ)
open import Relation.Unary.Properties public using (⊆-refl; ⊆-trans)
open import Data.List public using (List; []; _++_; filter; _∷_; [_])
open import Data.List.Relation.Unary.All public using (All; []; _∷_)
open import Data.Product public using (Σ; ∃; proj₁; proj₂; _×_) renaming (_,_ to ⟪_,_⟫)
open import Relation.Nullary.Negation public using (¬_)
open import Relation.Nullary public using (Dec; yes; no; does; proof)
