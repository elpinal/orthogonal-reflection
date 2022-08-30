open import Categories.Category

module Orthogonality {o ℓ e} (𝒞 : Category o ℓ e) where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Categories.Category.Construction.Arrow
open Category 𝒞

record Factorize (K : Obj) {A A′ : Obj} (m : A ⇒ A′) (f : A ⇒ K) : Type (ℓ-max ℓ e) where
  field
    f′ : A′ ⇒ K
    factorize : f ≈ f′ ∘ m
    unique : (g : A′ ⇒ K) → f ≈ g ∘ m → g ≈ f′

Orthogonal : (K : Obj) {A A′ : Obj} (m : A ⇒ A′) → Type (ℓ-max ℓ e)
Orthogonal K {A} m = ∀ (f : A ⇒ K) → Factorize K m f

record Orth (K : Obj) {ℓ′} (ℳ : Morphism 𝒞 → hProp ℓ′) : Type (ℓ-max o (ℓ-max ℓ (ℓ-max e ℓ′))) where
  constructor orth
  field
    prf : ∀ {A A′ : Obj} (m : A ⇒ A′) → typ (ℳ (mor m)) → Orthogonal K m
