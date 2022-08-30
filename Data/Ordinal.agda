module Data.Ordinal where

open import Cubical.Core.Everything
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Structure
-- open import Cubical.Foundations.Prelude
-- open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Nat
open import Cubical.Data.Unit

-- https://www.cs.bham.ac.uk/~mhe/papers/ordinals/ordinals.html

data Ω : Type where
  Z : Ω
  S : Ω → Ω
  L : (ℕ → Ω) → Ω

module _ {ℓ} (P : Ω → Type ℓ)
  (z : P Z)
  (s : ∀ o → P o → P (S o))
  (l : ∀ α → (∀ n → P (α n)) → P (L α)) where
  transInd : ∀ o → P o
  transInd Z = z
  transInd (S o) = s o (transInd o)
  transInd (L α) = l α (λ n → transInd (α n))

module Examples where
  fromℕ : ℕ → Ω
  fromℕ zero = Z
  fromℕ (suc n) = S (fromℕ n)

  ω : Ω
  ω = L fromℕ


  o+n : Ω → ℕ → Ω
  o+n o zero = o
  o+n o (suc n) = S (o+n o n)

  -- ω·(n+1)
  ω·n+1 : ℕ → Ω
  ω·n+1 zero = ω
  ω·n+1 (suc n) = L (o+n (ω·n+1 n))

  ω² : Ω
  ω² = L ω·n+1

  -- ω²·(n+1)
  ω²·n+1 : ℕ → Ω
  ω²·n+1 zero = ω²
  ω²·n+1 (suc n) = L (o+n (ω²·n+1 n))


module Church where
  data Br {ℓ} (X : Type ℓ) : Type ℓ where
    z : Br X
    s : X → Br X
    l : (α : ℕ → X) → Br X

  Br-map : ∀ {ℓ} {X : Type ℓ} {ℓ′} {Y : Type ℓ′} → (X → Y) → Br X → Br Y
  Br-map f z = z
  Br-map f (s x) = s (f x)
  Br-map f (l α) = l λ n → f (α n)

  -- Br-Algebra.
  Alg : ∀ {ℓ} → Type ℓ → Type ℓ
  Alg X = Br X → X

  -- Church encoding.
  O : ∀ {ℓ} → Type ℓ → Type ℓ
  O X = Alg X → X

  module Ω≅BrΩ where
    unroll : Ω → Br Ω
    unroll Z = z
    unroll (S o) = s o
    unroll (L α) = l α

    roll : Br Ω → Ω
    roll z = Z
    roll (s o) = S o
    roll (l α) = L α

    thm1 : ∀ o → roll (unroll o) ≡ o
    thm1 Z _ = Z
    thm1 (S o) _ = S o
    thm1 (L α) _ = L α

    thm2 : ∀ b → unroll (roll b) ≡ b
    thm2 z _ = z
    thm2 (s x) _ = s x
    thm2 (l α) _ = l α

  module initial-Br-Alg {ℓ} {X : Type ℓ} (h : Alg X) where
    cata : Ω → X
    cata Z = h z
    cata (S o) = h (s (cata o))
    cata (L α) = h (l λ n → cata (α n))

    thm : ∀ (b : Br Ω) → cata (Ω≅BrΩ.roll b) ≡ h (Br-map cata b)
    thm z i = h z
    thm (s x) i = h (s (cata x))
    thm (l α) i = h (l λ n → cata (α n))

    -- uniqueness

  Ω→ΩAlg : Alg (Ω → Ω)
  Ω→ΩAlg z o = o
  Ω→ΩAlg (s f) o = S (f o)
  Ω→ΩAlg (l α) o = L λ n → α n o

  Ω→ΩAlg′ : Alg (Ω → Ω)
  Ω→ΩAlg′ z o = S o
  Ω→ΩAlg′ (s f) o = L λ n → iter n f o
  Ω→ΩAlg′ (l α) o = L λ n → α n o

  -- addition?
  _ : Ω → Ω → Ω
  _ = initial-Br-Alg.cata Ω→ΩAlg

  -- Cantor hierarchy?
  ch : Ω → Ω → Ω
  ch = initial-Br-Alg.cata Ω→ΩAlg′

  -- 0 o = o + 1
  -- 1 o = lim_n (o + n) = o + ω
  -- 2 o = lim_n (o + ω·n) = o + ω·ω
  -- 3 o = lim_n (o + ω²·n) = o + ω³

  ω^ω : Ω
  ω^ω = L λ n → ch (Examples.fromℕ n) Z
