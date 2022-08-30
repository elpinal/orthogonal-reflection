open import Categories.Category
open import Categories.Category.Cocomplete
open import Categories.Category.Construction.Arrow

open import Cubical.Foundations.HLevels

module OrthogonalReflection
  {o ℓ e} (𝒞 : Category o ℓ e)
  (CC : ∀ {o′ ℓ′ e′} → Cocomplete o′ ℓ′ e′ 𝒞)
  {ℓ₁} (ℳ : Morphism 𝒞 → hProp ℓ₁)
  (K : Category.Obj 𝒞) where

open import Cubical.Core.Everything hiding (Sub)
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat

open import Categories.Category.Diagram.Span 𝒞
open import Categories.Category.SubCategory 𝒞
open import Categories.Functor hiding (id)
open import Categories.Functor.Construction.SubCategory 𝒞
open import Categories.Diagram.Colimit
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open import Data.Ordinal

open Category 𝒞

P : Ω → Type (ℓ-max o ℓ)
P _ = Σ[ X ∈ Obj ] (K ⇒ X)

z : P Z
z = K , id

module Suc (μ : Ω) (Pμ : P μ) where
  Xᵢ : Obj
  Xᵢ = fst Pμ

  data JObj : Type (ℓ-max o (ℓ-max ℓ (ℓ-max e ℓ₁))) where
    base : JObj
    spanApex : {A′ : Obj} → (S : Span Xᵢ A′) → typ (ℳ (mor (Span.cod S))) → JObj
    spanY  : (A′ : Obj) → (S : Span Xᵢ A′) → typ (ℳ (mor (Span.cod S))) → JObj
    parDom : (A′ : Obj) → (p q : A′ ⇒ Xᵢ) → {A : Obj} → (m : A ⇒ A′) → typ (ℳ (mor m)) → p ∘ m ≈ q ∘ m → JObj
      -- TODO: p and q might be distinct

  U : JObj → Obj
  U base = Xᵢ
  U (spanApex S₁ _) = Span.M S₁
  U (spanY A′ _ _) = A′
  U (parDom A′ _ _ _ _ _) = A′

  data R : ∀ (a b : JObj) → U a ⇒ U b → Set (ℓ-max o (ℓ-max ℓ (ℓ-max e ℓ₁))) where
    ident : ∀ {a : JObj} → R a a id
    ≈-closed : ∀ {a b : JObj} {f g : U a ⇒ U b} → f ≈ g → R a b f → R a b g
    spanDom : {A′ : Obj} → (S : Span Xᵢ A′) → (prf : typ (ℳ (mor (Span.cod S)))) → R (spanApex S prf) base (Span.dom S)
    spanCod : (A′ : Obj) → (S : Span Xᵢ A′) → (prf : typ (ℳ (mor (Span.cod S)))) → R (spanApex S prf) (spanY A′ S prf) (Span.cod S)
    par1 : {A′ : Obj} → (p q : A′ ⇒ Xᵢ) → {A : Obj} → (m : A ⇒ A′) → (prf : typ (ℳ (mor m))) → (eq : p ∘ m ≈ q ∘ m) → R (parDom A′ p q m prf eq) base p
    par2 : {A′ : Obj} → (p q : A′ ⇒ Xᵢ) → {A : Obj} → (m : A ⇒ A′) → (prf : typ (ℳ (mor m))) → (eq : p ∘ m ≈ q ∘ m) → R (parDom A′ p q m prf eq) base q

  _∘R_ : ∀ {a b c : JObj} {g : U b ⇒ U c} {f : U a ⇒ U b} → R b c g → R a b f → R a c (g ∘ f)
  ident ∘R r₂ = ≈-closed (Equiv.sym identityˡ) r₂
  ≈-closed eq r₁ ∘R r₂ = ≈-closed (∘-resp-≈ˡ eq) (r₁ ∘R r₂)
  spanDom S₁ prf ∘R ident = ≈-closed (Equiv.sym identityʳ) (spanDom S₁ prf)
  spanDom S₁ prf ∘R ≈-closed eq r₂ = ≈-closed (∘-resp-≈ʳ eq) (spanDom S₁ prf ∘R r₂)
  spanCod A′ S₁ prf ∘R ident = ≈-closed (Equiv.sym identityʳ) (spanCod A′ S₁ prf)
  spanCod A′ S₁ prf ∘R ≈-closed eq r₂ = ≈-closed (∘-resp-≈ʳ eq) (spanCod A′ S₁ prf ∘R r₂)
  par1 _ q m prf _ ∘R ident = ≈-closed (Equiv.sym identityʳ) (par1 _ q m prf _)
  par1 _ q m prf _ ∘R ≈-closed eq r₂ = ≈-closed (∘-resp-≈ʳ eq) (par1 _ q m prf _ ∘R r₂)
  par2 p _ m prf _ ∘R ident = ≈-closed (Equiv.sym identityʳ) (par2 p _ m prf _)
  par2 p _ m prf _ ∘R ≈-closed eq r₂ = ≈-closed (∘-resp-≈ʳ eq) (par2 p _ m prf _ ∘R r₂)

  sc : SubCat JObj
  sc = record
    { U = U
    ; R = λ {a} {b} → R a b
    ; Rid = ident
    ; _∘R_ = _∘R_
    }

  J : Category _ _ _
  J = SubCategory sc

  D : Functor J 𝒞
  D = Sub sc

  colim : Colimit D
  colim = CC D

  s : P (S μ)
  s = Colimit.coapex colim , Colimit.proj colim base ∘ snd Pμ

  step : Xᵢ ⇒ fst s
  step = Colimit.proj colim base

  f′ : ∀ A′ → (Sp : Span Xᵢ A′) → typ (ℳ (mor (Span.cod Sp))) → A′ ⇒ fst s
  f′ A′ Sp prf = Colimit.proj colim (spanY A′ Sp prf)

module Lim (α : ℕ → Ω) (hyp : ∀ n → P (α n)) where
  data JObj : Type where
    base : JObj
    prev : ℕ → JObj

  U : JObj → Obj
  U base = K
  U (prev n) = fst (hyp n)

  data R : ∀ (a b : JObj) → U a ⇒ U b → Type (ℓ-max ℓ e) where
    ident : ∀ {a} → R a a (id {U a})
    ≈-closed : ∀ {a b : JObj} {f g : U a ⇒ U b} → f ≈ g → R a b f → R a b g
    inj : ∀ n → R base (prev n) (snd (hyp n))

  _∘R_ : ∀ {a b c : JObj} {g : U b ⇒ U c} {f : U a ⇒ U b} → R b c g → R a b f → R a c (g ∘ f)
  r₁ ∘R ident = ≈-closed (Equiv.sym identityʳ) r₁
  r₁ ∘R ≈-closed eq r₂ = ≈-closed (∘-resp-≈ʳ eq) (r₁ ∘R r₂)
  ident ∘R inj n = ≈-closed (Equiv.sym identityˡ) (inj n)
  ≈-closed eq r₁ ∘R inj n = ≈-closed (∘-resp-≈ˡ eq) (r₁ ∘R inj n)

  sc : SubCat JObj
  sc = record
    { U = U
    ; R = λ {a} {b} f → R a b f
    ; Rid = ident
    ; _∘R_ = _∘R_
    }

  J : Category _ _ _
  J = SubCategory sc

  D : Functor J 𝒞
  D = Sub sc

  colim : Colimit D
  colim = CC D

  l : P (L α)
  l = Colimit.coapex colim , Colimit.proj colim base

construct : ∀ (o : Ω) → P o
construct = transInd P z Suc.s Lim.l


module Properties where
  open import Orthogonality 𝒞

  module _ (i₀ : Ω) where
    P_i₀ : P i₀
    P_i₀ = construct i₀

    X_i₀ : Obj
    X_i₀ = fst P_i₀

    X_i₀+1 : Obj
    X_i₀+1 = fst (Suc.s i₀ P_i₀)

    step : X_i₀ ⇒ X_i₀+1
    step = Suc.step i₀ P_i₀

    module T = Suc i₀ P_i₀

    module _ (iso : IsIso step) {A A′ : Obj} (m : A ⇒ A′) (m∈ℳ : typ (ℳ (mor m))) where
      module I = IsIso iso
      module S = Switch (record { from = step ; to = I.inv ; iso = I.iso })

      O : Orthogonal X_i₀ m
      O f =
        record
          { f′ = f′
          ; factorize = factorize
          ; unique = λ g eq → S.cancel-fromˡ
              let open HomReasoning in
              let gm≈f′m = Equiv.trans (Equiv.sym eq) factorize in
              begin
                step ∘ g
              ≈⟨ Colimit.colimit-commute T.colim (g , T.par1 g f′ m m∈ℳ gm≈f′m) ⟩
                Colimit.proj T.colim (T.parDom A′ g f′ m m∈ℳ gm≈f′m)
              ≈˘⟨ Colimit.colimit-commute T.colim (f′ , T.par2 g f′ m m∈ℳ gm≈f′m) ⟩
                step ∘ f′
              ∎
          }
        where
          Sp : Span X_i₀ A′
          Sp = record { M = A ; dom = f ; cod = m }

          f′ : A′ ⇒ X_i₀
          f′ = I.inv ∘ Suc.f′ i₀ P_i₀ A′ Sp m∈ℳ

          factorize : f ≈ f′ ∘ m
          factorize = Equiv.trans (S.switch-fromtoˡ
            let open HomReasoning in
            begin
              step ∘ f
            ≈⟨ Colimit.colimit-commute T.colim (f , T.spanDom Sp m∈ℳ) ⟩
              Colimit.proj T.colim (T.spanApex Sp m∈ℳ)
            ≈˘⟨ Colimit.colimit-commute T.colim (m , T.spanCod A′ Sp m∈ℳ) ⟩
              (Suc.f′ i₀ P_i₀ A′ Sp m∈ℳ) ∘ m
            ∎) sym-assoc

    -- LPAC, Proposition 1.37 (1).
    lemma : IsIso step → Orth X_i₀ ℳ
    lemma iso = orth (O iso)
