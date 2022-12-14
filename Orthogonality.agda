open import Categories.Category

module Orthogonality {o â e} (đ : Category o â e) where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Categories.Category.Construction.Arrow
open Category đ

record Factorize (K : Obj) {A Aâ˛ : Obj} (m : A â Aâ˛) (f : A â K) : Type (â-max â e) where
  field
    fâ˛ : Aâ˛ â K
    factorize : f â fâ˛ â m
    unique : (g : Aâ˛ â K) â f â g â m â g â fâ˛

Orthogonal : (K : Obj) {A Aâ˛ : Obj} (m : A â Aâ˛) â Type (â-max â e)
Orthogonal K {A} m = â (f : A â K) â Factorize K m f

record Orth (K : Obj) {ââ˛} (âł : Morphism đ â hProp ââ˛) : Type (â-max o (â-max â (â-max e ââ˛))) where
  constructor orth
  field
    prf : â {A Aâ˛ : Obj} (m : A â Aâ˛) â typ (âł (mor m)) â Orthogonal K m
