open import Categories.Category
open import Categories.Category.Cocomplete
open import Categories.Category.Construction.Arrow

open import Cubical.Foundations.HLevels

module OrthogonalReflection
  {o ā e} (š : Category o ā e)
  (CC : ā {oā² āā² eā²} ā Cocomplete oā² āā² eā² š)
  {āā} (ā³ : Morphism š ā hProp āā)
  (K : Category.Obj š) where

open import Cubical.Core.Everything hiding (Sub)
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat

open import Categories.Category.Diagram.Span š
open import Categories.Category.SubCategory š
open import Categories.Functor hiding (id)
open import Categories.Functor.Construction.SubCategory š
open import Categories.Diagram.Colimit
open import Categories.Morphism š
open import Categories.Morphism.Reasoning š

open import Data.Ordinal

open Category š

P : Ī© ā Type (ā-max o ā)
P _ = Ī£[ X ā Obj ] (K ā X)

z : P Z
z = K , id

module Suc (Ī¼ : Ī©) (PĪ¼ : P Ī¼) where
  Xįµ¢ : Obj
  Xįµ¢ = fst PĪ¼

  data JObj : Type (ā-max o (ā-max ā (ā-max e āā))) where
    base : JObj
    spanApex : {Aā² : Obj} ā (S : Span Xįµ¢ Aā²) ā typ (ā³ (mor (Span.cod S))) ā JObj
    spanY  : (Aā² : Obj) ā (S : Span Xįµ¢ Aā²) ā typ (ā³ (mor (Span.cod S))) ā JObj
    parDom : (Aā² : Obj) ā (p q : Aā² ā Xįµ¢) ā {A : Obj} ā (m : A ā Aā²) ā typ (ā³ (mor m)) ā p ā m ā q ā m ā JObj
      -- TODO: p and q might be distinct

  U : JObj ā Obj
  U base = Xįµ¢
  U (spanApex Sā _) = Span.M Sā
  U (spanY Aā² _ _) = Aā²
  U (parDom Aā² _ _ _ _ _) = Aā²

  data R : ā (a b : JObj) ā U a ā U b ā Set (ā-max o (ā-max ā (ā-max e āā))) where
    ident : ā {a : JObj} ā R a a id
    ā-closed : ā {a b : JObj} {f g : U a ā U b} ā f ā g ā R a b f ā R a b g
    spanDom : {Aā² : Obj} ā (S : Span Xįµ¢ Aā²) ā (prf : typ (ā³ (mor (Span.cod S)))) ā R (spanApex S prf) base (Span.dom S)
    spanCod : (Aā² : Obj) ā (S : Span Xįµ¢ Aā²) ā (prf : typ (ā³ (mor (Span.cod S)))) ā R (spanApex S prf) (spanY Aā² S prf) (Span.cod S)
    par1 : {Aā² : Obj} ā (p q : Aā² ā Xįµ¢) ā {A : Obj} ā (m : A ā Aā²) ā (prf : typ (ā³ (mor m))) ā (eq : p ā m ā q ā m) ā R (parDom Aā² p q m prf eq) base p
    par2 : {Aā² : Obj} ā (p q : Aā² ā Xįµ¢) ā {A : Obj} ā (m : A ā Aā²) ā (prf : typ (ā³ (mor m))) ā (eq : p ā m ā q ā m) ā R (parDom Aā² p q m prf eq) base q

  _āR_ : ā {a b c : JObj} {g : U b ā U c} {f : U a ā U b} ā R b c g ā R a b f ā R a c (g ā f)
  ident āR rā = ā-closed (Equiv.sym identityĖ”) rā
  ā-closed eq rā āR rā = ā-closed (ā-resp-āĖ” eq) (rā āR rā)
  spanDom Sā prf āR ident = ā-closed (Equiv.sym identityŹ³) (spanDom Sā prf)
  spanDom Sā prf āR ā-closed eq rā = ā-closed (ā-resp-āŹ³ eq) (spanDom Sā prf āR rā)
  spanCod Aā² Sā prf āR ident = ā-closed (Equiv.sym identityŹ³) (spanCod Aā² Sā prf)
  spanCod Aā² Sā prf āR ā-closed eq rā = ā-closed (ā-resp-āŹ³ eq) (spanCod Aā² Sā prf āR rā)
  par1 _ q m prf _ āR ident = ā-closed (Equiv.sym identityŹ³) (par1 _ q m prf _)
  par1 _ q m prf _ āR ā-closed eq rā = ā-closed (ā-resp-āŹ³ eq) (par1 _ q m prf _ āR rā)
  par2 p _ m prf _ āR ident = ā-closed (Equiv.sym identityŹ³) (par2 p _ m prf _)
  par2 p _ m prf _ āR ā-closed eq rā = ā-closed (ā-resp-āŹ³ eq) (par2 p _ m prf _ āR rā)

  sc : SubCat JObj
  sc = record
    { U = U
    ; R = Ī» {a} {b} ā R a b
    ; Rid = ident
    ; _āR_ = _āR_
    }

  J : Category _ _ _
  J = SubCategory sc

  D : Functor J š
  D = Sub sc

  colim : Colimit D
  colim = CC D

  s : P (S Ī¼)
  s = Colimit.coapex colim , Colimit.proj colim base ā snd PĪ¼

  step : Xįµ¢ ā fst s
  step = Colimit.proj colim base

  fā² : ā Aā² ā (Sp : Span Xįµ¢ Aā²) ā typ (ā³ (mor (Span.cod Sp))) ā Aā² ā fst s
  fā² Aā² Sp prf = Colimit.proj colim (spanY Aā² Sp prf)

module Lim (Ī± : ā ā Ī©) (hyp : ā n ā P (Ī± n)) where
  data JObj : Type where
    base : JObj
    prev : ā ā JObj

  U : JObj ā Obj
  U base = K
  U (prev n) = fst (hyp n)

  data R : ā (a b : JObj) ā U a ā U b ā Type (ā-max ā e) where
    ident : ā {a} ā R a a (id {U a})
    ā-closed : ā {a b : JObj} {f g : U a ā U b} ā f ā g ā R a b f ā R a b g
    inj : ā n ā R base (prev n) (snd (hyp n))

  _āR_ : ā {a b c : JObj} {g : U b ā U c} {f : U a ā U b} ā R b c g ā R a b f ā R a c (g ā f)
  rā āR ident = ā-closed (Equiv.sym identityŹ³) rā
  rā āR ā-closed eq rā = ā-closed (ā-resp-āŹ³ eq) (rā āR rā)
  ident āR inj n = ā-closed (Equiv.sym identityĖ”) (inj n)
  ā-closed eq rā āR inj n = ā-closed (ā-resp-āĖ” eq) (rā āR inj n)

  sc : SubCat JObj
  sc = record
    { U = U
    ; R = Ī» {a} {b} f ā R a b f
    ; Rid = ident
    ; _āR_ = _āR_
    }

  J : Category _ _ _
  J = SubCategory sc

  D : Functor J š
  D = Sub sc

  colim : Colimit D
  colim = CC D

  l : P (L Ī±)
  l = Colimit.coapex colim , Colimit.proj colim base

construct : ā (o : Ī©) ā P o
construct = transInd P z Suc.s Lim.l


module Properties where
  open import Orthogonality š

  module _ (iā : Ī©) where
    P_iā : P iā
    P_iā = construct iā

    X_iā : Obj
    X_iā = fst P_iā

    X_iā+1 : Obj
    X_iā+1 = fst (Suc.s iā P_iā)

    step : X_iā ā X_iā+1
    step = Suc.step iā P_iā

    module T = Suc iā P_iā

    module _ (iso : IsIso step) {A Aā² : Obj} (m : A ā Aā²) (māā³ : typ (ā³ (mor m))) where
      module I = IsIso iso
      module S = Switch (record { from = step ; to = I.inv ; iso = I.iso })

      O : Orthogonal X_iā m
      O f =
        record
          { fā² = fā²
          ; factorize = factorize
          ; unique = Ī» g eq ā S.cancel-fromĖ”
              let open HomReasoning in
              let gmāfā²m = Equiv.trans (Equiv.sym eq) factorize in
              begin
                step ā g
              āāØ Colimit.colimit-commute T.colim (g , T.par1 g fā² m māā³ gmāfā²m) ā©
                Colimit.proj T.colim (T.parDom Aā² g fā² m māā³ gmāfā²m)
              āĖāØ Colimit.colimit-commute T.colim (fā² , T.par2 g fā² m māā³ gmāfā²m) ā©
                step ā fā²
              ā
          }
        where
          Sp : Span X_iā Aā²
          Sp = record { M = A ; dom = f ; cod = m }

          fā² : Aā² ā X_iā
          fā² = I.inv ā Suc.fā² iā P_iā Aā² Sp māā³

          factorize : f ā fā² ā m
          factorize = Equiv.trans (S.switch-fromtoĖ”
            let open HomReasoning in
            begin
              step ā f
            āāØ Colimit.colimit-commute T.colim (f , T.spanDom Sp māā³) ā©
              Colimit.proj T.colim (T.spanApex Sp māā³)
            āĖāØ Colimit.colimit-commute T.colim (m , T.spanCod Aā² Sp māā³) ā©
              (Suc.fā² iā P_iā Aā² Sp māā³) ā m
            ā) sym-assoc

    -- LPAC, Proposition 1.37 (1).
    lemma : IsIso step ā Orth X_iā ā³
    lemma iso = orth (O iso)
