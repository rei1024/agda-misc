{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Logic.NonConstructiveAxiom.Properties.Transport where

-- agda-stdlib
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Sum as Sum
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality
open import Function.Base
import Function.LeftInverse as LInv -- TODO use new packages
import Function.Equality as Eq

-- agda-misc
open import Math.Logic.NonConstructiveAxiom
open import Math.Logic.Constructive
open import Math.Logic.NonConstructiveAxiom.Properties.Base

------------------------------------------------------------------------
-- transport
module Transport {a b p} {A : Set a} {B : Set b}
  (f : A → B) (g : B → A) (inv : ∀ x → f (g x) ≡ x)
  where
  private
    ∃Pf→∃P : {P : B → Set p} → ∃ (λ x → P (f x)) → ∃ P
    ∃Pf→∃P (x , Pfx) = (f x , Pfx)

    ∃P→∃Pf : {P : B → Set p} → ∃ P → ∃ (λ x → P (f x))
    ∃P→∃Pf {P = P} (x , Px) = g x , subst P (sym (inv x)) Px

    ∃Qg→∃Q : {Q : A → Set p} → ∃ (λ x → Q (g x)) → ∃ Q
    ∃Qg→∃Q (x , Qgx) = g x , Qgx

  lpo-transport : LPO A p → LPO B p
  lpo-transport lpo P? =
    Sum.map ∃Pf→∃P (contraposition ∃P→∃Pf) $ lpo (DecU-map f P?)

  llpo-transport : LLPO A p → LLPO B p
  llpo-transport llpo P? Q? w =
    Sum.map (contraposition ∃P→∃Pf) (contraposition ∃P→∃Pf) $
            llpo (DecU-map f P?) (DecU-map f Q?)
                 (contraposition (Prod.map ∃Pf→∃P ∃Pf→∃P) w)

  wlpo-Alt-transport : WLPO-Alt A p → WLPO-Alt B p
  wlpo-Alt-transport wlpo-Alt P? =
    Sum.map (contraposition ∃P→∃Pf) (DN-map ∃Pf→∃P) $ wlpo-Alt (DecU-map f P?)

  wlpo-transport : WLPO A p → WLPO B p
  wlpo-transport = wlpo-Alt⇒wlpo ∘′ wlpo-Alt-transport ∘′ wlpo⇒wlpo-Alt

  mr-transport : MR A p → MR B p
  mr-transport mr P? ¬¬∃P =
    ∃Pf→∃P $ mr (DecU-map f P?) (DN-map ∃P→∃Pf ¬¬∃P)

  mp-transport : MP A p → MP B p
  mp-transport = mr⇒mp ∘′ mr-transport ∘′ mp⇒mr

  wmp-transport : WMP A p → WMP B p
  wmp-transport wmp {P = P} P? hyp =
    ∃Pf→∃P $ wmp (DecU-map f P?)
    λ Q? → Sum.map (DN-map ∃Qg→∃Q) (DN-map λ {(x , Px , ¬Qgx) →
      g x , (subst P (sym (inv x)) Px) , ¬Qgx }) $ hyp (DecU-map g Q?)

  mp⊎-transport : MP⊎ A p → MP⊎ B p
  mp⊎-transport mp⊎ P? Q? w =
    Sum.map (DN-map ∃Pf→∃P) (DN-map ∃Pf→∃P) $
            mp⊎ (DecU-map f P?) (DecU-map f Q?)
                (contraposition (Prod.map (contraposition ∃P→∃Pf)
                                          (contraposition ∃P→∃Pf)) w)

open Transport public

module TransportByLeftInverse
  {a b p} {A : Set a} {B : Set b} (linv : B LInv.↞ A) =
  Transport {p = p} (LInv.LeftInverse.from linv Eq.⟨$⟩_)
    (LInv.LeftInverse.to linv Eq.⟨$⟩_) (LInv.LeftInverse.left-inverse-of linv)
