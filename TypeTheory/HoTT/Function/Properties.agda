{-# OPTIONS --without-K --safe #-}

module TypeTheory.HoTT.Function.Properties where

-- agda-stdlib
open import Axiom.Extensionality.Propositional
open import Level

-- agda-misc
open import TypeTheory.HoTT.Base

private
  variable
    a b : Level
    A : Set a
    B : Set b

module _ {a b} {A : Set a} {B : Set b} where
  isProp-→ : Extensionality a b → isProp B → isProp (A → B)
  isProp-→ ext B-isProp f g = ext λ x → B-isProp (f x) (g x)
