{-# OPTIONS --without-K --safe #-}

module TypeTheory.HoTT.Relation.Nullary.Negation.Properties where

-- agda-stdlib
open import Axiom.Extensionality.Propositional
open import Level renaming (zero to lzero)
open import Relation.Nullary

-- agda-misc
open import TypeTheory.HoTT.Base
open import TypeTheory.HoTT.Data.Empty.Properties
open import TypeTheory.HoTT.Function.Properties

private
  variable
    a b : Level
    A : Set a
    B : Set b

module _ {a} {A : Set a} where
  isProp-¬ : Extensionality a lzero → isProp (¬ A)
  isProp-¬ ext = isProp-→ ext isProp-⊥
