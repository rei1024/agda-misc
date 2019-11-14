{-# OPTIONS --without-K --safe #-}

module TypeTheory.HoTT.Data.Empty.Properties where

-- agda-stdlib
open import Data.Empty

-- agda-misc
open import TypeTheory.HoTT.Base

isProp-⊥ : isProp ⊥
isProp-⊥ x = ⊥-elim x
