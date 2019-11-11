------------------------------------------------------------------------
-- Searchable set
------------------------------------------------------------------------

-- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.127.3062&rep=rep1&type=pdf
-- http://www.cs.bham.ac.uk/~mhe/papers/omniscient-2011-07-06.pdf

{-# OPTIONS --without-K --safe --exact-split #-}

module Constructive.Searchable where

-- agda-stdlib
open import Data.Bool
open import Data.Empty
open import Data.Product as Prod
open import Data.Sum as Sum
open import Function.Base
open import Relation.Binary.PropositionalEquality
import Function.Equivalence as Eqv -- TOOD use new function bundle

-- agda-misc
open import Constructive.Axiom
open import Constructive.Combinators

-- Searchable set
Searchable : ∀ {a} → Set a → Set a
Searchable A = Σ ((A → Bool) → A)
                 λ ε → (P : A → Bool) → P (ε P) ≡ true → (x : A) → P x ≡ true

module SearchModule {a} {A : Set a} (searchable : Searchable A) where
  ε : ((A → Bool) → A)
  ε = proj₁ searchable
  ε-correct : (P : A → Bool) → P (ε P) ≡ true → (x : A) → P x ≡ true
  ε-correct = proj₂ searchable

-- Lemma 2.1
searchable⇒lpo-Bool-Alt : ∀ {a} {A : Set a} → Searchable A → LPO-Bool-Alt A
searchable⇒lpo-Bool-Alt (ε , ε-correct) P with P (ε P) | inspect P (ε P)
... | false | [ P[εP]≡false ] = inj₁ (ε P , P[εP]≡false)
... | true  | [ P[εP]≡true  ] = inj₂ (ε-correct P P[εP]≡true)

-- Lemma 2.2
module Lemma2-2 {a} {A : Set a} (searchable : Searchable A) where
  open SearchModule searchable
  module _ {P : A → Bool} where
    ∃x→Px≡false→P[εP]≡false : (∃ λ x → P x ≡ false) → P (ε P) ≡ false
    ∃x→Px≡false→P[εP]≡false e =
      x≢true⇒x≡false $ contraposition (ε-correct P)
                                      (∃¬P→¬∀P (Prod.map₂ x≡false⇒x≢true e))
        where
        x≡false⇒x≢true : ∀ {x} → x ≡ false → x ≢ true
        x≡false⇒x≢true {false} refl ()
        x≢true⇒x≡false : ∀ {x} → x ≢ true → x ≡ false
        x≢true⇒x≡false {false} neq = refl
        x≢true⇒x≡false {true } neq = ⊥-elim $ neq refl

    ∃x→Px≡false⇔P[εP]≡false : (∃ λ x → P x ≡ false) Eqv.⇔ P (ε P) ≡ false
    ∃x→Px≡false⇔P[εP]≡false =
      Eqv.equivalence ∃x→Px≡false→P[εP]≡false λ eq → ε P , eq

  -- E_X
  Exist : (A → Bool) → Bool
  Exist P = P (ε P)

  Exist[P]≡false⇔∃x→Px≡false :
    {P : A → Bool} → Exist P ≡ false Eqv.⇔ (∃ λ x → P x ≡ false)
  Exist[P]≡false⇔∃x→Px≡false = Eqv.sym ∃x→Px≡false⇔P[εP]≡false

open Lemma2-2

Exhaustible : ∀ {a} → Set a → Set a
Exhaustible A = Σ ((A → Bool) → Bool) λ ∀K →
  (P : A → Bool) → ∀K P ≡ true → ∀ x → P x ≡ true
