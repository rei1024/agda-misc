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
open import Constructive.Axiom.Properties.Base
open import Constructive.Axiom.Properties.Bool
open import Constructive.Common
open import Constructive.Combinators

module SearchModule {a} {A : Set a} (searchable : Searchable-Bool A) where
  ε : ((A → Bool) → A)
  ε = proj₁ searchable
  ε-correct : (P : A → Bool) → P (ε P) ≡ true → (x : A) → P x ≡ true
  ε-correct = proj₂ searchable

-- Lemma 2.1
searchable-Bool⇒lpo-Bool-Alt : ∀ {a} {A : Set a} → Searchable-Bool A → LPO-Bool-Alt A
searchable-Bool⇒lpo-Bool-Alt (ε , ε-correct) P with P (ε P) | inspect P (ε P)
... | false | [ P[εP]≡false ] = inj₁ (ε P , P[εP]≡false)
... | true  | [ P[εP]≡true  ] = inj₂ (ε-correct P P[εP]≡true)

searchable-Bool⇒inhabited : ∀ {a} {A : Set a} → Searchable-Bool A → Inhabited A
searchable-Bool⇒inhabited searchable-Bool = (proj₁ searchable-Bool) λ _ → true

-- Inhabited ∧ LPO-Bool-Alt => Searchable-Bool
inhabited∧lpo-Bool-Alt⇒ε : ∀ {a} {A : Set a} → Inhabited A → LPO-Bool-Alt A → (A → Bool) → A
inhabited∧lpo-Bool-Alt⇒ε inhabited lpo-Bool-Alt P with lpo-Bool-Alt P
... | inj₁ (x , _) = x
... | inj₂ _       = inhabited

inhabited∧lpo-Bool-Alt⇒ε-correct :
  ∀ {a} {A : Set a} (i : Inhabited A) (lpo-Bool-Alt : LPO-Bool-Alt A) (P : A → Bool) →
 P ((inhabited∧lpo-Bool-Alt⇒ε i lpo-Bool-Alt) P) ≡ true → (x : A) → P x ≡ true
inhabited∧lpo-Bool-Alt⇒ε-correct inhabited lpo-Bool-Alt P with lpo-Bool-Alt P
... | inj₁ (x , Px≡false) =
  λ Px≡true → ⊥-elim $ false≢true $ trans (sym Px≡false) Px≡true
  where
  false≢true : false ≢ true
  false≢true ()
... | inj₂ ∀x→Px≡true     = λ _ → ∀x→Px≡true

inhabited∧lpo-Bool-Alt⇒searchable-Bool :
  ∀ {a} {A : Set a} → Inhabited A → LPO-Bool-Alt A → Searchable-Bool A
inhabited∧lpo-Bool-Alt⇒searchable-Bool inhabited lpo-Bool-Alt =
  inhabited∧lpo-Bool-Alt⇒ε inhabited lpo-Bool-Alt ,
  inhabited∧lpo-Bool-Alt⇒ε-correct inhabited lpo-Bool-Alt

-- Searchable-Bool <=> Searchable
searchable-Bool⇒searchable : ∀ {a p} {A : Set a} →
                             Searchable-Bool A → Searchable A p
searchable-Bool⇒searchable {a} {p} {A} searchable-Bool =
  inhabited∧lpo⇒searchable inhabited lpo
  where
  inhabited = searchable-Bool⇒inhabited searchable-Bool
  lpo : LPO A p
  lpo = lpo-Bool⇒lpo p $ lpo-Bool-Alt⇒lpo-Bool $
          searchable-Bool⇒lpo-Bool-Alt searchable-Bool

searchable⇒searchable-Bool : ∀ {a p} {A : Set a} →
                             Searchable A p → Searchable-Bool A
searchable⇒searchable-Bool searchable =
  inhabited∧lpo-Bool-Alt⇒searchable-Bool inhabited lpo-Bool-Alt
  where
  inhabited = searchable⇒inhabited searchable
  lpo-Bool-Alt = lpo-Bool⇒lpo-Bool-Alt $ lpo⇒lpo-Bool $ searchable⇒lpo searchable

-- Lemma 2.2
module Lemma2-2 {a} {A : Set a} (searchable-Bool : Searchable-Bool A) where
  open SearchModule searchable-Bool
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
