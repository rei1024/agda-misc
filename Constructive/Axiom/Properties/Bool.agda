-- convert between `X` and `X-Bool`

{-# OPTIONS --without-K --safe --exact-split #-}

module Constructive.Axiom.Properties.Bool where

-- agda-stdlib
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; not)
open import Data.Sum as Sum
open import Data.Product as Prod
open import Function.Base
import Function.LeftInverse as LInv -- TODO use new packages
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym; cong)

-- agda-misc
open import Constructive.Axiom
open import Constructive.Combinators
open import Constructive.Common

------------------------------------------------------------------------
-- Bool version of axioms
private
  module _ {a p} {A : Set a} {P : A → Set p} where
    toBool : DecU P → (A → Bool)
    toBool P? x = ⌊ dec⊎⇒dec (P? x) ⌋

  toBool-Lift : ∀ {a} p {A : Set a} (P : A → Bool) →
    DecU (λ x → lift {ℓ = p} (P x) ≡ lift true)
  toBool-Lift p P x with P x
  ... | false = inj₂ (λ ())
  ... | true  = inj₁ refl

-- LPO <=> LPO-Bool
private
  lift-injective : ∀ {a ℓ} {A : Set a} {x y : A} → lift {ℓ = ℓ} x ≡ lift y → x ≡ y
  lift-injective refl = refl

  lift-injective′ : ∀ {a ℓ} {A : Set a} {P : A → Bool} →
    ∃ (λ z → lift {ℓ = ℓ} (P z) ≡ lift true) → ∃ (λ x → P x ≡ true)
  lift-injective′ = Prod.map₂ lift-injective

  lift-cong′ : ∀ {a p} {A : Set a} {P : A → Bool} →
    ∃ (λ n → P n ≡ true) → ∃ (λ z → lift (P z) ≡ lift true)
  lift-cong′ {p = p} (x , y) = x , cong (lift {ℓ = p}) y

  module _ {a p} {A : Set a} {P : A → Set p} (P? : DecU P) where
    from-eq : ∀ x → toBool P? x ≡ true → P x
    from-eq x eq with P? x
    from-eq x eq | inj₁ Px = Px
    from-eq x () | inj₂ ¬Px

    equal-refl : (∃P : ∃ P) → toBool P? (proj₁ ∃P) ≡ true
    equal-refl (x , Px) with P? x
    ... | inj₁ _   = refl
    ... | inj₂ ¬Px = ⊥-elim $ ¬Px Px

    ∃eq⇒∃P : (∃ λ x → toBool P? x ≡ true) → ∃ P
    ∃eq⇒∃P (x , eq) = x , from-eq x eq

    ∃P⇒∃eq : ∃ P → ∃ λ x → toBool P? x ≡ true
    ∃P⇒∃eq ∃P@(x , Px) = x , equal-refl ∃P

lpo⇒lpo-Bool : ∀ {a p} {A : Set a} → LPO A p → LPO-Bool A
lpo⇒lpo-Bool {a} {p} lpo P =
  Sum.map lift-injective′ (contraposition lift-cong′) $ lpo (toBool-Lift p P)

lpo-Bool⇒lpo : ∀ {a} p {A : Set a} → LPO-Bool A → LPO A p
lpo-Bool⇒lpo p lpo-Bool P? =
  Sum.map (∃eq⇒∃P P?) (contraposition (∃P⇒∃eq P?)) $
          lpo-Bool (toBool P?)

-- LLPO <=> LLPO-Bool
llpo⇒llpo-Bool : ∀ {a p} {A : Set a} → LLPO A p → LLPO-Bool A
llpo⇒llpo-Bool {a} {p} llpo P Q h =
  Sum.map (contraposition lift-cong′) (contraposition lift-cong′) $
          llpo (toBool-Lift p P) (toBool-Lift p Q)
          (contraposition (Prod.map lift-injective′ lift-injective′) h)

llpo-Bool⇒llpo : ∀ {a} p {A : Set a} → LLPO-Bool A → LLPO A p
llpo-Bool⇒llpo p llpo-Bool P? Q? ¬[∃P×∃Q] =
  Sum.map (contraposition (∃P⇒∃eq P?)) (contraposition (∃P⇒∃eq Q?)) $
          llpo-Bool (toBool P?) (toBool Q?)
            (contraposition (Prod.map (∃eq⇒∃P P?) (∃eq⇒∃P Q?)) ¬[∃P×∃Q])

-- MP⊎ <=> MP⊎-Bool
mp⊎⇒mp⊎-Bool : ∀ {a p} {A : Set a} → MP⊎ A p → MP⊎-Bool A
mp⊎⇒mp⊎-Bool {a} {p} mp⊎ P Q ¬[¬∃Peq×¬∃Qeq] =
  Sum.map
    (DN-map lift-injective′) (DN-map lift-injective′) $ mp⊎
      (toBool-Lift p P) (toBool-Lift p Q) (contraposition (λ {(u , v) →
      contraposition lift-cong′ u , contraposition lift-cong′ v}) ¬[¬∃Peq×¬∃Qeq])

mp⊎-Bool⇒mp⊎ : ∀ {a} p {A : Set a} → MP⊎-Bool A → MP⊎ A p
mp⊎-Bool⇒mp⊎ p mp⊎-Bool P? Q? ¬[¬∃P×¬Q] =
  Sum.map (DN-map (∃eq⇒∃P P?)) (DN-map (∃eq⇒∃P Q?)) $
          mp⊎-Bool (toBool P?) (toBool Q?) (contraposition (Prod.map
            (contraposition (∃P⇒∃eq P?)) (contraposition (∃P⇒∃eq Q?))) ¬[¬∃P×¬Q])

-- LPO-Bool <=> LPO-Bool-Alt
private
  not-injective : ∀ {x y} → not x ≡ not y → x ≡ y
  not-injective {false} {false} refl = refl
  not-injective {false} {true} ()
  not-injective {true} {false} ()
  not-injective {true} {true} refl = refl

  x≡false⇒x≢true : ∀ {x} → x ≡ false → x ≢ true
  x≡false⇒x≢true {false} refl ()

  not[x]≢true⇒x≡true : ∀ {x} → not x ≢ true → x ≡ true
  not[x]≢true⇒x≡true {false} neq = ⊥-elim $ neq refl
  not[x]≢true⇒x≡true {true}  _   = refl

  not[x]≡true→x≢true : ∀ {x} → not x ≡ true → x ≢ true
  not[x]≡true→x≢true notx≡true = x≡false⇒x≢true (not-injective notx≡true)

  x≢true⇒x≡false : ∀ {x} → x ≢ true → x ≡ false
  x≢true⇒x≡false {false} neq = refl
  x≢true⇒x≡false {true } neq = ⊥-elim $ neq refl

lpo-Bool⇒lpo-Bool-Alt : ∀ {a} {A : Set a} → LPO-Bool A → LPO-Bool-Alt A
lpo-Bool⇒lpo-Bool-Alt lpo-Bool P =
  Sum.map (Prod.map₂ not-injective)
          (λ ¬∃notPx≡true x → not[x]≢true⇒x≡true $ ¬∃P→∀¬P ¬∃notPx≡true x) $
            lpo-Bool (not ∘ P)

lpo-Bool-Alt⇒lpo-Bool : ∀ {a} {A : Set a} → LPO-Bool-Alt A → LPO-Bool A
lpo-Bool-Alt⇒lpo-Bool lpo-Bool-Alt P =
  Sum.map (Prod.map₂ not-injective)
          (λ ∀x→notPx≡true → ∀¬P→¬∃P λ x → not[x]≡true→x≢true $ ∀x→notPx≡true x) $
            lpo-Bool-Alt (not ∘ P)
