------------------------------------------------------------------------
-- Equivalence between omniscience principles
------------------------------------------------------------------------

-- http://math.fau.edu/lubarsky/Separating%20LLPO.pdf
-- https://pdfs.semanticscholar.org/deb5/23b6078032c845d8041ee6a5383fec41191c.pdf
-- http://www.math.lmu.de/~schwicht/pc16transparencies/ishihara/lecture1.pdf
-- https://ncatlab.org/nlab/show/weak+excluded+middle

------------------------------------------------------------------------
-- ->  : implication
-- <=> : equivalence
-- ∧   : conjunction

{-
         EM <=> DNE <=> Peirce <=> MI <=> DEM₁ <=> DEM₂-----┐
          |      |        |                         |       v
          |      |        v                         v     EM⁻¹ <=> DNE⁻¹
          |      |       DGP          ¬ ¬ EM  <=>  DNS
          |      |        |
          |      |        v
          |      |       WEM <=> DEM₃ <=> DN-distrib-⊎
          v      v
         LPO     KS-------------┐
         /  \                   \
        /    \                   \
       v      v                   v
       MP    WLPO <=> Σ-Π-DGP -> PFP -> WPFP
       | \    |
       |  \   v
       |   \  LLPO <=> Σ-DGP <=> Π-DGP
       |    | |
       v    v v
      WMP   MP∨
-}

-- WLPO ∧ MP -> LPO
-- WLPO ∧ WMP -> LPO

-- WMP ∧ MP∨ -> MP
-- WPFP ∧ MP -> LPO

-- WPFP ∧ MP∨ -> WLPO
-- WPFP ∧ LLPO -> WLPO

-- TODO
-- WLPO => MP∨

------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Constructive.Axiom.Properties.Base where

-- agda-stdlib
open import Axiom.Extensionality.Propositional
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Bool using (Bool; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; s≤s; z≤n; _≤?_)
import Data.Nat.Properties as ℕₚ
import Data.Nat.Induction as ℕInd
open import Data.Fin using (Fin)
import Data.Fin.Properties as Finₚ
open import Function.Base
import Function.Equality as Eq
import Function.Equivalence as Eqv
import Function.LeftInverse as LInv -- TODO use new packages
import Induction.WellFounded as Ind
open import Relation.Binary
  using (tri≈; tri<; tri>; Rel; Trichotomous)
open import Relation.Binary.PropositionalEquality hiding (Extensionality) -- TODO remove
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- agda-misc
open import Constructive.Axiom
open import Constructive.Combinators
open import Constructive.Common

-- Properties
aclt : ∀ {a b p} {A : Set a} {B : Set b} → ACLT A B p
aclt f = (λ x → proj₁ (f x)) , (λ x → proj₂ (f x))

lower-dne : ∀ a b → DNE (a ⊔ b) → DNE a
lower-dne a b dne = lower ∘′ dne ∘′ DN-map (lift {ℓ = b})

lower-wem : ∀ a b → WEM (a ⊔ b) → WEM a
lower-wem a b wem with wem
... | inj₁ ¬Lx  = inj₁ λ x → ¬Lx (lift {ℓ = b} x)
... | inj₂ ¬¬Lx = inj₂ λ ¬A → ¬¬Lx λ LA → ¬A (lower LA)

-- LPO for finite set
lpo-Fin : ∀ {n p} → LPO (Fin n) p
lpo-Fin = dec⇒dec⊎ ∘ Finₚ.any? ∘ DecU⇒decidable

dec-dns-i : ∀ {a p} {A : Set a} {P : A → Set p} → DecU P → DNS-i P
dec-dns-i P? ∀¬¬P = DN-intro (P?⇒∀¬¬P→∀P P? ∀¬¬P)

------------------------------------------------------------------------
-- Equivalence between classical proposition
------------------------------------------------------------------------

-- DNE <=> EM
dne⇒em : ∀ {a} → DNE a → EM a
dne⇒em dne = dne DN-Dec⊎

em⇒dne : ∀ {a} → EM a → DNE a
em⇒dne em = A⊎B→¬B→A em

-- Peirce => DNE, EM => Peirce
peirce⇒dne : ∀ {a b} → Peirce a b → DNE a
peirce⇒dne peirce ¬¬A =
  peirce {B = Lift _ ⊥} λ A→B → ⊥-elim (¬¬A λ x → lower $ A→B x)

em⇒peirce : ∀ {a b} → EM a → Peirce a b
em⇒peirce em f with em
... | inj₁ x  = x
... | inj₂ ¬A = f λ x → ⊥-elim (¬A x)

-- DEM₁ => EM, DNE => DEM₁
dem₁⇒em : ∀ {a} → DEM₁ a a → EM a
dem₁⇒em dem₁ = dem₁ (uncurry (flip _$_))

dne⇒dem₁ : ∀ {a b} → DNE (a ⊔ b) → DEM₁ a b
dne⇒dem₁ dne g = dne (g ∘ ¬[A⊎B]→¬A×¬B)

-- DNE <=> DEM₂
dne⇒dem₂ : ∀ {a} → DNE a → DEM₂ a a
dne⇒dem₂ dne f = Prod.map dne dne $ ¬[A⊎B]→¬A×¬B f

dem₂⇒dne : ∀ {a} → DEM₂ a lzero → DNE a
dem₂⇒dne dem₂ ¬¬A = uncurry id (dem₂ Sum.[ (λ f → ¬¬A (f ∘′ const)) , _$ tt ])

-- DNE => DEM₃
dne⇒dem₃ : ∀ {a} → DNE a → DEM₃ a a
dne⇒dem₃ dne ¬[A×B] = dne (¬[A×B]→¬¬[¬A⊎¬B] ¬[A×B])

-- Properties of WEM
em⇒wem : ∀ {a} → EM a → WEM a
em⇒wem em with em
... | inj₁ ¬A  = inj₁ ¬A
... | inj₂ ¬¬A = inj₂ ¬¬A

-- WEM <=> DEM₃
wem⇒dem₃ : ∀ {a} → WEM a → DEM₃ a a
wem⇒dem₃ wem ¬[A×B] with wem | wem
... | inj₁ ¬A  | _        = inj₁ ¬A
... | inj₂ ¬¬A | inj₁ ¬B  = inj₂ ¬B
... | inj₂ ¬¬A | inj₂ ¬¬B = ⊥-elim $ DN-undistrib-× (¬¬A , ¬¬B) ¬[A×B]

dem₃⇒wem : ∀ {a} → DEM₃ a a → WEM a
dem₃⇒wem dem₃ = dem₃ ¬[A×¬A]

-- WEM <=> DN-distrib-⊎
wem⇒DN-distrib-⊎ : ∀ {a b} → WEM (a ⊔ b) →
                   {A : Set a} {B : Set b} → ¬ ¬ (A ⊎ B) → ¬ ¬ A ⊎ ¬ ¬ B
wem⇒DN-distrib-⊎ {a} {b} wem ¬¬[A⊎B] with lower-wem a b wem | lower-wem b a wem
... | inj₁ ¬A  | inj₁ ¬B  = ⊥-elim $ ¬¬[A⊎B] (¬A×¬B→¬[A⊎B] (¬A , ¬B))
... | inj₁ ¬A  | inj₂ ¬¬B = inj₂ ¬¬B
... | inj₂ ¬¬A | _        = inj₁ ¬¬A

DN-distrib-⊎⇒wem : ∀ {a} → ({A B : Set a} → ¬ ¬ (A ⊎ B) → ¬ ¬ A ⊎ ¬ ¬ B) → WEM a
DN-distrib-⊎⇒wem DN-distrib-⊎ = Sum.swap $ Sum.map₂ TN-to-N $ DN-distrib-⊎ DN-Dec⊎

-- WEM-i ∧ Stable => Dec
wem-i∧stable⇒dec : ∀ {a} {A : Set a} → WEM-i A → Stable A → Dec A
wem-i∧stable⇒dec (inj₁ x) stable = no x
wem-i∧stable⇒dec (inj₂ y) stable = yes (stable y)

-- Converse of contraposition
dne⇒contraposition-converse : ∀ {a b} → DNE a →
                              {A : Set a} {B : Set b} → (¬ A → ¬ B) → B → A
dne⇒contraposition-converse dne ¬A→¬B b = dne $ contraposition ¬A→¬B (DN-intro b)

contraposition-converse⇒dne : ∀ {a} → ({A B : Set a} → (¬ A → ¬ B) → B → A) →
                              DNE a
contraposition-converse⇒dne f = f DN-intro

-- MI <=> EM
mi⇒em : ∀ {a} → MI a a → EM a
mi⇒em f = Sum.swap $ f id

em⇒mi : ∀ {a} → EM a → MI a a
em⇒mi em f = Sum.swap $ Sum.map₁ f em

-- EM <=> [¬A→B]→A⊎B
em⇒[¬A→B]→A⊎B : ∀ {a b} → EM a → {A : Set a} {B : Set b} → (¬ A → B) → A ⊎ B
em⇒[¬A→B]→A⊎B em f = Sum.map₂ f em

[¬A→B]→A⊎B⇒em : ∀ {a} → ({A B : Set a} → (¬ A → B) → A ⊎ B) → EM a
[¬A→B]→A⊎B⇒em f = f id

-- EM => DGP => WEM
em⇒dgp : ∀ {a} → EM a → DGP a a
em⇒dgp em = em⇒[¬A→B]→A⊎B em λ ¬[A→B] b → ⊥-elim $ ¬[A→B] (const b)

dgp⇒dem₃ : ∀ {a b} → DGP a b → DEM₃ a b
dgp⇒dem₃ dgp ¬[A×B] with dgp
... | inj₁ A→B = inj₁ (contraposition (λ x → x , A→B x) ¬[A×B])
... | inj₂ B→A = inj₂ (contraposition (λ y → B→A y , y) ¬[A×B])

dgp⇒wem : ∀ {a} → DGP a a → WEM a
dgp⇒wem dgp = dem₃⇒wem $ dgp⇒dem₃ dgp

-- Properties of DNS
-- DNE => DNS
dne⇒dns : ∀ {a b} → DNE (a ⊔ b) → DNS a (a ⊔ b)
dne⇒dns dne f = dne λ x → x λ y → y λ z → dne (f z)

-- DNS <=> ¬ ¬ EM
dns⇒¬¬em : ∀ {a} → DNS (lsuc a) a → ¬ ¬ EM a
dns⇒¬¬em dns = DN-map (λ x {A} → x A) $ dns λ x → DN-Dec⊎

¬¬em⇒dns : ∀ {a} → ¬ ¬ EM a → DNS a a
¬¬em⇒dns ¬¬em =
  λ ∀x→¬¬Px ¬[∀x→Px] → ¬¬em λ em → ¬[∀x→Px] (λ x → (em⇒dne em) (∀x→¬¬Px x))

-- other properties
[¬A→A]→A⇒dne : ∀ {a} → ({A : Set a} → (¬ A → A) → A) → DNE a
[¬A→A]→A⇒dne f ¬¬A = f λ ¬A → ⊥-elim (¬¬A ¬A)

em⇒[¬A→A]→A : ∀ {a} → EM a → {A : Set a} → (¬ A → A) → A
em⇒[¬A→A]→A em f = Sum.[ id , f ] em

-- DNE <=> ¬[A×¬B]→A→B
dne⇒¬[A×¬B]→A→B : ∀ {a b} → DNE (a ⊔ b) →
                  {A : Set a} {B : Set b} → ¬ (A × ¬ B) → A → B
dne⇒¬[A×¬B]→A→B dne = dne λ x → x λ y z → ⊥-elim (y (z , (λ w → x λ u v → w)))

¬[A×¬B]→A→B⇒dne : ∀ {a} → ({A B : Set a} → ¬ (A × ¬ B) → A → B) → DNE a
¬[A×¬B]→A→B⇒dne f ¬¬A = f (uncurry id) ¬¬A

-- EM <=> [A→B]→¬A⊎B
em⇒[A→B]→¬A⊎B : ∀ {a b} → EM b → {A : Set a} {B : Set b} → (A → B) → ¬ A ⊎ B
em⇒[A→B]→¬A⊎B em f with em
... | inj₁ y  = inj₂ y
... | inj₂ ¬B = inj₁ (contraposition f ¬B)

[A→B]→¬A⊎B⇒em : ∀ {a} → ({A B : Set a} → (A → B) → ¬ A ⊎ B) → EM a
[A→B]→¬A⊎B⇒em f = Sum.swap (f id)

dne⇒¬[A→¬B]→A×B : ∀ {a b} → DNE (a ⊔ b) →
                  {A : Set a} {B : Set b} → ¬ (A → ¬ B) → A × B
dne⇒¬[A→¬B]→A×B dne f = dne λ ¬[A×B] → f λ x y → ¬[A×B] (x , y)

-- the counterexample principle
dne⇒¬[A→B]→A×¬B : ∀ {a b} → DNE (a ⊔ b) →
                  {A B : Set a} {B : Set b} → ¬ (A → B) → A × ¬ B
dne⇒¬[A→B]→A×¬B dne f =
  dne λ ¬[A×¬B] → f λ x → ⊥-elim (¬[A×¬B] (x , (λ y → f (const y))))

¬[A→B]→A×¬B⇒dne : ∀ {a} → ({A B : Set a} → ¬ (A → B) → A × ¬ B) → DNE a
¬[A→B]→A×¬B⇒dne {a} f ¬¬A with f {B = Lift a ⊥} λ A→L⊥ → ¬¬A λ x → lower $ A→L⊥ x
... | x , _ = x

dne⇒ip : ∀ {a b c} → DNE (a ⊔ b ⊔ c) → IP a b c
dne⇒ip dne q f = dne (DN-ip q f)

-- Properties of DNE⁻¹ and EM⁻¹
em⇒em⁻¹ : ∀ {a} → EM a → EM⁻¹ a
em⇒em⁻¹ em _ = em

-- DNE⁻¹ <=> EM⁻¹
dne⁻¹⇒em⁻¹ : ∀ {a} → Extensionality a lzero → DNE⁻¹ a → EM⁻¹ a
dne⁻¹⇒em⁻¹ ext dne⁻¹ isP = dne⁻¹ isP′ DN-Dec⊎ where
  isP′ : ∀ x y → x ≡ y
  isP′ (inj₁  x) (inj₁  y) = cong inj₁ (isP x y)
  isP′ (inj₁  x) (inj₂ ¬y) = ⊥-elim $ ¬y x
  isP′ (inj₂ ¬x) (inj₁  y) = ⊥-elim $ ¬x y
  isP′ (inj₂ ¬x) (inj₂ ¬y) = cong inj₂ (ext λ x → ⊥-elim $ ¬x x)

em⁻¹⇒dne⁻¹ : ∀ {a} → EM⁻¹ a → DNE⁻¹ a
em⁻¹⇒dne⁻¹ em⁻¹ isP ¬¬x with em⁻¹ isP
... | inj₁  x = x
... | inj₂ ¬x = ⊥-elim $ ¬¬x ¬x

-----------------------------------------------------------------------
-- Properties of LPO, LLPO, WLPO, MP, MP⊎, WMP, KS, PFP, WPFP, Σ-DGP,
--   Π-DGP, Σ-Π-DGP
-----------------------------------------------------------------------

-- EM => LPO
em⇒lpo : ∀ {a p} {A : Set a} → EM (a ⊔ p) → LPO A p
em⇒lpo em _ = em

-- LPO => LLPO
lpo⇒llpo : ∀ {a p} {A : Set a} → LPO A p → LLPO A p
lpo⇒llpo lpo P? Q? ¬[∃P×∃Q] with lpo P? | lpo Q?
... | inj₁ ∃P  | inj₁ ∃Q  = ⊥-elim $ ¬[∃P×∃Q] (∃P , ∃Q)
... | inj₁ ∃P  | inj₂ ¬∃Q = inj₂ ¬∃Q
... | inj₂ ¬∃P | _        = inj₁ ¬∃P

-- LPO <=> WLPO ∧ MP
lpo⇒wlpo : ∀ {a p} {A : Set a} → LPO A p → WLPO A p
lpo⇒wlpo lpo P? with lpo (¬-DecU P?)
... | inj₁ ∃¬P  = inj₂ (∃¬P→¬∀P ∃¬P)
... | inj₂ ¬∃¬P = inj₁ (P?⇒¬∃¬P→∀P P? ¬∃¬P)

lpo⇒mp : ∀ {a p} {A : Set a} → LPO A p → MP A p
lpo⇒mp lpo P? ¬∀P with lpo (¬-DecU P?)
... | inj₁ ∃¬P  = ∃¬P
... | inj₂ ¬∃¬P = ⊥-elim $ ¬∀P $ P?⇒¬∃¬P→∀P P? ¬∃¬P

wlpo∧mp⇒lpo : ∀ {a p} {A : Set a} → WLPO A p → MP A p → LPO A p
wlpo∧mp⇒lpo wlpo mp P? with wlpo (¬-DecU P?)
... | inj₁ ∀¬P  = inj₂ (∀¬P→¬∃P ∀¬P)
... | inj₂ ¬∀¬P = inj₁ $ P?⇒∃¬¬P→∃P P? $ mp (¬-DecU P?) ¬∀¬P

-- WLPO => LLPO
wlpo⇒llpo : ∀ {a p} {A : Set a} → WLPO A p → LLPO A p
wlpo⇒llpo wlpo P? Q? ¬[∃P×∃Q] with wlpo (¬-DecU P?) | wlpo (¬-DecU Q?)
... | inj₁ ∀¬P  | _         = inj₁ (∀¬P→¬∃P ∀¬P)
... | inj₂ ¬∀¬P | inj₁ ∀¬Q  = inj₂ (∀¬P→¬∃P ∀¬Q)
... | inj₂ ¬∀¬P | inj₂ ¬∀¬Q = ⊥-elim $ ¬∀¬P×¬∀¬Q→¬¬[∃P×∃Q] (¬∀¬P , ¬∀¬Q) ¬[∃P×∃Q]

-- WEM => WLPO
wem⇒wlpo : ∀ {a p} {A : Set a} → WEM (a ⊔ p) → WLPO A p
wem⇒wlpo wem P? with wem
... | inj₁ ¬∀P  = inj₂ ¬∀P
... | inj₂ ¬¬∀P = inj₁ (P?⇒¬¬∀P→∀P P? ¬¬∀P)

-- WLPO <=> WLPO-Alt
wlpo⇒wlpo-Alt : ∀ {a p} {A : Set a} → WLPO A p → WLPO-Alt A p
wlpo⇒wlpo-Alt wlpo P? = Sum.map ∀¬P→¬∃P ¬∀¬P→¬¬∃P (wlpo (¬-DecU P?))

wlpo-Alt⇒wlpo : ∀ {a p} {A : Set a} → WLPO-Alt A p → WLPO A p
wlpo-Alt⇒wlpo wlpo-Alt P? =
  Sum.map (P?⇒¬∃¬P→∀P P?) ¬¬∃¬P→¬∀P (wlpo-Alt (¬-DecU P?))

-- MP <=> MR
mp⇒mr : ∀ {a p} {A : Set a} → MP A p → MR A p
mp⇒mr mp P? ¬¬∃P = P?⇒∃¬¬P→∃P P? $ mp (¬-DecU P?) (¬¬∃P→¬∀¬P ¬¬∃P)

mr⇒mp : ∀ {a p} {A : Set a} → MR A p → MP A p
mr⇒mp mr P? ¬∀P = mr (¬-DecU P?) (P?⇒¬∀P→¬¬∃¬P P? ¬∀P)

-- (WMP ∧ MP∨) <=> MP
mr⇒wmp : ∀ {a p} {A : Set a} → MR A p → WMP A p
mr⇒wmp mr {P = P} P? pp =
  mr P? $ Sum.[ id , (λ ¬¬∃x→Px×¬Px _ → f ¬¬∃x→Px×¬Px) ] (pp P?)
  where
  f : ¬ ¬ ∃ (λ x → P x × ¬ P x) → ⊥
  f ¬¬∃x→Px×¬Px = ⊥-stable $ DN-map (¬[A×¬A] ∘ proj₂) ¬¬∃x→Px×¬Px

-- MR => MP∨
mr⇒mp∨ : ∀ {a p} {A : Set a} → MR A p → MP∨ A p
mr⇒mp∨ mr {P = P} {Q = Q} P? Q? ¬¬∃x→Px⊎Qx with
  mr {P = λ x → P x ⊎ Q x} (DecU-⊎ P? Q?) ¬¬∃x→Px⊎Qx
... | x , Px⊎Qx = Sum.map (DN-intro ∘′ (x ,_)) (DN-intro ∘′ (x ,_)) Px⊎Qx

-- WMP ∧ MP∨ => MR
-- α = P, β = Q, γ = R in [2]
wmp∧mp∨⇒mr : ∀ {a p} {A : Set a} → WMP A p → MP∨ A p → MR A p
wmp∧mp∨⇒mr {a} {p} {A} wmp mp∨ {P = P} P? ¬¬∃P = wmp P? Lem.¬¬∃Q⊎¬¬∃R
  where
  module Lem {Q : A → Set p} (Q? : DecU Q) where
    R : A → Set p
    R x = P x × ¬ Q x

    ¬¬∃x→Qx⊎Rx : ¬ ¬ ∃ λ x → Q x ⊎ R x
    ¬¬∃x→Qx⊎Rx = DN-map f ¬¬∃P
      where
      f : ∃ P → ∃ (λ x → Q x ⊎ (P x × ¬ Q x))
      f (x , Px) = x , Sum.map₂ (Px ,_) (Q? x)

    R? : DecU R
    R? = DecU-× P? (¬-DecU Q?)

    ¬¬∃Q⊎¬¬∃R : ¬ ¬ ∃ Q ⊎ ¬ ¬ ∃ R
    ¬¬∃Q⊎¬¬∃R = mp∨ Q? R? ¬¬∃x→Qx⊎Rx

-- MP⊎ <=> MP⊎-Alt
mp⊎⇒mp⊎-Alt : ∀ {a p} {A : Set a} → MP⊎ A p → MP⊎-Alt A p
mp⊎⇒mp⊎-Alt mp⊎ P? Q? =
  Sum.map (contraposition ∀P→¬∃¬P) (contraposition ∀P→¬∃¬P) ∘′
  mp⊎ (¬-DecU P?) (¬-DecU Q?) ∘′
  contraposition (Prod.map (P?⇒¬∃¬P→∀P P?) (P?⇒¬∃¬P→∀P Q?))

mp⊎-Alt⇒mp⊎ : ∀ {a p} {A : Set a} → MP⊎-Alt A p → MP⊎ A p
mp⊎-Alt⇒mp⊎ mp⊎-Alt P? Q? =
  Sum.map (contraposition ¬∃P→∀¬P) (contraposition ¬∃P→∀¬P) ∘′
  mp⊎-Alt (¬-DecU P?) (¬-DecU Q?) ∘′
  contraposition (Prod.map ∀¬P→¬∃P ∀¬P→¬∃P)

-- MP⊎ <=> MP∨
mp⊎⇒mp∨ : ∀ {a p} {A : Set a} → MP⊎ A p → MP∨ A p
mp⊎⇒mp∨ mp⊎ P? Q? ¬¬∃x→Px⊎Qx = mp⊎ P? Q? ([¬¬∃x→Px⊎Qx]→¬[¬∃P×¬∃Q] ¬¬∃x→Px⊎Qx)

mp∨⇒mp⊎ : ∀ {a p} {A : Set a} → MP∨ A p → MP⊎ A p
mp∨⇒mp⊎ mp∨ P? Q? ¬[¬∃P×¬∃Q] = mp∨ P? Q? (¬[¬∃P×¬∃Q]→¬¬∃x→Px⊎Qx ¬[¬∃P×¬∃Q])

record HasProperties
  {a} r p (A : Set a) : Set (a ⊔ lsuc r ⊔ lsuc p)
  where
  field
    _<_       : Rel A r
    <-cmp     : Trichotomous _≡_ _<_
    <-any-dec : {P : A → Set p} → DecU P → DecU (λ n → ∃ λ m → (m < n) × P m)
    <-wf      : Ind.WellFounded _<_

  private
    ¬∃¬→∀ : ∀ {P : A → Set p} {x} →
            DecU P → ¬ (∃ λ y → y < x × ¬ P y) → ∀ y → y < x → P y
    ¬∃¬→∀ {x} P? ¬∃y→y<x×¬Py y y<x =
      DecU⇒stable P? y λ ¬Py → ¬∃y→y<x×¬Py (y , (y<x , ¬Py))

  <-all-dec : {P : A → Set p} → DecU P → DecU (λ n → ∀ i → i < n → P i)
  <-all-dec P? n with <-any-dec (¬-DecU P?) n
  ... | inj₁ (m , m<n , ¬Pm) = inj₂ λ ∀i→i<n→Pi → ¬Pm (∀i→i<n→Pi m m<n)
  ... | inj₂ ¬∃m→m<n×¬Pm     = inj₁ (¬∃¬→∀ P? ¬∃m→m<n×¬Pm)

  findFirst : {P : A → Set p} →
              DecU P → ∃ P → ∃ λ x → (∀ y → y < x → ¬ P y) × P x
  findFirst {P} P? (x , Px) = go x (<-wf x) Px
    where
    go : ∀ x → Ind.Acc _<_ x → P x → ∃ λ y → (∀ i → i < y → ¬ P i) × P y
    go x (Ind.acc rs) Px with <-any-dec P? x
    ... | inj₁ (y , y<x , Py) = go y (rs y y<x) Py
    ... | inj₂ ¬∃y→y<x×Py     =
      x , (λ i i<x Pi → ¬∃y→y<x×Py (i , (i<x , Pi))) , Px

  module HasPropertiesLemma
    {P : A → Set p} {Q : A → Set p} (P? : DecU P) (Q? : DecU Q)
    where
    -- ex. R 5
    -- n : 0 1 2 3 4 5 6 7 8
    -- P : 0 0 0 0 0 1 ? ? ?
    -- Q : 0 0 0 0 0 0 ? ? ?
    R S : A → Set (r ⊔ p ⊔ a)
    R n = (∀ i → i < n → ¬ P i × ¬ Q i) × P n × ¬ Q n
    S n = (∀ i → i < n → ¬ P i × ¬ Q i) × ¬ P n × Q n

    private
      lem : DecU (λ n → ∀ i → i < n → ¬ P i × ¬ Q i)
      lem = <-all-dec (DecU-× (¬-DecU P?) (¬-DecU Q?))

    R? : DecU R
    R? = DecU-× lem (DecU-× P? (¬-DecU Q?))

    S? : DecU S
    S? = DecU-× lem (DecU-× (¬-DecU P?) Q?)

    ¬[∃R×∃S] : ¬ (∃ R × ∃ S)
    ¬[∃R×∃S] ((m , ∀i→i<m→¬Pi×¬Qi , Pm  , ¬Qm) ,
              (n , ∀i→i<n→¬Pi×¬Qi , ¬Pn , Qn)) with <-cmp m n
    ... | tri< m<n _ _ = proj₁ (∀i→i<n→¬Pi×¬Qi m m<n) Pm
    ... | tri≈ _ m≡n _ = ¬Pn (subst P m≡n Pm)
    ... | tri> _ _ n<m = proj₂ (∀i→i<m→¬Pi×¬Qi n n<m) Qn

    ¬∃R→∃P→∃Q : ¬ ∃ R → ∃ P → ∃ Q
    ¬∃R→∃P→∃Q ¬∃R ∃P with findFirst P? ∃P
    ... | (x , ∀y→y<x→¬Px , Px) with Q? x
    ¬∃R→∃P→∃Q ¬∃R _ | x , ∀y→y<x→¬Px , Px | inj₁  Qx = x , Qx
    ¬∃R→∃P→∃Q ¬∃R _ | x , ∀y→y<x→¬Px , Px | inj₂ ¬Qx with <-any-dec Q? x
    ¬∃R→∃P→∃Q ¬∃R _ | x , ∀y→y<x→¬Px , Px | inj₂ ¬Qx | inj₁ (y , _ , Qy) = y , Qy
    ¬∃R→∃P→∃Q ¬∃R _ | x , ∀y→y<x→¬Px , Px | inj₂ ¬Qx | inj₂ ¬∃           =
      ⊥-elim $ ¬∃R (x , ((λ i i<x → ∀y→y<x→¬Px i i<x ,
                   (λ Qi → ¬∃ (i , i<x , Qi))) , (Px , ¬Qx)))

    ¬∃S→∃Q→∃P : ¬ ∃ S → ∃ Q → ∃ P
    ¬∃S→∃Q→∃P ¬∃S ∃Q with findFirst Q? ∃Q
    ... | (x , ∀y→y<x→¬Qx , Qx) with P? x
    ¬∃S→∃Q→∃P ¬∃S _ | x , ∀y→y<x→¬Qx , Qx | inj₁  Px = x , Px
    ¬∃S→∃Q→∃P ¬∃S _ | x , ∀y→y<x→¬Qx , Qx | inj₂ ¬Px with <-any-dec P? x
    ¬∃S→∃Q→∃P ¬∃S _ | x , ∀y→y<x→¬Qx , Qx | inj₂ ¬Px | inj₁ (y , _ , Py) = y , Py
    ¬∃S→∃Q→∃P ¬∃S _ | x , ∀y→y<x→¬Qx , Qx | inj₂ ¬Px | inj₂ ¬∃           =
      ⊥-elim $ ¬∃S (x , (λ i i<x →
                   (λ Pi → ¬∃ (i , i<x , Pi)) , ∀y→y<x→¬Qx i i<x) , (¬Px , Qx))

-- Proposition 8.6.1. [1]
-- Σ-DGP <=> LLPO
Σ-dgp⇒llpo : ∀ {a p} {A : Set a} → Σ-DGP A p → LLPO A p
Σ-dgp⇒llpo Σ-dgp P? Q? ¬[∃P×∃Q] =
  Sum.map (λ ∃P→∃Q ∃P → ¬[∃P×∃Q] (∃P , ∃P→∃Q ∃P))
          (λ ∃Q→∃P ∃Q → ¬[∃P×∃Q] (∃Q→∃P ∃Q , ∃Q))
          (Σ-dgp P? Q?)

llpo⇒Σ-dgp : ∀ {r p a} {A : Set a} → HasProperties r p A →
             LLPO A (p ⊔ a ⊔ r) → Σ-DGP A p
llpo⇒Σ-dgp {r} {p} {a} {A = A} has llpo {P = P} {Q} P? Q? =
  Sum.map ¬∃R→∃P→∃Q ¬∃S→∃Q→∃P ¬∃R⊎¬∃S
  where
  open HasProperties has
  open HasPropertiesLemma P? Q?

  ¬∃R⊎¬∃S : ¬ ∃ R ⊎ ¬ ∃ S
  ¬∃R⊎¬∃S = llpo R? S? ¬[∃R×∃S]

-- Σ-DGP => MP∨
Σ-dgp⇒mp∨ : ∀ {p a} {A : Set a} → Σ-DGP A p → MP∨ A p
Σ-dgp⇒mp∨ Σ-dgp {P = P} {Q} P? Q? ¬¬[∃x→Px⊎Qx] = ¬¬∃P⊎¬¬∃Q
  where
  ¬¬[∃P⊎∃Q] : ¬ ¬ (∃ P ⊎ ∃ Q)
  ¬¬[∃P⊎∃Q] = DN-map ∃-distrib-⊎ ¬¬[∃x→Px⊎Qx]

  ¬¬∃P⊎¬¬∃Q : ¬ ¬ ∃ P ⊎ ¬ ¬ ∃ Q
  ¬¬∃P⊎¬¬∃Q =
    Sum.map (λ ∃Q→∃P ¬∃P → ¬¬[∃P⊎∃Q] Sum.[ ¬∃P , (λ ∃Q → ¬∃P (∃Q→∃P ∃Q)) ])
            (λ ∃P→∃Q ¬∃Q → ¬¬[∃P⊎∃Q] Sum.[ (λ ∃P → ¬∃Q (∃P→∃Q ∃P)) , ¬∃Q ])
            (Σ-dgp Q? P?)

-- Σ-DGP => Π-DGP
Σ-dgp⇒Π-dgp : ∀ {p a} {A : Set a} → Σ-DGP A p → Π-DGP A p
Σ-dgp⇒Π-dgp Σ-dgp P? Q? =
  Sum.map (P?⇒[∃¬P→∃¬Q]→∀Q→∀P Q?) (P?⇒[∃¬P→∃¬Q]→∀Q→∀P P?)
          (Σ-dgp (¬-DecU Q?) (¬-DecU P?))

-- Π-DGP => LLPO
Π-dgp⇒llpo : ∀ {a p} {A : Set a} → Π-DGP A p → LLPO A p
Π-dgp⇒llpo Π-dgp P? Q? ¬[∃P×∃Q] =
  Sum.map (λ ∀¬Q→∀¬P ∃P → [∀¬P→∀¬Q]→¬¬[∃Q→∃P] ∀¬Q→∀¬P
             λ ∃P→∃Q → ¬[∃P×∃Q] (∃P , ∃P→∃Q ∃P))
          (λ ∀¬P→∀¬Q ∃Q → [∀¬P→∀¬Q]→¬¬[∃Q→∃P] ∀¬P→∀¬Q
             λ ∃Q→∃P → ¬[∃P×∃Q] (∃Q→∃P ∃Q , ∃Q))
          (Π-dgp (¬-DecU Q?) (¬-DecU P?))

-- LLPO => MP∨
llpo⇒mp∨ : ∀ {r p a} {A : Set a} →
           HasProperties r p A → LLPO A (p ⊔ a ⊔ r) → MP∨ A p
llpo⇒mp∨ has llpo = Σ-dgp⇒mp∨ (llpo⇒Σ-dgp has llpo)

-- lemma for `ℕ-llpo⇒mp∨`
private
  1+n≰0 : ∀ n → ¬ (suc n ≤ 0)
  1+n≰0 n ()

  ℕ≤-any-dec : ∀ {p} {P : ℕ → Set p} → DecU P → DecU (λ n → ∃ λ m → m ≤ n × P m)
  ℕ≤-any-dec {P = P} P? zero with P? 0
  ... | inj₁  P0 = inj₁ (0 , ℕₚ.≤-refl , P0)
  ... | inj₂ ¬P0 = inj₂ λ {(m , m≤0 , Pm) → ¬P0 (subst P (ℕₚ.n≤0⇒n≡0 m≤0) Pm)}
  ℕ≤-any-dec P? (suc n) with P? 0
  ... | inj₁  P0 = inj₁ (0 , (z≤n , P0))
  ... | inj₂ ¬P0 with ℕ≤-any-dec (P? ∘ suc) n
  ℕ≤-any-dec {P = P} P? (suc n) | inj₂ ¬P0 | inj₁ (m , m≤n , Psm) =
    inj₁ (suc m , s≤s m≤n , Psm)
  ℕ≤-any-dec {P = P} P? (suc n) | inj₂ ¬P0 | inj₂ ¬∃m→m≤n×Psm =
    inj₂ f
    where
    f : (∃ λ m → m ≤ suc n × P m) → ⊥
    f (zero  , m≤sn  , Pm)  = ¬P0 Pm
    f (suc m , sm≤sn , Psm) = ¬∃m→m≤n×Psm (m , (ℕₚ.≤-pred sm≤sn , Psm))

  ℕ<-any-dec : ∀ {p} {P : ℕ → Set p} → DecU P →
               DecU (λ n → ∃ λ m → m ℕ.< n × P m)
  ℕ<-any-dec P? zero     = inj₂ λ {(m , m<0 , _) → 1+n≰0 m m<0}
  ℕ<-any-dec {P = P} P? (suc n) with ℕ≤-any-dec P? n
  ... | inj₁ (m , m≤n , Pm) = inj₁ (m , s≤s m≤n , Pm)
  ... | inj₂ ¬∃m→m≤n×Pm     = inj₂ (contraposition f ¬∃m→m≤n×Pm)
    where
    f : (∃ λ m → suc m ≤ suc n × P m) → ∃ λ m → m ≤ n × P m
    f (m , sm≤sn , Pm) = m , (ℕₚ.≤-pred sm≤sn , Pm)

ℕ-hasProperties : ∀ p → HasProperties lzero p ℕ
ℕ-hasProperties _ = record
  { _<_       = ℕ._<_
  ; <-cmp     = ℕₚ.<-cmp
  ; <-any-dec = ℕ<-any-dec
  ; <-wf      = ℕInd.<-wellFounded
  }

ℕ-llpo⇒mp∨ : ∀ {p} → LLPO ℕ p → MP∨ ℕ p
ℕ-llpo⇒mp∨ = llpo⇒mp∨ (ℕ-hasProperties _)

ℕ-llpo⇒Σ-dgp : ∀ {p} → LLPO ℕ p → Σ-DGP ℕ p
ℕ-llpo⇒Σ-dgp = llpo⇒Σ-dgp (ℕ-hasProperties _)

-- Proposition 8.6.1. [1]
-- WLPO <=> Σ-Π-DGP
wlpo⇒Σ-Π-dgp : ∀ {a p} {A : Set a} → WLPO A p → Σ-Π-DGP A p
wlpo⇒Σ-Π-dgp wlpo P? Q? with wlpo Q?
... | inj₁  ∀Q = inj₁ λ _ → ∀Q
... | inj₂ ¬∀Q = inj₂ λ ∀Q → ⊥-elim $ ¬∀Q ∀Q

Σ-Π-dgp⇒wlpo : ∀ {a p} {A : Set a} → Σ-Π-DGP A p → WLPO A p
Σ-Π-dgp⇒wlpo Σ-Π-dgp P? with Σ-Π-dgp (¬-DecU P?) P?
... | inj₁ ∃¬P→∀P = inj₁ (P?⇒[∃¬P→∀P]→∀P P? ∃¬P→∀P)
... | inj₂ ∀P→∃¬P = inj₂ λ ∀P → ∃¬P→¬∀P (∀P→∃¬P ∀P) ∀P

-- Proposition 6.4.1. [1]
-- WMP ∧ WLPO-Alt => LPO
wmp∧wlpo-Alt⇒lpo : ∀ {a p} {A : Set a} → WMP A p → WLPO-Alt A p → LPO A p
wmp∧wlpo-Alt⇒lpo             wmp wlpo-Alt         P? with wlpo-Alt P?
wmp∧wlpo-Alt⇒lpo             wmp wlpo-Alt         P? | inj₁ ¬∃P  = inj₂ ¬∃P
wmp∧wlpo-Alt⇒lpo {a} {p} {A} wmp wlpo-Alt {P = P} P? | inj₂ ¬¬∃P =
  inj₁ (wmp P? Lem.res)
  where
  module Lem {Q : A → Set p} (Q? : DecU Q) where
    R : A → Set p
    R x = P x × ¬ Q x

    R? : DecU R
    R? = DecU-× P? (¬-DecU Q?)

    ¬∃R⊎¬¬∃R : ¬ ∃ R ⊎ ¬ ¬ ∃ R
    ¬∃R⊎¬¬∃R = wlpo-Alt R?

    res : ¬ ¬ ∃ Q ⊎ (¬ ¬ ∃ λ x → P x × ¬ Q x)
    res = Sum.map₁ (λ ¬∃R ¬∃Q → ¬¬∃P (f ¬∃R ¬∃Q)) ¬∃R⊎¬¬∃R
      where
      f : ¬ ∃ R → ¬ ∃ Q → ¬ ∃ P
      f ¬∃R ¬∃Q (x , Px) = ¬∃R (x , (Px , ¬∃P→∀¬P ¬∃Q x))

-- EM => KS
em⇒ks : ∀ {a p} q {A : Set a} (x : A) → EM p → KS A p q
em⇒ks q x em P with em {A = P}
em⇒ks q x em P | inj₁ xP =
  (λ _ → Lift q ⊤) , (λ _ → inj₁ (lift tt)) , ((λ _ → x , lift tt) , (λ _ → xP))
em⇒ks q x em P | inj₂ ¬P =
  (λ _ → Lift q ⊥) , (λ _ → inj₂ lower) ,
  ((λ xP → ⊥-elim $ ¬P xP) , (λ A×L⊥ → ⊥-elim $ lower $ proj₂ A×L⊥))

-- KS => PFP
ks⇒pfp : ∀ {a p q} {A : Set a} → KS A (a ⊔ p) q → PFP A p q
ks⇒pfp ks {P = P} P? = ks (∀ x → P x)

-- PFP => WPFP
pfp⇒wpfp : ∀ {a p} {A : Set a} → PFP A p p → WPFP A p p
pfp⇒wpfp pfp {P = P} P? with pfp P?
... | Q , Q? , ∀P→∃Q , ∃Q→∀P = (λ x → ¬ Q x) , (¬-DecU Q? , (f , g))
  where
  f : (∀ x → P x) → ¬ (∀ x → ¬ Q x)
  f ∀P = ∃P→¬∀¬P (∀P→∃Q ∀P)
  g : (¬ (∀ x → ¬ Q x)) → ∀ x → P x
  g = P?⇒[∃Q→∀P]→¬∀¬Q→∀P P? ∃Q→∀P

-- WLPO => PFP
wlpo⇒pfp : ∀ {a p} {A : Set a} → A → WLPO A p → PFP A p p
wlpo⇒pfp {p = p} xA wlpo {P = P} P? with wlpo P?
... | inj₁ ∀P  = (λ _ → Lift p ⊤) , (λ _ → inj₁ (lift tt)) , (f , g)
  where
  f : (∀ x → P x) → ∃ λ x → Lift p ⊤
  f _ = xA , lift tt
  g : (∃ λ x → Lift p ⊤) → (∀ x → P x)
  g _ = ∀P
... | inj₂ ¬∀P = (λ _ → Lift p ⊥) , (λ _ → inj₂ lower) , f , g
  where
  f : (∀ x → P x) → ∃ (λ x → Lift p ⊥)
  f ∀P = ⊥-elim $ ¬∀P ∀P
  g : ∃ (λ x → Lift p ⊥) → ∀ x → P x
  g (x , L⊥) = ⊥-elim $ lower L⊥

-- Proposition 6.2.3 [1]
-- WPFP ∧ MP⊎-Alt => WLPO
-- This can be proved by `wpfp∧llpo⇒wlpo` but it requires `HasPropertiesForLLPO⇒MP∨`
wpfp∧mp⊎-Alt⇒wlpo : ∀ {a p} {A : Set a} → WPFP A p p → MP⊎-Alt A p → WLPO A p
wpfp∧mp⊎-Alt⇒wlpo {a} {p} {A} wpfp mp⊎-Alt {P = P} P? with wpfp P?
... | Q , Q? , ∀P→¬∀Q , ¬∀Q→∀P = Sum.map₁ ¬∀Q→∀P (Sum.swap ¬∀P⊎¬∀Q)
  where
  f : ¬ ((∀ x → P x) × (∀ x → Q x))
  f (∀P , ∀Q) = ∀P→¬∀Q ∀P ∀Q
  ¬∀P⊎¬∀Q : ¬ (∀ x → P x) ⊎ ¬ (∀ x → Q x)
  ¬∀P⊎¬∀Q = mp⊎-Alt P? Q? f

-- WLPO => WPFP
wlpo⇒wpfp : ∀ {a p} {A : Set a} (xA : A) → WLPO A p → WPFP A p p
wlpo⇒wpfp xA wlpo = pfp⇒wpfp (wlpo⇒pfp xA wlpo)

-- WPFP ∧ MP <=> LPO
wpfp∧mp⇒lpo : ∀ {a p} {A : Set a} → WPFP A p p → MP A p → LPO A p
wpfp∧mp⇒lpo wpfp mp =
  wlpo∧mp⇒lpo (wpfp∧mp⊎-Alt⇒wlpo wpfp (mp⊎⇒mp⊎-Alt (mp∨⇒mp⊎ (mr⇒mp∨ (mp⇒mr mp)))))
              mp

-- WPFP ∧ LLPO => WLPO
wpfp∧llpo⇒wlpo : ∀ {a p} {A : Set a} → WPFP A p p → LLPO A p → WLPO A p
wpfp∧llpo⇒wlpo wpfp llpo P? with wpfp P?
wpfp∧llpo⇒wlpo wpfp llpo P? | Q , Q? , ∀P→¬∀Q , ¬∀Q→∀P with
  llpo (¬-DecU P?) (¬-DecU Q?)
       λ {(∃¬P , ∃¬Q) → ∀P→¬∃¬P (¬∀Q→∀P (∃¬P→¬∀P ∃¬Q)) ∃¬P}
wpfp∧llpo⇒wlpo wpfp llpo P? | Q , Q? , ∀P→¬∀Q , ¬∀Q→∀P | inj₁ ¬∃¬P =
  inj₁ (P?⇒¬∃¬P→∀P P? ¬∃¬P)
wpfp∧llpo⇒wlpo wpfp llpo P? | Q , Q? , ∀P→¬∀Q , ¬∀Q→∀P | inj₂ ¬∃¬Q =
  inj₂ λ ∀P → ∀P→¬∀Q ∀P (P?⇒¬∃¬P→∀P Q? ¬∃¬Q)

-- [1] Hannes Diener "Constructive Reverse Mathematics"
-- [2] Hajime lshihara "Markov’s principle, Church’s thesis and LindeUf’s theorem"
