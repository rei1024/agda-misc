{-# OPTIONS --without-K --safe --exact-split #-}

-- http://math.fau.edu/lubarsky/Separating%20LLPO.pdf
-- https://pdfs.semanticscholar.org/deb5/23b6078032c845d8041ee6a5383fec41191c.pdf

-- http://www.math.lmu.de/~schwicht/pc16transparencies/ishihara/lecture1.pdf

module Math.Logic.NonConstructiveAxiom.Properties where

-- agda-stdlib
open import Axiom.Extensionality.Propositional
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Fin hiding (lift)
import Data.Fin.Properties as Finₚ
open import Function.Core
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality hiding (Extensionality) -- TODO remove
import Function.LeftInverse as LInv -- TODO use new packages
import Function.Equality as Eq
import Function.Equivalence as Eqv

-- agda-misc
open import Math.Logic.NonConstructiveAxiom
open import Math.Logic.Constructive

-- Properties
aclt : ∀ {a b p} {A : Set a} {B : Set b} → ACLT A B p
aclt f = (λ x → proj₁ (f x)) , (λ x → proj₂ (f x))

lower-dne : ∀ a b → DNE (a ⊔ b) → DNE a
lower-dne a b dne = lower ∘′ dne ∘′ DN-map (lift {ℓ = b})

lower-wem : ∀ a b → WEM (a ⊔ b) → WEM a
lower-wem a b wem with wem
... | inj₁ ¬Lx  = inj₁ λ x → ¬Lx (lift {ℓ = b} x)
... | inj₂ ¬¬Lx = inj₂ λ ¬A → ¬¬Lx λ LA → ¬A (lower LA)

assume-EM-in-DN : ∀ {a b} {A : Set a} {B : Set b} → (A ⊎ ¬ A → ¬ ¬ B) → ¬ ¬ B
assume-EM-in-DN f = DN-bind f DN-EM-i

assume-DNE-in-DN : ∀ {a b} {A : Set a} {B : Set b} → ((¬ ¬ A → A) → ¬ ¬ B) → ¬ ¬ B
assume-DNE-in-DN f = assume-EM-in-DN λ em → f (A⊎B→¬B→A em)

-- LPO for finite set
lpo-Fin : ∀ {n p} → LPO (Fin n) p
lpo-Fin = dec⇒em-i ∘ Finₚ.any? ∘ DecU⇒decidable

dec-dns-i : ∀ {a p} {A : Set a} {P : A → Set p} → DecU P → DNS-i P
dec-dns-i P? ∀¬¬P ¬∀P = ¬∀P (λ x → DecU⇒stable P? x (∀¬¬P x))

------------------------------------------------------------------------
-- Equivalence between classical proposition

------------------------------------------------------------------------
-- ->  : implication
-- <=> : equivalence
-- +   : and

--     EM⁻¹ <=> DNE⁻¹
--      ^
--      |
--  ┌- EM <=> DNE <=> Peirce <=> MI <=> DEM₁ <=> DEM₂
--  |   |              |         |
--  |   v              v         v
--  |  WEM <=> DEM₃ <- LC       DNS <=> ¬ ¬ EM <=> ¬ ¬ DNE
--   \  \       ||
--    v  \     DN-distrib-⊎
--   LPO  \
--   /  \ |
--  v    vv
-- MP    WLPO
-- | \    |
-- |  \   v
-- |   \  LLPO
-- |    \ |
-- v     vv
-- WMP   MP⊎

-- LPO <=> WLPO + MP
-- MP  <=> WMP + MP⊎

--
-- EM -> LPO
-- WLPO -> WKL
-- WKL -> LLPO
-- LLPO -> MP⊎ -- ?
-- WKL = LLPO

------------------------------------------------------------------------

-- DNE <=> EM
dne⇒em : ∀ {a} → DNE a → EM a
dne⇒em dne = dne DN-EM-i

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

dne⇒dem₁ : ∀ {a} → DNE a → DEM₁ a a
dne⇒dem₁ dne g = dne (g ∘ ¬[A⊎B]→¬A×¬B)

dne⇒dem₁′ : ∀ {a b} → DNE (a ⊔ b) → DEM₁ a b
dne⇒dem₁′ dne g = dne (g ∘ ¬[A⊎B]→¬A×¬B)

-- DNE <=> DEM₂
dne⇒dem₂ : ∀ {a} → DNE a → DEM₂ a a
dne⇒dem₂ dne f = Prod.map dne dne $ ¬[A⊎B]→¬A×¬B f

dem₂⇒dne : ∀ {a} → DEM₂ a lzero → DNE a
dem₂⇒dne dem₂ ¬¬A = uncurry id (dem₂ Sum.[ (λ f → ¬¬A (f ∘′ const)) , _$ tt ])

-- DNE => DEM₃
dne⇒dem₃ : ∀ {a} → DNE a → DEM₃ a a
dne⇒dem₃ dne ¬[A×B] = dne λ ¬[¬A⊎¬B] → ¬[A×B] $ dem₂ ¬[¬A⊎¬B]
  where dem₂ = dne⇒dem₂ dne

-- WEM <=> DEM₃
em⇒wem : ∀ {a} → EM a → WEM a
em⇒wem em with em
... | inj₁ x = inj₁ x
... | inj₂ y = inj₂ y

-- https://ncatlab.org/nlab/show/weak+excluded+middle
wem⇒dem₃ : ∀ {a} → WEM a → DEM₃ a a
wem⇒dem₃ wem ¬[A×B] with wem | wem
... | inj₁ ¬A  | _        = inj₁ ¬A
... | inj₂ ¬¬A | inj₁ ¬B  = inj₂ ¬B
... | inj₂ ¬¬A | inj₂ ¬¬B = ⊥-elim $ DN-undistrib-× (¬¬A , ¬¬B) ¬[A×B]

dem₃⇒wem : ∀ {a} → DEM₃ a a → WEM a
dem₃⇒wem dem₃ = dem₃ ¬[A×¬A]

wem-i∧stable⇒dec : ∀ {a} {A : Set a} → WEM-i A → Stable A → Dec A
wem-i∧stable⇒dec (inj₁ x) stable = no x
wem-i∧stable⇒dec (inj₂ y) stable = yes (stable y)

-- Converse of contraposition
dne⇒contraposition-converse : ∀ {a} → DNE a → {A B : Set a} → (¬ A → ¬ B) → B → A
dne⇒contraposition-converse dne ¬A→¬B b = dne $ contraposition ¬A→¬B (DN-intro b)

contraposition-converse⇒dne : ∀ {a} → ({A B : Set a} → (¬ A → ¬ B) → B → A) → DNE a
contraposition-converse⇒dne f = f DN-intro

-- MI <=> EM
mi⇒em : ∀ {a} → MI a a → EM a
mi⇒em f = Sum.swap $ f id

em⇒mi : ∀ {a} → EM a → MI a a
em⇒mi em f = Sum.swap $ Sum.map₁ f em

-- EM <=> [¬A→B]→A⊎B
em⇒[¬A→B]→A⊎B : ∀ {a} → EM a → {A B : Set a} → (¬ A → B) → A ⊎ B
em⇒[¬A→B]→A⊎B em f = Sum.map₂ f em

[¬A→B]→A⊎B⇒em : ∀ {a} → ({A B : Set a} → (¬ A → B) → A ⊎ B) → EM a
[¬A→B]→A⊎B⇒em f = f id

-- Gödel-Dummett logic (LC)
em⇒lc : ∀ {a} → EM a → LC a a
em⇒lc em = em⇒[¬A→B]→A⊎B em λ ¬[A→B] b → ⊥-elim $ ¬[A→B] (const b)

lc⇒dem₃ : ∀ {a} → LC a a → DEM₃ a a
lc⇒dem₃ lc ¬[A×B] with lc
... | inj₁ A→B = inj₁ (contraposition (λ x → x , A→B x) ¬[A×B])
... | inj₂ B→A = inj₂ (contraposition (λ y → B→A y , y) ¬[A×B])

lc⇒wem : ∀ {a} → LC a a → WEM a
lc⇒wem lc = dem₃⇒wem $ lc⇒dem₃ lc

-- Properties of DNS
dne⇒dns : ∀ {a} → DNE a → DNS a a
dne⇒dns dne f = dne λ x → x λ y → y λ z → dne (f z)

-- DNS <=> ¬ ¬ EM
dns⇒¬¬em : ∀ {a} → DNS (lsuc a) a → ¬ ¬ EM a
dns⇒¬¬em dns = DN-map (λ x {A} → x A) $ dns λ x → DN-EM-i

¬¬em⇒dns : ∀ {a} → ¬ ¬ EM a → DNS a a
¬¬em⇒dns ¬¬em =
  λ ∀x→¬¬Px ¬[∀x→Px] → ¬¬em λ em → ¬[∀x→Px] (λ x → (em⇒dne em) (∀x→¬¬Px x))

-- other properties
[¬A→A]→A⇒dne : ∀ {a} → ({A : Set a} → (¬ A → A) → A) → DNE a
[¬A→A]→A⇒dne f ¬¬A = f λ ¬A → ⊥-elim (¬¬A ¬A)

em⇒[¬A→A]→A : ∀ {a} → EM a → {A : Set a} → (¬ A → A) → A
em⇒[¬A→A]→A em f = Sum.[ id , f ] em

-- DNE <=> ¬[A×¬B]→A→B
dne⇒¬[A×¬B]→A→B : ∀ {a} → DNE a → {A B : Set a} → ¬ (A × ¬ B) → A → B
dne⇒¬[A×¬B]→A→B dne = dne λ x → x λ y z → ⊥-elim (y (z , (λ w → x λ u v → w)))

¬[A×¬B]→A→B⇒dne : ∀ {a} → ({A B : Set a} → ¬ (A × ¬ B) → A → B) → DNE a
¬[A×¬B]→A→B⇒dne f ¬¬A = f (uncurry id) ¬¬A

-- EM <=> [A→B]→¬A⊎B
em⇒[A→B]→¬A⊎B : ∀ {a} → EM a → {A B : Set a} → (A → B) → ¬ A ⊎ B
em⇒[A→B]→¬A⊎B em f with em
... | inj₁ y  = inj₂ y
... | inj₂ ¬B = inj₁ (contraposition f ¬B)

[A→B]→¬A⊎B⇒em : ∀ {a} → ({A B : Set a} → (A → B) → ¬ A ⊎ B) → EM a
[A→B]→¬A⊎B⇒em f = Sum.swap (f id)

dne⇒¬[A→¬B]→A×B : ∀ {a} → DNE a → {A B : Set a} → ¬ (A → ¬ B) → A × B
dne⇒¬[A→¬B]→A×B dne f = dne λ ¬[A×B] → f λ x y → ¬[A×B] (x , y)

-- the counterexample principle
dne⇒¬[A→B]→A×¬B : ∀ {a} → DNE a → {A B : Set a} → ¬ (A → B) → A × ¬ B
dne⇒¬[A→B]→A×¬B dne f =
  dne λ ¬[A×¬B] → f λ x → ⊥-elim (¬[A×¬B] (x , (λ y → f (const y))))

¬[A→B]→A×¬B⇒dne : ∀ {a} → ({A B : Set a} → ¬ (A → B) → A × ¬ B) → DNE a
¬[A→B]→A×¬B⇒dne {a} f ¬¬A with f {B = Lift a ⊥} λ A→L⊥ → ¬¬A λ x → lower $ A→L⊥ x
... | x , _ = x

-- WEM <=> DN-distrib-⊎
wem⇒DN-distrib-⊎ : ∀ {a} → WEM a → {A B : Set a} → ¬ ¬ (A ⊎ B) → ¬ ¬ A ⊎ ¬ ¬ B
wem⇒DN-distrib-⊎ wem ¬¬[A⊎B] with wem | wem
... | inj₁ ¬A  | inj₁ ¬B  = ⊥-elim $ ¬¬[A⊎B] (¬A×¬B→¬[A⊎B] (¬A , ¬B))
... | inj₁ ¬A  | inj₂ ¬¬B = inj₂ ¬¬B
... | inj₂ ¬¬A | _        = inj₁ ¬¬A

DN-distrib-⊎⇒wem : ∀ {a} → ({A B : Set a} → ¬ ¬ (A ⊎ B) → ¬ ¬ A ⊎ ¬ ¬ B) → WEM a
DN-distrib-⊎⇒wem DN-distrib-⊎ = Sum.swap $ Sum.map₂ TN-to-N $ DN-distrib-⊎ DN-EM-i

DN-ip : ∀ {p q r} {P : Set p} {Q : Set q} {R : Q → Set r} →
        Q → (P → Σ Q R) → ¬ ¬ (Σ Q λ x → (P → R x))
DN-ip q f = DN-map
  Sum.[ (λ x → Prod.map₂ const (f x)) , (λ ¬P → q , λ P → ⊥-elim $ ¬P P) ] DN-EM-i

dne⇒ip : ∀ {a b c} → DNE (a ⊔ b ⊔ c) → IP a b c
dne⇒ip dne q f = dne (DN-ip q f)

-- Properties of EM⁻¹
em⇒em⁻¹ : ∀ {a} → EM a → EM⁻¹ a
em⇒em⁻¹ em _ = em

-- DNE⁻¹ <=> EM⁻¹
dne⁻¹⇒em⁻¹ : ∀ {a} → Extensionality a lzero → DNE⁻¹ a → EM⁻¹ a
dne⁻¹⇒em⁻¹ ext dne⁻¹ isP = dne⁻¹ isP′ DN-EM-i where
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
-- Properties of LPO, LLPO, WLPO, MP, MP⊎, WMP
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
... | inj₂ ¬∃¬P = inj₁ (P-stable⇒¬∃¬P→∀P (DecU⇒stable P?) ¬∃¬P)

lpo⇒mp : ∀ {a p} {A : Set a} → LPO A p → MP A p
lpo⇒mp lpo P? ¬∀P with lpo (¬-DecU P?)
... | inj₁ t    = t
... | inj₂ ¬∃¬P = ⊥-elim $ ¬∀P $ P-stable⇒¬∃¬P→∀P (DecU⇒stable P?) ¬∃¬P

wlpo∧mp⇒lpo : ∀ {a p} {A : Set a} → WLPO A p → MP A p → LPO A p
wlpo∧mp⇒lpo wlpo mp P? with wlpo (¬-DecU P?)
... | inj₁ ∀¬P  = inj₂ (∀¬P→¬∃P ∀¬P)
... | inj₂ ¬∀¬P =
  inj₁ $ P-stable⇒∃¬¬P→∃P (DecU⇒stable P?) $ mp (¬-DecU P?) ¬∀¬P

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
... | inj₂ ¬¬∀P = inj₁ (P-stable⇒¬¬∀P→∀P (DecU⇒stable P?) ¬¬∀P)

-- WLPO <=> WLPO-Alt
wlpo⇒wlpo-Alt : ∀ {a p} {A : Set a} → WLPO A p → WLPO-Alt A p
wlpo⇒wlpo-Alt wlpo P? = Sum.map ∀¬P→¬∃P ¬∀¬P→¬¬∃P (wlpo (¬-DecU P?))

wlpo-Alt⇒wlpo : ∀ {a p} {A : Set a} → WLPO-Alt A p → WLPO A p
wlpo-Alt⇒wlpo wlpo-Alt P? =
  Sum.map (P-stable⇒¬∃¬P→∀P (DecU⇒stable P?)) ¬¬∃¬P→¬∀P (wlpo-Alt (¬-DecU P?))

-- MP <=> MR
mp⇒mr : ∀ {a p} {A : Set a} → MP A p → MR A p
mp⇒mr mp P? ¬¬∃P =
  P-stable⇒∃¬¬P→∃P (DecU⇒stable P?) $ mp (¬-DecU P?) (¬¬∃P→¬∀¬P ¬¬∃P)

mr⇒mp : ∀ {a p} {A : Set a} → MR A p → MP A p
mr⇒mp mr P? ¬∀P = mr (¬-DecU P?) (P-stable⇒¬∀P→¬¬∃¬P (DecU⇒stable P?) ¬∀P)

-- (WMP ∧ MP⊎) <=> MP
mp⇒wmp : ∀ {a p} {A : Set a} → MP A p → WMP A p
mp⇒wmp mp P? pp = P-stable⇒∃¬¬P→∃P (DecU⇒stable P?) $
  mp (¬-DecU P?) (Sum.[ ¬¬∃P→¬∀¬P , (λ ¬¬∃P×¬P _ →
    ⊥-stable $ DN-map (¬[A×¬A] ∘ proj₂) ¬¬∃P×¬P) ] (pp P?))

mr⇒mp⊎ : ∀ {a p} {A : Set a} → MR A p → MP⊎ A p
mr⇒mp⊎ mr {P = P} {Q = Q} P? Q? ¬[¬∃P×¬∃Q] with
  mr {P = λ x → P x ⊎ Q x} (DecU-⊎ P? Q?) (¬[¬∃P×¬∃Q]→¬¬∃x→Px⊎Qx ¬[¬∃P×¬∃Q])
... | x , Px⊎Qx = Sum.map (DN-intro ∘′ (x ,_)) (DN-intro ∘′ (x ,_)) Px⊎Qx

-- Markov’s principle, Church’s thesis and LindeUf’s theorem by Hajime lshihara
-- α = P, β = Q, γ = R
wmp∧mp⊎⇒mr : ∀ {a p} {A : Set a} → WMP A p → MP⊎ A p → MR A p
wmp∧mp⊎⇒mr {a} {p} {A} wmp mp⊎ {P = P} P? ¬¬∃P = wmp P? Lem.¬¬∃Q⊎¬¬∃R
  where
  module Lem {Q : A → Set p} (Q? : DecU Q) where
    R : A → Set p
    R x = P x × ¬ Q x

    ¬¬∃x→Qx⊎Rx : ¬ ¬ ∃ λ x → Q x ⊎ R x
    ¬¬∃x→Qx⊎Rx = DN-map (λ {(x , Px) → x , Sum.map₂ (Px ,_) (Q? x) }) ¬¬∃P

    R? : DecU R
    R? = DecU-× P? (¬-DecU Q?)

    ¬¬∃Q⊎¬¬∃R : ¬ ¬ ∃ Q ⊎ ¬ ¬ ∃ R
    ¬¬∃Q⊎¬¬∃R = mp⊎ Q? R? ([¬¬∃x→Px⊎Qx]→¬[¬∃P×¬∃Q] ¬¬∃x→Qx⊎Rx)

-- MP⊎ <=> MP⊎-Alt
mp⊎⇒mp⊎-Alt : ∀ {a p} {A : Set a} → MP⊎ A p → MP⊎-Alt A p
mp⊎⇒mp⊎-Alt mp⊎ P? Q? =
  Sum.map (contraposition ∀P→¬∃¬P) (contraposition ∀P→¬∃¬P) ∘′
  mp⊎ (¬-DecU P?) (¬-DecU Q?) ∘′
  contraposition (Prod.map (P-stable⇒¬∃¬P→∀P (DecU⇒stable P?)) (P-stable⇒¬∃¬P→∀P (DecU⇒stable Q?)))

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

{-
llpo⇒mp∨ : ∀ {a p} {A : Set a} → LLPO A p → MP∨ A p
llpo⇒mp∨ {p = p} {A = A} llpo {P = P} {Q = Q} P? Q? ¬¬[∃x→Px⊎Qx] =
  Sum.swap ¬¬∃Q⊎¬¬∃P
  where
  R S : A → Set p
  R x = P x × ¬ Q x
  S x = ¬ P x × Q x
  R? : DecU R
  R? = DecU-× P? (¬-DecU Q?)
  S? : DecU S
  S? = DecU-× (¬-DecU P?) Q?
  ¬[∃R×∃S] : ¬ (∃ R × ∃ S)
  ¬[∃R×∃S] (∃R , ∃S) = {!   !}
  ¬∃R⊎¬∃S : ¬ ∃ R ⊎ ¬ ∃ S
  ¬∃R⊎¬∃S = llpo R? S? ¬[∃R×∃S]
  ¬∃R→¬∃Q→⊥ : ¬ ∃ R → ¬ ∃ Q → ⊥
  ¬∃R→¬∃Q→⊥ ¬∃R ¬∃Q = ¬∃P→∀¬P ¬∃Q {!   !} {!   !}
  -- ¬ ∃ λ x → P x × ¬ Q x
  -- ¬ ∃ λ x → ¬ Q x
  ¬¬∃Q⊎¬¬∃P : ¬ ¬ ∃ Q ⊎ ¬ ¬ ∃ P
  ¬¬∃Q⊎¬¬∃P = Sum.map ¬∃R→¬∃Q→⊥ {!   !} ¬∃R⊎¬∃S
-}

{-
-- LLPO -> MP⊎
llpo⇒mp⊎ : ∀ {a p} {A : Set a} → ((a b : A) → EM-i (a ≡ b)) → LLPO A (a ⊔ p) → MP⊎ A (a ⊔ p)
llpo⇒mp⊎ {a} {p} {A} A-dec llpo {P = P} {Q = Q} P? Q? ¬[¬∃P×¬∃Q] = {!   !}
  where
  ¬¬∃x→Px×Qx : ¬ ¬ ∃ λ x → P x ⊎ Q x
  ¬¬∃x→Px×Qx = ¬[¬∃P×¬∃Q]→¬¬∃x→Px⊎Qx ¬[¬∃P×¬∃Q]

  R S : A → Set (a ⊔ p)
  -- R x = P x × ¬ Q x
  -- S x = ¬ P x × Q x

-- R S : A → Set (a ⊔ p)
-- R x = ∀ (i : A)  → i < x  → (¬ P i × ¬ Q i) × P x × ¬ Q x
-- S x = ∀ (i : A)  → i < x  → (¬ P i × ¬ Q i) × ¬ P x × Q x

  -- R x = (∀ (y : A) → y ≡ x) × P x × ¬ Q x
  -- S x = (∀ (y : A) → y ≡ x) × ¬ P x × Q x
  R x = ((y : A) → y ≢ x → ¬ P y × ¬ Q y) × P x × ¬ Q x
  S x = ((y : A) → y ≢ x → ¬ P y × ¬ Q y) × ¬ P x × Q x
  ¬[∃R×∃S] : ¬ (∃ R × ∃ S)
  ¬[∃R×∃S] ((x , neqx , Px , ¬Qx) , y , neqy , ¬Py , Qx) =
    ¬¬∃x→Px×Qx λ {(w , Pw⊎Qw) → Sum.[ (λ Pw →
      Sum.[ (λ w≡y → ¬Py (subst P w≡y Pw)) , (λ w≢y → (λ t → proj₁ t Pw) $ neqy w w≢y) ] (A-dec w y) ) ,
      (λ Qw →
            {!   !}) ] Pw⊎Qw }
  -- ((x , ∀z→z≡x , Px , ¬Qx) , y , ∀z→z≡y , ¬Py , Qy) =
  -- ¬¬∃x→Px×Qx λ {(w , Pw⊎Qw) → Sum.[ (λ Pw → ¬Py {! sub  Pw  !}) , (λ Qw → {!   !}) ] Pw⊎Qw }
  --  ((x , Px , ¬Qx) , y , ¬Py , Qy) = ¬¬∃x→Px×Qx λ {(z , Pz⊎Qz) → Sum.[ (λ Pz → {! ¬Py Pz  !}) , {!   !} ] Pz⊎Qz}

  -- ¬[¬∃P×¬∃Q] ((λ ∃P → {!   !}) , (λ ∃Q → {!   !}))

  R? : DecU R
  R? x with P? x | Q? x
  R? x | inj₁ Px | inj₁ Qx = inj₂ λ ∃x→ → {!   !}
  R? x | inj₁ Px | inj₂ ¬Qx = inj₁ ((λ y y≢x → {!   !} , {!   !}) , (Px , ¬Qx))
  R? x | inj₂ y | inj₁ x₁ = {!   !}
  R? x | inj₂ y | inj₂ y₁ = {!   !}

  ¬∃R⊎¬∃S : ¬ ∃ R ⊎ ¬ ∃ S
  ¬∃R⊎¬∃S = llpo (λ x → {!   !}) {!   !} ¬[∃R×∃S]

  result : ¬ ¬ ∃ P ⊎ ¬ ¬ ∃ Q
  result with ¬∃R⊎¬∃S
  result | inj₁ ¬∃R = inj₂ (contraposition (λ ¬∃Q → {!   !}) ¬∃R)
  -- ¬∃R × ¬∃Q → ⊥
  -- ¬∃×→Px×¬Qx × ¬∃Q
  --  (x , Px ¬Qx) ,
  result | inj₂ ¬∃S = {!   !}
-}

-- Bool version of axioms
private
  module _ {a p} {A : Set a} {P : A → Set p} where
    toBool : DecU P → (A → Bool)
    toBool P? x = ⌊ em-i⇒dec (P? x) ⌋

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
  not[x]≢true⇒x≡true {true}  _  = refl

  not[x]≡true→x≢true : ∀ {x} → not x ≡ true → x ≢ true
  not[x]≡true→x≢true notx≡true = x≡false⇒x≢true (not-injective notx≡true)

  x≢true⇒x≡false : ∀ {x} → x ≢ true → x ≡ false
  x≢true⇒x≡false {false} neq = refl
  x≢true⇒x≡false {true} neq = ⊥-elim $ neq refl

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

-- http://www.cs.bham.ac.uk/~mhe/papers/omniscient-2011-07-06.pdf
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
      x≢true⇒x≡false $ contraposition
        (ε-correct P) (∃¬P→¬∀P (Prod.map₂ x≡false⇒x≢true e))

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

-- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.127.3062&rep=rep1&type=pdf
Exhaustible : ∀ {a} → Set a → Set a
Exhaustible A = Σ ((A → Bool) → Bool) λ ∀K →
  (P : A → Bool) → ∀K P ≡ true → ∀ x → P x ≡ true
