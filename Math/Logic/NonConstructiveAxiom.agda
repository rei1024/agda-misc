-- https://ncatlab.org/nlab/show/principle+of+omniscience
-- http://math.fau.edu/lubarsky/Separating%20LLPO.pdf
-- https://arxiv.org/pdf/1804.05495.pdf
-- https://www.cs.bham.ac.uk/~mhe/papers/omniscient-journal-revised.pdf
-- https://www.jaist.ac.jp/~t-nemoto/WMP.pdf
-- http://math.fau.edu/lubarsky/Separating%20LLPO.pdf

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Logic.NonConstructiveAxiom where

-- agda-stdlib
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Bool
open import Data.Sum as Sum
open import Data.Product as Prod
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality

Stable : ∀ {a} → Set a → Set a
Stable A = ¬ ¬ A → A

-- Axioms
-- Excluded middle
EM-i : ∀ {a} → Set a → Set a
EM-i A = A ⊎ ¬ A

EM : ∀ a → Set (lsuc a)
EM a = ∀ {A : Set a} → EM-i A

-- Double negation elimination
DNE : ∀ a → Set (lsuc a)
DNE a = ∀ {A : Set a} → Stable A

-- Peirce's law
Peirce-i : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Peirce-i A B = ((A → B) → A) → A

Peirce : ∀ a b → Set (lsuc (a ⊔ b))
Peirce a b = {A : Set a} {B : Set b} → Peirce-i A B

-- Material implication
MI-i : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
MI-i A B = (A → B) → ¬ A ⊎ B

MI : ∀ a b → Set (lsuc (a ⊔ b))
MI a b = {A : Set a} {B : Set b} → MI-i A B

--  De Morgan's laws
DEM₁-i : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
DEM₁-i A B = ¬ (¬ A × ¬ B) → A ⊎ B

DEM₂-i : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
DEM₂-i A B = ¬ (¬ A ⊎ ¬ B) → A × B

DEM₃-i : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
DEM₃-i A B = ¬ (A × B) → ¬ A ⊎ ¬ B

DEM₁ : ∀ a b → Set (lsuc (a ⊔ b))
DEM₁ a b = {A : Set a} {B : Set b} → DEM₁-i A B

DEM₂ : ∀ a b → Set (lsuc (a ⊔ b))
DEM₂ a b = {A : Set a} {B : Set b} → DEM₂-i A B

DEM₃ : ∀ a b → Set (lsuc (a ⊔ b))
DEM₃ a b = {A : Set a} {B : Set b} → DEM₃-i A B

-- Weak excluded middle
-- https://ncatlab.org/nlab/show/weak+excluded+middle
-- WLEM WPEM
WEM-i : ∀ {a} → Set a → Set a
WEM-i A = ¬ A ⊎ ¬ ¬ A

WEM : ∀ a → Set (lsuc a)
WEM a = {A : Set a} → WEM-i A

-- Gödel-Dummett logic (LC)
LC-i : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
LC-i A B = (A → B) ⊎ (B → A)

LC : ∀ a b → Set (lsuc (a ⊔ b))
LC a b = {A : Set a} {B : Set b} → LC-i A B

-- Double-negation shift
-- if domain of P is finite this can be proved.
-- https://ncatlab.org/nlab/show/double-negation+shift
DNS-i : ∀ {a} p → Set a → Set (a ⊔ lsuc p)
DNS-i {a} p A = {P : A → Set p} → (∀ x → ¬ ¬ P x) → ¬ ¬ (∀ x → P x)

DNS : ∀ a p → Set (lsuc (a ⊔ p))
DNS a p = {A : Set a} → DNS-i p A

-- Independence-of-premise
IP : ∀ p q r → Set (lsuc (p ⊔ q ⊔ r))
IP p q r = ∀ {P : Set p} {Q : Set q} {R : Q → Set r} →
             Q → (P → Σ Q R) → (Σ Q λ x → (P → R x))

-- Unary decidable predicate
DecU : ∀ {a p} {A : Set a} → (A → Set p) → Set (a ⊔ p)
DecU P = ∀ x → P x ⊎ ¬ P x

private
  toPred : ∀ {a} {A : Set a} → (A → Bool) → (A → Set)
  toPred P x = P x ≡ true

-- The limited principle of omniscience
-- https://ncatlab.org/nlab/show/principle+of+omniscience
LPO-i : ∀ {a p} {A : Set a} → (A → Set p) → Set (a ⊔ p)
LPO-i P = DecU P → ∃ P ⊎ ¬ ∃ P

LPO : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
LPO A p = {P : A → Set p} → LPO-i P

LPO-Bool-i : ∀ {a} {A : Set a} → (A → Bool) → Set a
LPO-Bool-i P = ∃ (toPred P) ⊎ ¬ ∃ (toPred P)

LPO-Bool : ∀ {a} → Set a → Set a
LPO-Bool A = (P : A → Bool) → LPO-Bool-i P

-- http://www.cs.bham.ac.uk/~mhe/papers/omniscient-2011-07-06.pdf
LPO-Bool-Alt-i : ∀ {a} {A : Set a} → (A → Bool) → Set a
LPO-Bool-Alt-i P = (∃ λ x → P x ≡ false) ⊎ (∀ x → P x ≡ true)

LPO-Bool-Alt : ∀ {a} → Set a → Set a
LPO-Bool-Alt A = (P : A → Bool) → LPO-Bool-Alt-i P

-- The lesser limited principle of omniscience
LLPO-i : ∀ {a p} {A : Set a} → (P Q : A → Set p) → Set (a ⊔ p)
LLPO-i P Q = DecU P → DecU Q → ¬ (∃ P × ∃ Q) → ¬ ∃ P ⊎ ¬ ∃ Q

LLPO : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
LLPO A p = {P Q : A → Set p} → LLPO-i P Q

LLPO-Bool-i : ∀ {a} {A : Set a} → (P Q : A → Bool) → Set a
LLPO-Bool-i P Q = ¬ (∃ (toPred P) × ∃ (toPred Q)) → ¬ ∃ (toPred P) ⊎ ¬ ∃ (toPred Q)

LLPO-Bool : ∀ {a} → Set a → Set a
LLPO-Bool A = (P Q : A → Bool) → LLPO-Bool-i P Q

-- Weak limited principle of omniscience
-- https://www.cs.bham.ac.uk/~mhe/papers/omniscient-journal-revised.pdf
-- http://math.fau.edu/lubarsky/Separating%20LLPO.pdf
-- ∀-PEM
WLPO-i : ∀ {a p} {A : Set a} → (A → Set p) → Set (a ⊔ p)
WLPO-i P = DecU P → (∀ x → P x) ⊎ ¬ (∀ x → P x)

WLPO : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
WLPO A p = {P : A → Set p} → WLPO-i P

-- Alternative form of WLPO
WLPO-Alt-i : ∀ {a p} {A : Set a} → (A → Set p) → Set (a ⊔ p)
WLPO-Alt-i P = DecU P → ¬ ∃ P ⊎ ¬ ¬ ∃ P

WLPO-Alt : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
WLPO-Alt A p = {P : A → Set p} → WLPO-Alt-i P

-- Markov's principle
-- https://ncatlab.org/nlab/show/Markov%27s+principle
MP-i : ∀ {a p} {A : Set a} → (A → Set p) → Set (a ⊔ p)
MP-i P = DecU P → ¬ (∀ x → P x) → ∃ λ x → ¬ P x

MP : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
MP A p = {P : A → Set p} → MP-i P

-- Markov's rule
MR-i : ∀ {a p} {A : Set a} → (A → Set p) → Set (a ⊔ p)
MR-i P = DecU P → ¬ ¬ ∃ P → ∃ P

MR : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
MR A p = {P : A → Set p} → MR-i P

-- Weak Markov's principle
-- https://ncatlab.org/nlab/show/Markov%27s+principle
WMP-i : ∀ {a p} {A : Set a} → (A → Set p) → Set (a ⊔ lsuc p)
WMP-i {p = p} {A = A} P = DecU P →
  ({Q : A → Set p} → DecU Q → ¬ ¬ ∃ Q ⊎ (¬ ¬ ∃ λ x → P x × ¬ Q x)) →
  ∃ P

WMP : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
WMP A p  = {P : A → Set p} → WMP-i P

WMP-Bool-i : ∀ {a} {A : Set a} → (A → Bool) → Set a
WMP-Bool-i {A = A} P =
  ((Q : A → Bool) →
    ¬ ¬ ∃ (λ x → Q x ≡ true) ⊎ (¬ ¬ ∃ λ x → P x ≡ true × Q x ≢ true)) →
   ∃ λ x → P x ≡ true

WMP-Bool : ∀ {a} (A : Set a) → Set a
WMP-Bool A = (P : A → Bool) → WMP-Bool-i P

-- Disjunctive Markov’s principle
MP⊎-i : ∀ {a p} {A : Set a} → (P Q : A → Set p) → Set (a ⊔ p)
MP⊎-i P Q = DecU P → DecU Q → ¬ (¬ ∃ P × ¬ ∃ Q) → ¬ ¬ ∃ P ⊎ ¬ ¬ ∃ Q
-- ¬ ¬ (∃ λ x → P x ⊎ Q x)

MP⊎ : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
MP⊎ A p = {P Q : A → Set p} → MP⊎-i P Q

MP⊎-Bool-i : ∀ {a} {A : Set a} → (P Q : A → Bool) → Set a
MP⊎-Bool-i P Q = ¬ (¬ ∃ (toPred P) × ¬ ∃ (toPred Q)) → ¬ ¬ ∃ (toPred P) ⊎ ¬ ¬ ∃ (toPred Q)

MP⊎-Bool : ∀ {a} → Set a → Set a
MP⊎-Bool A = (P Q : A → Bool) → MP⊎-Bool-i P Q

MP⊎-Alt-i : ∀ {a p} {A : Set a} → (P Q : A → Set p) → Set (a ⊔ p)
MP⊎-Alt-i P Q = DecU P → DecU Q →
  ¬ ((∀ x → P x) × (∀ x → Q x)) → ¬ (∀ x → P x) ⊎ ¬ (∀ x → Q x)

MP⊎-Alt : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
MP⊎-Alt A p = {P Q : A → Set p} → MP⊎-Alt-i P Q

-- https://plato.stanford.edu/entries/axiom-choice/choice-and-type-theory.html
ACLT : ∀ {a b} → Set a → Set b → ∀ p → Set (a ⊔ b ⊔ lsuc p)
ACLT A B p = {P : A → B → Set p} →
  ((x : A) → ∃ λ y → P x y) → Σ (A → B) λ f → (x : A) → P x (f x)

-- HoTT
isProp : ∀ {a} → Set a → Set a
isProp A = (x y : A) → x ≡ y

isSet : ∀ {a} → Set a → Set a
isSet A = {x y : A} (p q : x ≡ y) → p ≡ q

EM⁻¹ : ∀ a → Set (lsuc a)
EM⁻¹ a = {A : Set a} → isProp A → EM-i A

DNE⁻¹ : ∀ a → Set (lsuc a)
DNE⁻¹ a = {A : Set a} → isProp A → Stable A