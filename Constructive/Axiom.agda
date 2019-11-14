-- Omniscience principles

-- https://ncatlab.org/nlab/show/principle+of+omniscience
-- http://math.fau.edu/lubarsky/Separating%20LLPO.pdf
-- https://arxiv.org/pdf/1804.05495.pdf
-- https://www.cs.bham.ac.uk/~mhe/papers/omniscient-journal-revised.pdf
-- https://www.jaist.ac.jp/~t-nemoto/WMP.pdf
-- http://math.fau.edu/lubarsky/Separating%20LLPO.pdf

-- TODO
-- WKL: weak Koning's lemma
-- BE: Every real number in [0,1] has binary expansion
-- IVT: intermediate value theorem
-- BD-N
-- LLPOₙ

-- WLPO -> WKL
-- WKL <=> LLPO

{-# OPTIONS --without-K --safe --exact-split #-}

module Constructive.Axiom where

-- agda-stdlib
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function

-- agda-misc
open import Constructive.Common
open import TypeTheory.HoTT.Base using (isProp)

---------------------------------------------------------------------------
-- Axioms
-- -i indicates instance

-- Excluded middle
EM : ∀ a → Set (lsuc a)
EM a = ∀ {A : Set a} → Dec⊎ A

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

-- call/cc
Call/CC-i : ∀ {a} → Set a → Set a
Call/CC-i A = Peirce-i A ⊥

Call/CC : ∀ a → Set (lsuc a)
Call/CC a = ∀ {A : Set a} → Call/CC-i A

-- Gödel-Dummett logic
-- Dirk Gently's Principle (DGP)
DGP-i : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
DGP-i A B = (A → B) ⊎ (B → A)

DGP : ∀ a b → Set (lsuc (a ⊔ b))
DGP a b = {A : Set a} {B : Set b} → DGP-i A B

-- Weak excluded middle
-- https://ncatlab.org/nlab/show/weak+excluded+middle
-- WLEM WPEM
WEM-i : ∀ {a} → Set a → Set a
WEM-i A = Dec⊎ (¬ A)

WEM : ∀ a → Set (lsuc a)
WEM a = {A : Set a} → WEM-i A

-- Double-negation shift
-- if domain of P is finite this can be proved.
-- https://ncatlab.org/nlab/show/double-negation+shift
DNS-i : ∀ {a p} {A : Set a} → (A → Set p) → Set (a ⊔ p)
DNS-i P = (∀ x → ¬ ¬ P x) → ¬ ¬ (∀ x → P x)

DNS : ∀ a p → Set (lsuc (a ⊔ p))
DNS a p = {A : Set a} {P : A → Set p} → DNS-i P

-- Independence-of-premise
IP : ∀ p q r → Set (lsuc (p ⊔ q ⊔ r))
IP p q r = ∀ {P : Set p} {Q : Set q} {R : Q → Set r} →
           Q → (P → Σ Q R) → (Σ Q λ x → (P → R x))

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

-- The lesser limited principle of omniscience
-- Σ⁰₁-DML
LLPO-i : ∀ {a p} {A : Set a} → (P Q : A → Set p) → Set (a ⊔ p)
LLPO-i P Q = DecU P → DecU Q → ¬ (∃ P × ∃ Q) → ¬ ∃ P ⊎ ¬ ∃ Q

LLPO : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
LLPO A p = {P Q : A → Set p} → LLPO-i P Q

LLPO-Bool-i : ∀ {a} {A : Set a} → (P Q : A → Bool) → Set a
LLPO-Bool-i P Q = ¬ (∃ (toPred P) × ∃ (toPred Q)) → ¬ ∃ (toPred P) ⊎ ¬ ∃ (toPred Q)

LLPO-Bool : ∀ {a} → Set a → Set a
LLPO-Bool A = (P Q : A → Bool) → LLPO-Bool-i P Q

-- Markov's principle
-- LPE
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
WMP-i {p = p} {A = A} P =
  DecU P →
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

MP⊎ : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
MP⊎ A p = {P Q : A → Set p} → MP⊎-i P Q

MP⊎-Bool-i : ∀ {a} {A : Set a} → (P Q : A → Bool) → Set a
MP⊎-Bool-i P Q = ¬ (¬ ∃ (toPred P) × ¬ ∃ (toPred Q)) →
                 ¬ ¬ ∃ (toPred P) ⊎ ¬ ¬ ∃ (toPred Q)

MP⊎-Bool : ∀ {a} → Set a → Set a
MP⊎-Bool A = (P Q : A → Bool) → MP⊎-Bool-i P Q

MP⊎-Alt-i : ∀ {a p} {A : Set a} → (P Q : A → Set p) → Set (a ⊔ p)
MP⊎-Alt-i P Q = DecU P → DecU Q →
                ¬ ((∀ x → P x) × (∀ x → Q x)) → ¬ (∀ x → P x) ⊎ ¬ (∀ x → Q x)

MP⊎-Alt : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
MP⊎-Alt A p = {P Q : A → Set p} → MP⊎-Alt-i P Q

MP∨-i : ∀ {a p} {A : Set a} → (P Q : A → Set p) → Set (a ⊔ p)
MP∨-i P Q = DecU P → DecU Q →
            ¬ ¬ (∃ λ x → P x ⊎ Q x) → ¬ ¬ ∃ P ⊎ ¬ ¬ ∃ Q

MP∨ : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
MP∨ A p = {P Q : A → Set p} → MP∨-i P Q

-- Σ-DGP
-- Equivalent to LLPO
Σ-DGP-i : ∀ {a p} {A : Set a} (P Q : A → Set p) → Set (a ⊔ p)
Σ-DGP-i P Q = DecU P → DecU Q → DGP-i (∃ P) (∃ Q)

Σ-DGP : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
Σ-DGP A p = ∀ {P Q : A → Set p} → Σ-DGP-i P Q

-- Π-DGP
Π-DGP-i : ∀ {a p} {A : Set a} (P Q : A → Set p) → Set (a ⊔ p)
Π-DGP-i P Q = DecU P → DecU Q → DGP-i (∀ x → P x) (∀ x → Q x)

Π-DGP : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
Π-DGP A p = ∀ {P Q : A → Set p} → Π-DGP-i P Q

-- Σ-Π-DGP
Σ-Π-DGP-i : ∀ {a p} {A : Set a} (P Q : A → Set p) → Set (a ⊔ p)
Σ-Π-DGP-i P Q = DecU P → DecU Q → DGP-i (∃ P) (∀ x → Q x)

Σ-Π-DGP : ∀ {a} (A : Set a) p → Set (a ⊔ lsuc p)
Σ-Π-DGP A p = ∀ {P Q : A → Set p} → Σ-Π-DGP-i P Q

-- Kripke's Schema
KS : ∀ {a} (A : Set a) p q → Set (a ⊔ lsuc p ⊔ lsuc q)
KS A p q = ∀ (P : Set p) → Σ (A → Set q) λ Q → DecU Q × (P <=> ∃ Q)

-- Principle of Finite Possiblity
-- Principle of inverse Decision (PID)
PFP : ∀ {a} (A : Set a) p q → Set (a ⊔ lsuc p ⊔ lsuc q)
PFP A p q = {P : A → Set p} → DecU P →
            Σ (A → Set q) λ Q → DecU Q × ((∀ x → P x) <=> ∃ Q)

PFP-Bool-ℕ : Set
PFP-Bool-ℕ =
  (α : ℕ → Bool) →
  Σ (ℕ → Bool) (λ β → (∀ n → α n ≡ false) <=> ∃ λ n → β n ≡ true)

-- Weak Principle of Finite Possiblity
WPFP : ∀ {a} (A : Set a) p q → Set (a ⊔ lsuc p ⊔ lsuc q)
WPFP A p q = {P : A → Set p} → DecU P →
             Σ (A → Set q) λ Q → DecU Q × ((∀ x → P x) <=> (¬ (∀ x → Q x)))

WPFP-Bool-ℕ : Set
WPFP-Bool-ℕ =
  (α : ℕ → Bool) →
  Σ (ℕ → Bool) λ β → (∀ n → α n ≡ false) <=> (¬ (∀ n → β n ≡ false))

-- https://plato.stanford.edu/entries/axiom-choice/choice-and-type-theory.html
ACLT : ∀ {a b} → Set a → Set b → ∀ p → Set (a ⊔ b ⊔ lsuc p)
ACLT A B p = {P : A → B → Set p} →
             ((x : A) → ∃ λ y → P x y) → Σ (A → B) λ f → (x : A) → P x (f x)

-- HoTT
EM⁻¹ : ∀ a → Set (lsuc a)
EM⁻¹ a = {A : Set a} → isProp A → Dec⊎ A

DNE⁻¹ : ∀ a → Set (lsuc a)
DNE⁻¹ a = {A : Set a} → isProp A → Stable A

-- WKL
takeT : ℕ → (ℕ → Bool) → List Bool
takeT ℕ.zero    α = []
takeT (ℕ.suc n) α = α 0 ∷ takeT n (λ m → α (ℕ.suc m))

-- "THE WEAK KONIG LEMMA, BROUWER’S FAN THEOREM, DE MORGAN’S LAW, AND DEPENDENT CHOICE"
PreTree : Set₁
PreTree = List Bool → Set

IsDetachable : PreTree → Set
IsDetachable T = DecU T

-- closed under restrictions
IsClosed : PreTree → Set
IsClosed T = ∀ u v → Prefix _≡_ v u → T u → T v

IsInfinite : PreTree → Set
IsInfinite T = ∀ n → ∃ λ u → T u × n ≡ length u

IsFinite : PreTree → Set
IsFinite T = ∃ λ n → ∀ u → ¬ T u × n ≡ length u

IsWellFounded : PreTree → Set
IsWellFounded T = Σ (ℕ → Bool) λ α → ∃ λ n → ¬ T (takeT n α)

HasInfinitePath : PreTree → Set
HasInfinitePath T = Σ (ℕ → Bool) λ α → ∀ n → T (takeT n α)

IsTree : PreTree → Set
IsTree T = IsDetachable T × IsClosed T

-- Weak Kőnig Lemma
WKL : Set₁
WKL = ∀ T → IsTree T → IsInfinite T → HasInfinitePath T

-- Brouwer’s Fan Theorem
FAN : Set₁
FAN = ∀ T → IsTree T → IsWellFounded T → IsFinite T

-- BD-N
Peseudobounded : (ℕ → Set) → Set
Peseudobounded S = (s : ℕ → ℕ) → (∀ n → S (s n)) → ∃ λ N → s N < N
