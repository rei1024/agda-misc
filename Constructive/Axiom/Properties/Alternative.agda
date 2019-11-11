module Constructive.Axiom.Properties.Alternative where

-- agda-stdlib
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; not)
open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; s≤s; z≤n; _≤?_)
import Data.Nat.Properties as ℕₚ
import Data.Nat.Induction as ℕInd
open import Function.Base
import Induction.WellFounded as Ind
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary
  using (tri≈; tri<; tri>; Rel; Trichotomous)
open import Relation.Binary.PropositionalEquality

-- agda-misc
open import Constructive.Axiom
open import Constructive.Combinators
open import Constructive.Common

-- LLPO => MP∨
record HasPropertiesForLLPO⇒MP∨
  {a} r p (A : Set a) : Set (a ⊔ lsuc r ⊔ lsuc p)
  where
  field
    _<_       : Rel A r
    <-cmp     : Trichotomous _≡_ _<_
    <-all-dec : {P : A → Set p} → DecU P → DecU (λ n → ∀ i → i < n → P i)
    <-wf      : Ind.WellFounded _<_

llpo⇒mp∨ : ∀ {r p a} {A : Set a} →
           HasPropertiesForLLPO⇒MP∨ r p A → LLPO A (p ⊔ a ⊔ r) → MP∨ A p
llpo⇒mp∨ {r} {p} {a} {A = A} has llpo {P = P} {Q} P? Q? ¬¬[∃x→Px⊎Qx] =
  Sum.swap ¬¬∃Q⊎¬¬∃P
  where
  open HasPropertiesForLLPO⇒MP∨ has
  -- ex. R 5
  -- n : 0 1 2 3 4 5 6 7 8
  -- P : 0 0 0 0 0 1 ? ? ?
  -- Q : 0 0 0 0 0 0 ? ? ?
  R S : A → Set (r ⊔ p ⊔ a)
  R n = (∀ i → i < n → ¬ P i × ¬ Q i) × P n × ¬ Q n
  S n = (∀ i → i < n → ¬ P i × ¬ Q i) × ¬ P n × Q n

  lem : DecU (λ n → ∀ i → i < n → ¬ P i × ¬ Q i)
  lem = <-all-dec (DecU-× (¬-DecU P?) (¬-DecU Q?))

  R? : DecU R
  R? = DecU-× lem (DecU-× P? (¬-DecU Q?))

  S? : DecU S
  S? = DecU-× lem (DecU-× (¬-DecU P?) Q?)

  ¬[∃R×∃S] : ¬ (∃ R × ∃ S)
  ¬[∃R×∃S] ((m , ∀i→i<m→¬Pi×¬Qi , Pm , ¬Qm) ,
            (n , ∀i→i<n→¬Pi×¬Qi , ¬Pn , Qn)) with <-cmp m n
  ... | tri< m<n _ _ = proj₁ (∀i→i<n→¬Pi×¬Qi m m<n) Pm
  ... | tri≈ _ m≡n _ = ¬Pn (subst P m≡n Pm)
  ... | tri> _ _ n<m = proj₂ (∀i→i<m→¬Pi×¬Qi n n<m) Qn

  -- use LLPO
  ¬∃R⊎¬∃S : ¬ ∃ R ⊎ ¬ ∃ S
  ¬∃R⊎¬∃S = llpo R? S? ¬[∃R×∃S]

  -- Induction by _<_
  byacc₁ : (∀ x → ¬ R x) → (∀ x → ¬ Q x) → ∀ x → Ind.Acc _<_ x → ¬ P x
  byacc₁ ∀¬R ∀¬Q x (Ind.acc rs) Px =
    ∀¬R x ((λ i i<x → (λ Pi → byacc₁ ∀¬R ∀¬Q i (rs i i<x) Pi) , ∀¬Q i) , (Px , ∀¬Q x))

  ∀¬R→∀¬Q→∀¬P : (∀ x → ¬ R x) → (∀ x → ¬ Q x) → ∀ x → ¬ P x
  ∀¬R→∀¬Q→∀¬P ∀¬R ∀¬Q x Px = byacc₁ ∀¬R ∀¬Q x (<-wf x) Px

  ¬∃R→¬∃Q→¬∃P : ¬ ∃ R → ¬ ∃ Q → ¬ ∃ P
  ¬∃R→¬∃Q→¬∃P ¬∃R ¬∃Q = ∀¬P→¬∃P $ ∀¬R→∀¬Q→∀¬P (¬∃P→∀¬P ¬∃R) (¬∃P→∀¬P ¬∃Q)

  byacc₂ : (∀ x → ¬ S x) → (∀ x → ¬ P x) → ∀ x → Ind.Acc _<_ x → ¬ Q x
  byacc₂ ∀¬S ∀¬P x (Ind.acc rs) Qx =
    ∀¬S x ((λ i i<x → ∀¬P i , λ Qi → byacc₂ ∀¬S ∀¬P i (rs i i<x) Qi) , (∀¬P x , Qx))

  ∀¬S→∀¬P→∀¬Q : (∀ x → ¬ S x) → (∀ x → ¬ P x) → ∀ x → ¬ Q x
  ∀¬S→∀¬P→∀¬Q ∀¬S ∀¬P x Qx = byacc₂ ∀¬S ∀¬P x (<-wf x) Qx

  ¬∃S→¬∃P→¬∃Q : ¬ ∃ S → ¬ ∃ P → ¬ ∃ Q
  ¬∃S→¬∃P→¬∃Q ¬∃S ¬∃P = ∀¬P→¬∃P $ ∀¬S→∀¬P→∀¬Q (¬∃P→∀¬P ¬∃S) (¬∃P→∀¬P ¬∃P)

  ¬¬[∃P⊎∃Q] : ¬ ¬ (∃ P ⊎ ∃ Q)
  ¬¬[∃P⊎∃Q] = DN-map ∃-distrib-⊎ ¬¬[∃x→Px⊎Qx]

  ¬¬∃Q⊎¬¬∃P : ¬ ¬ ∃ Q ⊎ ¬ ¬ ∃ P
  ¬¬∃Q⊎¬¬∃P =
    Sum.map
      (λ ¬∃R ¬∃Q → ¬¬[∃P⊎∃Q] Sum.[ ¬∃R→¬∃Q→¬∃P ¬∃R ¬∃Q , ¬∃Q ])
      (λ ¬∃S ¬∃P → ¬¬[∃P⊎∃Q] Sum.[ ¬∃P , ¬∃S→¬∃P→¬∃Q ¬∃S ¬∃P ])
      ¬∃R⊎¬∃S
