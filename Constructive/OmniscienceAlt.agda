
{-# OPTIONS --without-K --safe #-}
-- https://www.cs.bham.ac.uk/~mhe/papers/omniscient-journal-revised.pdf

module Constructive.OmniscienceAlt where

open import Level renaming (zero to lzero; suc to lsuc)
import Data.Bool as 𝔹 using (_≤_)
open import Data.Bool as 𝔹 using (Bool; true; false; T; f≤t; b≤b; _∧_; not; _∨_)
import Data.Bool.Properties as 𝔹ₚ
open import Data.Empty
open import Data.Unit using (tt)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as Prod
open import Data.Sum as Sum
open import Function.Base
open import Relation.Binary as B
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Relation.Unary as U

-- agda-misc
open import Constructive.Axiom
open import Constructive.Axiom.Properties
open import Constructive.Axiom.Properties.Base.Lemma
open import Constructive.Common
open import Constructive.Combinators

ℕ∞ : Set
ℕ∞ = Σ (ℕ → Bool) λ x → ∀ i → T (x i) → T (x (suc i))

fromℕ-C : ℕ → ℕ → Bool
fromℕ-C zero    zero    = false
fromℕ-C zero    (suc n) = true
fromℕ-C (suc m) zero    = false
fromℕ-C (suc m) (suc n) = fromℕ-C m n

fromℕ-convergent : ∀ n i → T (fromℕ-C n i) → T (fromℕ-C n (suc i))
fromℕ-convergent zero    (suc i) t = tt
fromℕ-convergent (suc n) (suc i) t = fromℕ-convergent n i t

fromℕ : ℕ → ℕ∞
fromℕ n = fromℕ-C n , fromℕ-convergent n

∞ : ℕ∞
∞ = (λ _ → false) , (λ i x → x)

_≈_ : Rel (ℕ → Bool) lzero
α ≈ β = ∀ i → α i ≡ β i

_≉_ : Rel (ℕ → Bool) lzero
α ≉ β = ¬ (α ≈ β)

_#_ : Rel (ℕ → Bool) lzero
α # β = ∃ λ i → α i ≢ β i

#⇒≉  : {α β : ℕ → Bool} → α # β → α ≉ β
#⇒≉ {α} {β} (i , αi≢βi) α≈β = αi≢βi (α≈β i)

≈-refl : {α : ℕ → Bool} → α ≈ α
≈-refl _ = refl

≈-sym : {α β : ℕ → Bool} → α ≈ β → β ≈ α
≈-sym α≈β i = sym (α≈β i)

≈-trans : {α β γ : ℕ → Bool} → α ≈ β → β ≈ γ → α ≈ γ
≈-trans α≈β β≈γ i = trans (α≈β i) (β≈γ i)

_≈∞_ : Rel ℕ∞ lzero
x ≈∞ y = proj₁ x ≈ proj₁ y

_≉∞_ : Rel ℕ∞ lzero
x ≉∞ y = proj₁ x ≉ proj₁ y

_#∞_ : Rel ℕ∞ lzero
x #∞ y = proj₁ x # proj₁ y

-- Proposition 3.1
-- r = ≤-any

≤-any : (ℕ → Bool) → (ℕ → Bool)
≤-any α zero    = α 0
≤-any α (suc n) = α (suc n) ∨ ≤-any α n

≤-any-idem : ∀ α → ≤-any (≤-any α) ≈ ≤-any α
≤-any-idem α zero    = refl
≤-any-idem α (suc n) = begin
  (α (suc n) ∨ ≤-any α n) ∨ ≤-any (≤-any α) n
    ≡⟨ cong ((α (suc n) ∨ ≤-any α n) ∨_) $ ≤-any-idem α n ⟩
  (α (suc n) ∨ ≤-any α n) ∨ ≤-any α n
    ≡⟨ 𝔹ₚ.∨-assoc (α (suc n)) (≤-any α n) (≤-any α n) ⟩
  α (suc n) ∨ (≤-any α n ∨ ≤-any α n)
    ≡⟨ cong (α (suc n) ∨_) $ 𝔹ₚ.∨-idem (≤-any α n) ⟩
  α (suc n) ∨ ≤-any α n
    ∎
  where open ≡-Reasoning

private
  T-∧-× : ∀ {x y} → T (x ∧ y) → (T x × T y)
  T-∧-× {true} {true} t = tt , tt

  T-×-∧ : ∀ {x y} → (T x × T y) → T (x ∧ y)
  T-×-∧ {true} {true} (tt , tt) = tt

  T-∨-introʳ : ∀ {x y} → T y → T (x ∨ y)
  T-∨-introʳ {true} {true} t = tt
  T-∨-introʳ {false} {true} t = tt

  T-∨-introˡ : ∀ {x y} → T x → T (x ∨ y)
  T-∨-introˡ {true} {true} t = tt
  T-∨-introˡ {true} {false} t = tt

≤-any-convergent : ∀ α i → T (≤-any α i) → T (≤-any α (suc i))
≤-any-convergent α n t = T-∨-introʳ t

≤-any-ℕ∞ : (ℕ → Bool) → ℕ∞
≤-any-ℕ∞ α = ≤-any α , ≤-any-convergent α

≤-any-construct : ∀ α n → T (α n) → T (≤-any α n)
≤-any-construct α zero    t = t
≤-any-construct α (suc n) t = T-∨-introˡ t

private
  not-injective : ∀ {x y} → not x ≡ not y → x ≡ y
  not-injective {false} {false} refl = refl
  not-injective {true}  {true}  refl = refl

  x≢y⇒not[x]≡y : ∀ {x y} → x ≢ y → not x ≡ y
  x≢y⇒not[x]≡y {false} {false} x≢y = contradiction refl x≢y
  x≢y⇒not[x]≡y {false} {true} x≢y = refl
  x≢y⇒not[x]≡y {true} {false} x≢y = refl
  x≢y⇒not[x]≡y {true} {true} x≢y = contradiction refl x≢y

  x≢y⇒x≡not[y] : ∀ {x y} → x ≢ y → x ≡ not y
  x≢y⇒x≡not[y] {x} {y} x≢y = subst (_≡ not y) (𝔹ₚ.not-involutive x) $
                             x≢y⇒not[x]≡y {not x} {not y} (x≢y ∘′ not-injective)

  x≡y⇒not[x]≢y : ∀ {x y} → x ≡ y → not x ≢ y
  x≡y⇒not[x]≢y {false} {false} p ()
  x≡y⇒not[x]≢y {false} {true} () q
  x≡y⇒not[x]≢y {true} {false} () q
  x≡y⇒not[x]≢y {true} {true} p ()

  not[x]≡true→x≢true : ∀ {x} → not x ≡ true → x ≢ true
  not[x]≡true→x≢true {false} refl ()
  not[x]≡true→x≢true {true}  ()   p

  false≢true : false ≢ true
  false≢true ()

lpo-Bool⇒∀x→x#∞⊎x≈∞ : LPO-Bool ℕ → ∀ x → (x #∞ ∞) ⊎ (x ≈∞ ∞)
lpo-Bool⇒∀x→x#∞⊎x≈∞ lpo-Bool (α , con) with lpo-Bool α
... | inj₁ (x , αx≡true) = inj₁ (x , λ αx≡false → false≢true (trans (sym αx≡false) αx≡true))
... | inj₂ ¬∃x→αx≡true   = inj₂ λ i →  x≢y⇒x≡not[y] $′ ¬∃P→∀¬P ¬∃x→αx≡true i


T-to-≡ : ∀ {x} → T x → x ≡ true
T-to-≡ {true} tx = refl

≡-to-T : ∀ {x} → x ≡ true → T x
≡-to-T {true} x≡true = tt

private
  T-¬-not : ∀ {x} → ¬ (T x) → T (not x)
  T-¬-not {false} n = tt
  T-¬-not {true}  n = n tt

  T-not-¬ : ∀ {x} → T (not x) → ¬ (T x)
  T-not-¬ {false} tt ()
  T-not-¬ {true}  () y

¬T-≤-any : ∀ α x → ¬ T (≤-any α x) → ∃ λ y → ¬ T (α y)
¬T-≤-any α zero    ¬T with α 0 | inspect α 0
... | true  | [ α0≡true ]  = contradiction tt ¬T
... | false | [ α0≡false ] = zero , (λ T[α0] → subst T α0≡false T[α0])
¬T-≤-any α (suc x) ¬T with α (suc x) | inspect α (suc x)
... | true  | [ αsn≡true ] = ¬T-≤-any α x ¬T
... | false | [ αsn≡false ] = (suc x) , (λ T[αsn] → subst T αsn≡false T[αsn])
{-
¬T-≤-any′ : ∀ α x → ¬ T (≤-any (not ∘′ α) x) → ∃ λ y → T (α y)
¬T-≤-any′ α x ¬T =
  Prod.map₂ (λ nt → subst T (𝔹ₚ.not-involutive _) (T-¬-not nt)) $′
  ¬T-≤-any (not ∘ α) x ¬T

∀x→x#∞⊎x≈∞⇒lpo-Bool : (∀ x → (x #∞ ∞) ⊎ (x ≈∞ ∞)) → LPO-Bool ℕ
∀x→x#∞⊎x≈∞⇒lpo-Bool ≈∞? P with ≈∞? (≤-any-ℕ∞ (λ n → not (P n)))
... | inj₁ (x , ≤-any[not∘P,x]≢true) =
  inj₁ (Prod.map₂ T-to-≡ (¬T-≤-any′ P x (contraposition T-to-≡ ≤-any[not∘P,x]≢true)))
... | inj₂ ∀i→≤-any[not∘P,i]≡true =
  inj₂ (∀¬P→¬∃P λ i → not[x]≡true→x≢true (T-to-≡ $ ≤-any-extract (not ∘ P) i $ ≡-to-T (∀i→≤-any[not∘P,i]≡true i)))

--  ≤-any (λ n → not (P n)) x ≡ true → ⊥
-- ≤-any (not ∘ P) x ≡ false
--
--  ---------------------------
--  T (≤-any P x)
-}
