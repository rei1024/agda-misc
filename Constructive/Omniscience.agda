
{-# OPTIONS --without-K --safe #-}
-- https://www.cs.bham.ac.uk/~mhe/papers/omniscient-journal-revised.pdf

module Constructive.Omniscience where

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
ℕ∞ = Σ (ℕ → Bool) λ x → ∀ i → T (x (suc i)) → T (x i)

⟦_⟧C : ℕ → ℕ → Bool
⟦ n ⟧C = λ m → isYes (m <? n)

⟦_⟧C-con : ∀ n i → T (⟦ n ⟧C (suc i)) → T (⟦ n ⟧C i)
⟦ n ⟧C-con i True[si<n] = fromWitness (m+n≤o⇒n≤o 1 $ toWitness True[si<n])

⟦_⟧ : ℕ → ℕ∞
⟦ n ⟧ = ⟦ n ⟧C , ⟦ n ⟧C-con

∞ : ℕ∞
∞ = (λ _ → true) , (λ i _ → tt)

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

⟦⟧-cong : ∀ {m n} → m ≡ n → ⟦ m ⟧ ≈∞ ⟦ n ⟧
⟦⟧-cong {m} {n} m≡n i = cong (λ x → ⟦ x ⟧C i) m≡n

-- Proposition 3.1
-- r = ≤-all
≤-all : (ℕ → Bool) → (ℕ → Bool)
≤-all α zero    = α 0
≤-all α (suc n) = α (suc n) ∧ ≤-all α n

≤-all-idem : ∀ α → ≤-all (≤-all α) ≈ ≤-all α
≤-all-idem α zero    = refl
≤-all-idem α (suc n) = begin
  (α (suc n) ∧ ≤-all α n) ∧ ≤-all (≤-all α) n
    ≡⟨ cong ((α (suc n) ∧ ≤-all α n) ∧_) $ ≤-all-idem α n ⟩
  (α (suc n) ∧ ≤-all α n) ∧ ≤-all α n
    ≡⟨ 𝔹ₚ.∧-assoc (α (suc n)) (≤-all α n) (≤-all α n) ⟩
  α (suc n) ∧ (≤-all α n ∧ ≤-all α n)
    ≡⟨ cong (α (suc n) ∧_) $ 𝔹ₚ.∧-idem (≤-all α n) ⟩
  α (suc n) ∧ ≤-all α n
    ∎
  where open ≡-Reasoning

private
  T-∧-× : ∀ {x y} → T (x ∧ y) → (T x × T y)
  T-∧-× {true} {true} t = tt , tt

  T-×-∧ : ∀ {x y} → (T x × T y) → T (x ∧ y)
  T-×-∧ {true} {true} (tt , tt) = tt

  ≤⇒≡∨< : ∀ {m n} → m ≤ n → (m ≡ n) ⊎ (m < n)
  ≤⇒≡∨< {m} {n} m≤n with m ≟ n
  ... | yes m≡n = inj₁ m≡n
  ... | no  m≢n = inj₂ (≤∧≢⇒< m≤n m≢n)

≤-all-convergent : ∀ α i → T (≤-all α (suc i)) → T (≤-all α i)
≤-all-convergent α n t = proj₂ (T-∧-× t)

≤-all-ℕ∞ : (ℕ → Bool) → ℕ∞
≤-all-ℕ∞ α = ≤-all α , ≤-all-convergent α

≤-all-extract-by-≤ : ∀ α {n k} → k ≤ n → T (≤-all α n) → T (α k)
≤-all-extract-by-≤ α {zero}  {.0}    z≤n       t = t
≤-all-extract-by-≤ α {suc n} {zero}  z≤n       t =
  ≤-all-extract-by-≤ α {n} {0} z≤n (proj₂ (T-∧-× t))
≤-all-extract-by-≤ α {suc n} {suc k} (s≤s k≤n) t with ≤⇒≡∨< k≤n
... | inj₁ k≡n    = subst (T ∘′ α ∘′ suc) (sym k≡n) (proj₁ (T-∧-× t))
... | inj₂ suck≤n = ≤-all-extract-by-≤ α suck≤n (proj₂ (T-∧-× t))

≤-all-extract : ∀ α n → T (≤-all α n) → T (α n)
≤-all-extract α n = ≤-all-extract-by-≤ α ≤-refl

≤-all-construct : ∀ α n → (∀ k → k ≤ n → T (α k)) → T (≤-all α n)
≤-all-construct α zero    f = f zero ≤-refl
≤-all-construct α (suc n) f =
  T-×-∧ ((f (suc n) ≤-refl) , ≤-all-construct α n λ k k≤n → f k (≤-step k≤n))

private
  not-injective : ∀ {x y} → not x ≡ not y → x ≡ y
  not-injective {false} {false} refl = refl
  not-injective {true}  {true}  refl = refl

  x≢y⇒not[x]≡y : ∀ {x y} → x ≢ y → not x ≡ y
  x≢y⇒not[x]≡y {false} {false} x≢y = contradiction refl x≢y
  x≢y⇒not[x]≡y {false} {true}  x≢y = refl
  x≢y⇒not[x]≡y {true}  {false} x≢y = refl
  x≢y⇒not[x]≡y {true}  {true}  x≢y = contradiction refl x≢y

  x≡y⇒not[x]≢y : ∀ {x y} → x ≡ y → not x ≢ y
  x≡y⇒not[x]≢y {false} {false} p ()
  x≡y⇒not[x]≢y {false} {true}  () q
  x≡y⇒not[x]≢y {true}  {false} () q
  x≡y⇒not[x]≢y {true}  {true}  p ()

  not[x]≢y⇒x≡y : ∀ {x y} → not x ≢ y → x ≡ y
  not[x]≢y⇒x≡y {x} {y} not[x]≢y =
    subst (_≡ y) (𝔹ₚ.not-involutive x) $ x≢y⇒not[x]≡y not[x]≢y

  not[x]≡y⇒x≢y : ∀ {x y} → not x ≡ y → x ≢ y
  not[x]≡y⇒x≢y not[x]≡y x≡y = x≡y⇒not[x]≢y x≡y not[x]≡y

-- LPO-Bool <=> ∀ x → (x #∞ ∞) ⊎ (x ≈∞ ∞)
lpo-Bool⇒∀x→x#∞⊎x≈∞ : LPO-Bool ℕ → ∀ x → (x #∞ ∞) ⊎ (x ≈∞ ∞)
lpo-Bool⇒∀x→x#∞⊎x≈∞ lpo-Bool (α , con) with lpo-Bool λ n → not (α n)
... | inj₁ (x , not[αx]≡true) = inj₁ (x , not[x]≡y⇒x≢y not[αx]≡true)
... | inj₂ ¬∃x→not[αx]≡true   =
  inj₂ λ i → not[x]≢y⇒x≡y $′ ¬∃P→∀¬P ¬∃x→not[αx]≡true i

private
  T-to-≡ : ∀ {x} → T x → x ≡ true
  T-to-≡ {true} tx = refl

  ≡-to-T : ∀ {x} → x ≡ true → T x
  ≡-to-T {true} x≡true = tt

  T-¬-not : ∀ {x} → ¬ (T x) → T (not x)
  T-¬-not {false} n = tt
  T-¬-not {true}  n = n tt

  T-not-¬ : ∀ {x} → T (not x) → ¬ (T x)
  T-not-¬ {false} tt ()
  T-not-¬ {true}  () y

  ¬-T-not-to-T : ∀ {x} → ¬ T (not x) → T x
  ¬-T-not-to-T {x} ¬Tnotx = subst T (𝔹ₚ.not-involutive x) $ T-¬-not ¬Tnotx

  ≤-to-→ : ∀ {x y} → x 𝔹.≤ y → T x → T y
  ≤-to-→ {true} {true} x≤y _ = tt

  →-to-≤ : ∀ {x y} → (T x → T y) → x 𝔹.≤ y
  →-to-≤ {false} {false} Tx→Ty = b≤b
  →-to-≤ {false} {true}  Tx→Ty = f≤t
  →-to-≤ {true}  {false} Tx→Ty = ⊥-elim (Tx→Ty tt)
  →-to-≤ {true}  {true}  Tx→Ty = b≤b

  T-≡ : ∀ {x y} → (T x → T y) → (T y → T x) → x ≡ y
  T-≡ Tx→Ty Ty→Tx = 𝔹ₚ.≤-antisym (→-to-≤ Tx→Ty) (→-to-≤ Ty→Tx)

¬T-≤-all-to-≤ : ∀ α n → ¬ T (≤-all α n) → ∃ λ k → k ≤ n × ¬ T (α k)
¬T-≤-all-to-≤ α zero    ¬T with 𝔹ₚ.T? (α 0)
... | yes Tα0 = contradiction Tα0 ¬T
... | no ¬Tα0 = 0 , (z≤n , ¬Tα0)
¬T-≤-all-to-≤ α (suc n) ¬T with 𝔹ₚ.T? (α (suc n))
... | yes Tαsn =
 Prod.map₂ (Prod.map₁ ≤-step) $
   ¬T-≤-all-to-≤ α n (contraposition (λ T≤-allαn → T-×-∧ (Tαsn , T≤-allαn)) ¬T)
... | no ¬Tαsn = suc n , ≤-refl , ¬Tαsn

¬T-≤-all-to-≤′ : ∀ α n → ¬ T (≤-all (not ∘′ α) n) → ∃ λ k → k ≤ n × T (α k)
¬T-≤-all-to-≤′ α n ¬T with ¬T-≤-all-to-≤ (not ∘ α) n ¬T
... | (k , k≤n , ¬Tnotαn) = k , (k≤n , ¬-T-not-to-T ¬Tnotαn)

¬T-≤-all-to-∃ : ∀ α n → ¬ T (≤-all α n) → ∃ λ k → ¬ T (α k)
¬T-≤-all-to-∃ α n ¬T = Prod.map₂ proj₂ (¬T-≤-all-to-≤ α n ¬T)

¬T-≤-all-to-∃′ : ∀ α n → ¬ T (≤-all (not ∘′ α) n) → ∃ λ k → T (α k)
¬T-≤-all-to-∃′ α n ¬T = Prod.map₂ proj₂ (¬T-≤-all-to-≤′ α n ¬T)

≤-to-¬T-≤-all : ∀ α n → ∃ (λ k → k ≤ n × ¬ T (α k)) → ¬ T (≤-all α n)
≤-to-¬T-≤-all α n (k , k≤n  , ¬Tαk) ttt = ¬Tαk (≤-all-extract-by-≤ α k≤n ttt)

∀x→x#∞⊎x≈∞⇒lpo-Bool : (∀ x → (x #∞ ∞) ⊎ (x ≈∞ ∞)) → LPO-Bool ℕ
∀x→x#∞⊎x≈∞⇒lpo-Bool ≈∞? P with ≈∞? (≤-all-ℕ∞ (λ n → not (P n)))
... | inj₁ (x , ≤-all[not∘P,x]≢true) =
  inj₁ (Prod.map₂ T-to-≡ (¬T-≤-all-to-∃′ P x
    (contraposition T-to-≡ ≤-all[not∘P,x]≢true)))
... | inj₂ ∀i→≤-all[not∘P,i]≡true =
  inj₂ (∀¬P→¬∃P λ i → not[x]≡y⇒x≢y (T-to-≡ $ ≤-all-extract (not ∘ P) i $
    ≡-to-T (∀i→≤-all[not∘P,i]≡true i)))

-- Theorem 3.5
ε : (ℕ∞ → Bool) → ℕ∞
ε p = ≤-all-ℕ∞ λ n → p ⟦ n ⟧

T-⟦⟧C-to-< : ∀ {n i} → T (⟦ n ⟧C i) → i < n
T-⟦⟧C-to-< t = toWitness t

<-to-T-⟦⟧C : ∀ {n i} → i < n → T (⟦ n ⟧C i)
<-to-T-⟦⟧C i<n = fromWitness i<n

lemma-1-forward : ∀ (p : ℕ∞ → Bool) n →
                  ε p ≈∞ ⟦ n ⟧ → ¬ T (p ⟦ n ⟧) × (∀ k → k < n → T (p ⟦ k ⟧))
lemma-1-forward p n εp≈∞⟦n⟧ = ¬T[p⟦n⟧] , i<n⇒Tp⟦i⟧
  where
  ∀i→≤-all[p∘⟦⟧,i]≡⟦n⟧Ci : ∀ i → ≤-all (λ m → p ⟦ m ⟧) i ≡ ⟦ n ⟧C i
  ∀i→≤-all[p∘⟦⟧,i]≡⟦n⟧Ci = εp≈∞⟦n⟧

  i<n⇒Tp⟦i⟧ : ∀ i → i < n → T (p ⟦ i ⟧)
  i<n⇒Tp⟦i⟧ i i<n = ≤-all-extract (p ∘′ ⟦_⟧) i T[≤-all[p∘⟦⟧,i]]
    where
    ⟦n⟧Ci≡true : ⟦ n ⟧C i ≡ true
    ⟦n⟧Ci≡true = T-to-≡ (<-to-T-⟦⟧C i<n)

    ≤-all[p∘⟦⟧,i]≡true : ≤-all (λ m → p ⟦ m ⟧) i ≡ true
    ≤-all[p∘⟦⟧,i]≡true = trans (∀i→≤-all[p∘⟦⟧,i]≡⟦n⟧Ci i) ⟦n⟧Ci≡true

    T[≤-all[p∘⟦⟧,i]] : T (≤-all (λ m → p ⟦ m ⟧) i)
    T[≤-all[p∘⟦⟧,i]] = ≡-to-T ≤-all[p∘⟦⟧,i]≡true

  ¬T[p⟦n⟧] : ¬ T (p ⟦ n ⟧)
  ¬T[p⟦n⟧] = contraposition (subst (T ∘′ p ∘′ ⟦_⟧) (sym m≡n)) ¬T[p⟦m⟧]
    where
    ⟦n⟧Cn≡false : ⟦ n ⟧C n ≡ false
    ⟦n⟧Cn≡false = not-injective (T-to-≡ (T-¬-not (contraposition T-⟦⟧C-to-< (n≮n n))))

    ≤-all[p∘⟦⟧,n]≡false : ≤-all (λ m → p ⟦ m ⟧) n ≡ false
    ≤-all[p∘⟦⟧,n]≡false = trans (∀i→≤-all[p∘⟦⟧,i]≡⟦n⟧Ci n) ⟦n⟧Cn≡false

    ¬T-≤-all[p∘⟦⟧,n] : ¬ T (≤-all (λ m → p ⟦ m ⟧) n)
    ¬T-≤-all[p∘⟦⟧,n] = T-not-¬ (≡-to-T (cong not ≤-all[p∘⟦⟧,n]≡false))

    ∃m→m≤n×¬T[p⟦m⟧] : ∃ λ m → m ≤ n × ¬ T (p ⟦ m ⟧)
    ∃m→m≤n×¬T[p⟦m⟧] = ¬T-≤-all-to-≤ (p ∘′ ⟦_⟧) n ¬T-≤-all[p∘⟦⟧,n]

    m : ℕ
    m = proj₁ ∃m→m≤n×¬T[p⟦m⟧]

    m≤n : m ≤ n
    m≤n = proj₁ (proj₂ ∃m→m≤n×¬T[p⟦m⟧])

    ¬T[p⟦m⟧] : ¬ T (p ⟦ m ⟧)
    ¬T[p⟦m⟧] = proj₂ (proj₂ ∃m→m≤n×¬T[p⟦m⟧])

    m≮n : m ≮ n
    m≮n m<n = ¬T[p⟦m⟧] (i<n⇒Tp⟦i⟧ m m<n)

    m≡n : m ≡ n
    m≡n = ≤-antisym m≤n (≮⇒≥ m≮n)

lemma-1-backwards : ∀ (p : ℕ∞ → Bool) n →
                    ¬ T (p ⟦ n ⟧) × (∀ k → k < n → T (p ⟦ k ⟧)) →
                    ε p ≈∞ ⟦ n ⟧
lemma-1-backwards p n (¬Tp⟦n⟧ , ∀k→k<n→Tp⟦k⟧) = ∀i→≤-all[p∘⟦⟧,i]≡⟦n⟧Ci
  where
  open ≡-Reasoning

  ∀i→≤-all[p∘⟦⟧,i]≡⟦n⟧Ci : ∀ i → ≤-all (λ m → p ⟦ m ⟧) i ≡ ⟦ n ⟧C i
  ∀i→≤-all[p∘⟦⟧,i]≡⟦n⟧Ci i with n ≤? i
  ... | yes n≤i = trans (not-injective (T-to-≡ (T-¬-not ¬T≤-all[p∘⟦⟧,i])))
                        (sym ⟦n⟧Ci≡false)
    where
    ⟦n⟧Ci≡false : ⟦ n ⟧C i ≡ false
    ⟦n⟧Ci≡false = not-injective (T-to-≡ (T-¬-not (contraposition T-⟦⟧C-to-< (≤⇒≯ n≤i))))

    ¬T≤-all[p∘⟦⟧,i] : ¬ T (≤-all (λ m → p ⟦ m ⟧) i)
    ¬T≤-all[p∘⟦⟧,i] t = ¬Tp⟦n⟧ (≤-all-extract-by-≤ (p ∘′ ⟦_⟧) n≤i t)
  ... | no  n≰i = begin
    ≤-all (λ m → p ⟦ m ⟧) i
      ≡⟨ T-to-≡ (≤-all-construct (p ∘ ⟦_⟧) i
                λ k k≤i → ∀k→k<n→Tp⟦k⟧ k (<-transʳ k≤i i<n)) ⟩
    true
     ≡⟨ sym $ T-to-≡ (<-to-T-⟦⟧C i<n) ⟩
    ⟦ n ⟧C i
     ∎
    where i<n = ≰⇒> n≰i

{-
pp : ℕ∞ → Bool
pp (x , _) = not (x 0) ∨ (x 0 ∧ not (x 1))
-}

ε-correct : (P : ℕ∞ → Bool) → P (ε P) ≡ true → ∀ x → P x ≡ true
ε-correct P P[εP]≡true x = {!   !}

searchable-Bool : Searchable-Bool ℕ∞
searchable-Bool = ε , ε-correct
