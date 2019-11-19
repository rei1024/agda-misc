-- Properties of insertion sort

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary as B

module Algorithms.List.Sort.Insertion.Properties
  {c ℓ₁ ℓ₂} (DTO : DecTotalOrder c ℓ₁ ℓ₂)
  where

-- agda-stdlib
open import Level

open import Data.Bool hiding (_≤_; _≤?_; _<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List
import      Data.List.Properties as Listₚ
import      Data.Nat as ℕ
import      Data.Nat.Properties as ℕₚ
open import Data.Product hiding (swap)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import      Data.List.Relation.Binary.Equality.Setoid as ListSetoidEquality
import      Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid
import      Data.List.Relation.Binary.Permutation.Setoid.Properties
  as PermutationSetoidProperties
open import Data.List.Relation.Unary.All as All
import      Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.List.Relation.Unary.Linked as Linked
open import      Data.List.Relation.Unary.Linked.Properties as Linkedₚ
open import Data.List.Relation.Unary.AllPairs as AllPairs
import      Data.List.Relation.Unary.AllPairs.Properties as AllPairsₚ

open import Function.Base using (_∘_; _$_; flip)

import      Relation.Binary.Properties.DecTotalOrder as DecTotalOrderProperties
open import Relation.Binary.PropositionalEquality using (_≡_)
import      Relation.Binary.PropositionalEquality as ≡ hiding ([_])
import      Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Nullary
open import Relation.Unary as U

-- agda-misc
open import Algorithms.List.Sort.Common DTO
open import Algorithms.List.Sort.Insertion
open import Experiment.ListRelationProperties
  using (foldr-preservesʳ; Linked-∷⁻ʳ; Linked-resp-≋)

open DecTotalOrder DTO renaming (Carrier to A)
open DecTotalOrderProperties DTO
open PermutationSetoid Eq.setoid renaming (refl to PSrefl; trans to PStrans)
open PermutationSetoidProperties Eq.setoid
open ListSetoidEquality Eq.setoid
open InsertionSortOperation _≤?_

private
  _≰_ : Rel A _
  x ≰ y = ¬ (x ≤ y)

  -- stdlib
  <⇒≤ : ∀ {x y} → x < y → x ≤ y
  <⇒≤ = proj₁

  ≰⇒≥ : ∀ {x y} → x ≰ y → y ≤ x
  ≰⇒≥ = <⇒≤ ∘ ≰⇒>

  ≰∧≱⇒⊥ : ∀ {x y} → x ≰ y → y ≰ x → ⊥
  ≰∧≱⇒⊥ x≰y y≰x = x≰y (≰⇒≥ y≰x)

  ≰⇒≉ : ∀ {x y} → x ≰ y → ¬ (x ≈ y)
  ≰⇒≉ x≰y x≈y = x≰y (≤-respʳ-≈ x≈y refl)

  ≱⇒≉ : ∀ {x y} → y ≰ x → ¬ (x ≈ y)
  ≱⇒≉ x≱y x≈y = ≰⇒≉ x≱y (Eq.sym x≈y)

  -- stdlib
  _≈?_ : ∀ x y → Dec (x ≈ y)
  x ≈? y with x ≤? y | y ≤? x
  ... | yes x≤y | yes y≤x = yes (antisym x≤y y≤x)
  ... | yes x≤y | no  y≰x = no (≱⇒≉ y≰x)
  ... | no  x≰y | yes y≤x = no (≰⇒≉ x≰y)
  ... | no  x≰y | no  y≰x = ⊥-elim $ ≰∧≱⇒⊥ x≰y y≰x

  ≤⇒<∨≈ : ∀ {x y} → x ≤ y → x < y ⊎ x ≈ y
  ≤⇒<∨≈ {x} {y} x≤y with x ≈? y
  ... | yes x≈y = inj₂ x≈y
  ... | no  x≉y = inj₁ (≤∧≉⇒< x≤y x≉y)

insert-permutation : ∀ x xs → insert x xs ↭ x ∷ xs
insert-permutation x []       = ↭-refl
insert-permutation x (y ∷ ys) with x ≤? y
... | true  because _ = ↭-refl
... | false because _ = ↭-trans (prep Eq.refl (insert-permutation x ys))
                      (swap Eq.refl Eq.refl ↭-refl)

insert-pres-Sorted : ∀ x {xs} → Sorted xs → Sorted (insert x xs)
insert-pres-Sorted x {[]}     _ = [-]
insert-pres-Sorted x {y ∷ ys} xs-Sorted with x ≤? y
... | yes x≤y = x≤y ∷ xs-Sorted
... | no  x≰y = Linkedₚ.AllPairs⇒Linked (hd ∷ tl)
  where
  y≤x : y ≤ x
  y≤x = ≰⇒≥ x≰y
  lem : All (y ≤_) ys
  lem = AllPairs.head (toAllPairs xs-Sorted)
  hd : All (y ≤_) (insert x ys)
  hd = All-resp-↭ ≤-respʳ-≈ (↭-sym (insert-permutation x ys)) (y≤x ∷ lem)
  insert[x,ys]-Sorted : Sorted (insert x ys)
  insert[x,ys]-Sorted = insert-pres-Sorted x {ys} (Linked-∷⁻ʳ xs-Sorted)
  tl : AllPairs _≤_ (insert x ys)
  tl = toAllPairs insert[x,ys]-Sorted

sort-Sorted : ∀ xs → Sorted (sort xs)
sort-Sorted xs = foldr-preservesʳ insert-pres-Sorted [] xs

sort-permutation : ∀ xs → sort xs ↭ xs
sort-permutation []       = ↭-refl
sort-permutation (x ∷ xs) = begin
  sort (x ∷ xs)      ≡⟨⟩
  insert x (sort xs) ≈⟨ insert-permutation x (sort xs) ⟩
  x ∷ sort xs        ≈⟨ prep Eq.refl (sort-permutation xs) ⟩
  x ∷ xs             ∎
  where open SetoidReasoning ↭-setoid

insert-cong-≋ : ∀ {x y xs ys} → x ≈ y → xs ≋ ys → insert x xs ≋ insert y ys
insert-cong-≋ {x} {y} {[]}      {[]}      x≈y xs≋ys = x≈y ∷ []
insert-cong-≋ {x} {y} {x₁ ∷ xs} {y₁ ∷ ys} x≈y (x₁≈y₁ ∷ xs≋ys) with x ≤? x₁ | y ≤? y₁
... | yes p | yes p₁ = x≈y ∷ x₁≈y₁ ∷ xs≋ys
... | yes p | no ¬p  = ⊥-elim (¬p (≤-respʳ-≈ x₁≈y₁ (≤-respˡ-≈ x≈y p)))
... | no ¬p | yes p  = ⊥-elim (¬p (≤-respʳ-≈ (Eq.sym x₁≈y₁) (≤-respˡ-≈ (Eq.sym x≈y) p)))
... | no ¬p | no ¬p₁ = x₁≈y₁ ∷ insert-cong-≋ x≈y xs≋ys

insert-stop : ∀ {x y} ys → x ≤ y → insert x (y ∷ ys) ≋ x ∷ y ∷ ys
insert-stop {x} {y} ys x≤y with x ≤? y
... | yes _   = ≋-refl
... | no  x≰y = ⊥-elim (x≰y x≤y)

insert-into : ∀ {x y} ys → x ≰ y → insert x (y ∷ ys) ≋ y ∷ insert x ys
insert-into {x} {y} ys x≰y with x ≤? y
... | yes x≤y = ⊥-elim (x≰y x≤y)
... | no  _   = ≋-refl

Sorted-insert : ∀ {x xs} → Sorted (x ∷ xs) → insert x xs ≋ x ∷ xs
Sorted-insert {x} {[]}     _         = ≋-refl
Sorted-insert {x} {y ∷ ys} (x≤y ∷ _) = insert-stop ys x≤y

sort-Sorted-id : ∀ xs → Sorted xs → sort xs ≋ xs
sort-Sorted-id []       xs-Sorted   = ≋-refl
sort-Sorted-id (x ∷ xs) x∷xs-Sorted = begin
  sort (x ∷ xs)
    ≡⟨⟩
  insert x (sort xs)
    ≈⟨ insert-cong-≋ Eq.refl
                     (sort-Sorted-id xs (Linked-∷⁻ʳ x∷xs-Sorted)) ⟩
  insert x xs
    ≈⟨ Sorted-insert x∷xs-Sorted ⟩
  x ∷ xs
    ∎
  where open SetoidReasoning ≋-setoid

sort-idem : ∀ xs → sort (sort xs) ≋ sort xs
sort-idem xs = sort-Sorted-id (sort xs) (sort-Sorted xs)

module _ where
  open SetoidReasoning ≋-setoid

  insert-swap : ∀ x y xs → insert x (insert y xs) ≋ insert y (insert x xs)
  insert-swap x y [] with x ≤? y | y ≤? x
  ... | yes x≤y | yes y≤x = x≈y ∷ Eq.sym x≈y ∷ []
    where x≈y = antisym x≤y y≤x
  ... | yes _   | no  _   = ≋-refl
  ... | no  _   | yes _   = ≋-refl
  ... | no  x≰y | no  y≰x = ⊥-elim $ ≰∧≱⇒⊥ x≰y y≰x
  insert-swap x y (z ∷ zs) with y ≤? z | x ≤? z
  insert-swap x y (z ∷ zs) | yes _   | yes _ with x ≤? y | y ≤? x
  insert-swap x y (z ∷ zs) | yes y≤z | yes x≤z | yes x≤y | yes y≤x =
    x≈y ∷ Eq.sym x≈y ∷ ≋-refl
    where x≈y = antisym x≤y y≤x
  insert-swap x y (z ∷ zs) | yes y≤z | yes _   | yes _  | no _ = begin
    x ∷ y ∷ z ∷ zs        ≈˘⟨ Eq.refl ∷ insert-stop zs y≤z ⟩
    x ∷ insert y (z ∷ zs) ∎
  insert-swap x y (z ∷ zs) | yes _   | yes x≤z | no _   | yes _ = begin
    y ∷ insert x (z ∷ zs) ≈⟨ Eq.refl ∷ insert-stop zs x≤z ⟩
    y ∷ x ∷ z ∷ zs        ∎
  insert-swap x y (z ∷ zs) | yes y≤z | yes x≤z | no x≰y | no y≰x =
    ⊥-elim $ ≰∧≱⇒⊥ x≰y y≰x
  insert-swap x y (z ∷ zs) | yes _   | no  _ with x ≤? y
  insert-swap x y (z ∷ zs) | yes y≤z | no  x≰z | yes x≤y =
    ⊥-elim $ x≰z (trans x≤y y≤z)
  insert-swap x y (z ∷ zs) | yes y≤z | no  x≰z | no  x≰y = begin
    y ∷ insert x (z ∷ zs)      ≈⟨ Eq.refl ∷ insert-into zs x≰z ⟩
    y ∷ z ∷ insert x zs        ≈˘⟨ insert-stop (insert x zs) y≤z ⟩
    insert y (z ∷ insert x zs) ∎
  insert-swap x y (z ∷ zs) | no _   | yes _ with y ≤? x
  insert-swap x y (z ∷ zs) | no y≰z | yes x≤z | yes y≤x =
    ⊥-elim (y≰z (trans y≤x x≤z))
  insert-swap x y (z ∷ zs) | no y≰z | yes x≤z | no  _   = begin
    insert x (z ∷ insert y zs) ≈⟨ insert-stop (insert y zs) x≤z ⟩
    x ∷ z ∷ insert y zs        ≈˘⟨ Eq.refl ∷ insert-into zs y≰z ⟩
    x ∷ insert y (z ∷ zs)      ∎
  insert-swap x y (z ∷ zs) | no y≰z | no  x≰z = begin
    insert x (z ∷ insert y zs) ≈⟨ insert-into (insert y zs) x≰z ⟩
    z ∷ insert x (insert y zs) ≈⟨ Eq.refl ∷ insert-swap x y zs ⟩
    z ∷ insert y (insert x zs) ≈˘⟨ insert-into (insert x zs) y≰z ⟩
    insert y (z ∷ insert x zs) ∎

sort-cong-↭-≋ : ∀ {xs ys} → xs ↭ ys → sort xs ≋ sort ys
sort-cong-↭-≋ {xs}         {.xs}          PSrefl               = ≋-refl
sort-cong-↭-≋ {_ ∷ _}      {_ ∷ _}        (prep eq xs↭ys)      =
  insert-cong-≋ eq (sort-cong-↭-≋ xs↭ys)
sort-cong-↭-≋ {x ∷ y ∷ xs} {y′ ∷ x′ ∷ ys} (swap eq₁ eq₂ xs↭ys) = begin
  insert x  (insert y  (sort xs)) ≈⟨ insert-cong-≋ eq₁
                                    (insert-cong-≋ eq₂ (sort-cong-↭-≋ xs↭ys)) ⟩
  insert x′ (insert y′ (sort ys)) ≈⟨ insert-swap x′ y′ (sort ys) ⟩
  insert y′ (insert x′ (sort ys)) ∎
  where open SetoidReasoning ≋-setoid
sort-cong-↭-≋ {xs} {ys} (PStrans {ys = zs} xs↭zs zs↭ys) = begin
  sort xs ≈⟨ sort-cong-↭-≋ xs↭zs ⟩
  sort zs ≈⟨ sort-cong-↭-≋ zs↭ys ⟩
  sort ys ∎
  where open SetoidReasoning ≋-setoid

Sorted-unique : ∀ {xs ys} → xs ↭ ys → Sorted xs → Sorted ys → xs ≋ ys
Sorted-unique {xs} {ys} xs↭ys ixs iys = begin
  xs      ≈⟨ ≋-sym $ sort-Sorted-id xs ixs ⟩
  sort xs ≈⟨ sort-cong-↭-≋ xs↭ys ⟩
  sort ys ≈⟨ sort-Sorted-id ys iys ⟩
  ys      ∎
  where open SetoidReasoning ≋-setoid
