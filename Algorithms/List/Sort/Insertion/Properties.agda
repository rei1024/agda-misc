{-# OPTIONS --without-K --safe #-}

-- Properties of insertion sort

open import Relation.Binary as B

module Algorithms.List.Sort.Insertion.Properties {c ℓ₁ ℓ₂} (DTO : DecTotalOrder c ℓ₁ ℓ₂) where

-- agda-stdlib
open import Level

open import Data.Bool hiding (_≤_; _≤?_; _<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List
import      Data.List.Properties as Listₚ
import      Data.Nat as ℕ
import      Data.Nat.Properties as ℕₚ
open import Data.Product hiding (swap)

import      Data.List.Relation.Binary.Equality.Setoid as ListSetoidEquality
open import Data.List.Relation.Unary.All as All
import      Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.List.Relation.Unary.Linked as Linked
import      Data.List.Relation.Unary.Linked.Properties as Linkedₚ
open import Data.List.Relation.Unary.AllPairs as AllPairs
import      Data.List.Relation.Unary.AllPairs.Properties as AllPairsₚ
import      Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid
import      Data.List.Relation.Binary.Permutation.Setoid.Properties
  as PermutationSetoidProperties

open import Function.Core using (_∘_; _$_; flip)

import      Relation.Binary.Properties.DecTotalOrder as DecTotalOrderProperties
open import Relation.Binary.PropositionalEquality using (_≡_)
import      Relation.Binary.PropositionalEquality as ≡ hiding ([_])
import      Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Nullary
open import Relation.Unary as U

-- agda-misc
open import Experiment.ListRelationProperties using (foldr-preservesʳ; Linked-∷⁻ʳ)
open import Algorithms.List.Sort.Insertion

open DecTotalOrder DTO renaming (Carrier to A)
open InsertionSortOperation _≤?_
open DecTotalOrderProperties DTO
open PermutationSetoid Eq.setoid renaming (refl to PSrefl; trans to PStrans)
open PermutationSetoidProperties Eq.setoid
open ListSetoidEquality Eq.setoid

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
(x ≈? y) | yes x≤y | yes y≤x = yes (antisym x≤y y≤x)
(x ≈? y) | yes x≤y | no  y≰x = no (≱⇒≉ y≰x)
(x ≈? y) | no  x≰y | yes y≤x = no (≰⇒≉ x≰y)
(x ≈? y) | no  x≰y | no  y≰x = ⊥-elim $ ≰∧≱⇒⊥ x≰y y≰x

IsSorted : List A → Set _
IsSorted = Linked _≤_

insert-permutation : ∀ x xs → insert x xs ↭ x ∷ xs
insert-permutation x []       = ↭-refl
insert-permutation x (y ∷ ys) with x ≤? y
... | yes _ = ↭-refl
... | no  _ = ↭-trans (prep Eq.refl (insert-permutation x ys))
                      (swap Eq.refl Eq.refl ↭-refl)

insert-isSorted : ∀ x {xs} → IsSorted xs → IsSorted (insert x xs)
insert-isSorted x {[]}     _ = [-]
insert-isSorted x {y ∷ ys} xs-isSorted with x ≤? y
... | yes x≤y = x≤y ∷ xs-isSorted
... | no  x≰y = Linkedₚ.AllPairs⇒Linked (hd ∷ tl)
  where
  y≤x : y ≤ x
  y≤x = ≰⇒≥ x≰y
  lem : All (y ≤_) ys
  lem = AllPairs.head (Linkedₚ.Linked⇒AllPairs trans xs-isSorted)
  hd : All (y ≤_) (insert x ys)
  hd = All-resp-↭ ≤-respʳ-≈ (↭-sym (insert-permutation x ys)) (y≤x ∷ lem)
  insert[x,ys]-isSorted : IsSorted (insert x ys)
  insert[x,ys]-isSorted = insert-isSorted x {ys} (Linked-∷⁻ʳ xs-isSorted)
  tl : AllPairs _≤_ (insert x ys)
  tl = Linkedₚ.Linked⇒AllPairs trans insert[x,ys]-isSorted

sort-isSorted : ∀ xs → IsSorted (sort xs)
sort-isSorted xs = foldr-preservesʳ insert-isSorted [] xs

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

isSorted-insert : ∀ {x xs} → IsSorted (x ∷ xs) → insert x xs ≋ x ∷ xs
isSorted-insert {x} {[]}     _         = ≋-refl
isSorted-insert {x} {y ∷ ys} (x≤y ∷ _) = insert-stop ys x≤y

sort-isSorted-id : ∀ xs → IsSorted xs → sort xs ≋ xs
sort-isSorted-id []       xs-isSorted   = ≋-refl
sort-isSorted-id (x ∷ xs) x∷xs-isSorted = begin
  sort (x ∷ xs)
    ≡⟨⟩
  insert x (sort xs)
    ≈⟨ insert-cong-≋ Eq.refl
                     (sort-isSorted-id xs (Linked-∷⁻ʳ x∷xs-isSorted)) ⟩
  insert x xs
    ≈⟨ isSorted-insert x∷xs-isSorted ⟩
  x ∷ xs
    ∎
  where open SetoidReasoning ≋-setoid

sort-idem : ∀ xs → sort (sort xs) ≋ sort xs
sort-idem xs = sort-isSorted-id (sort xs) (sort-isSorted xs)

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
  insert-swap x y (z ∷ zs) | no y≰z | yes x≤z | yes y≤x = ⊥-elim (y≰z (trans y≤x x≤z))
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
  insert x  (insert y  (sort xs)) ≈⟨ insert-cong-≋ eq₁ (insert-cong-≋ eq₂ (sort-cong-↭-≋ xs↭ys)) ⟩
  insert x′ (insert y′ (sort ys)) ≈⟨ insert-swap x′ y′ (sort ys) ⟩
  insert y′ (insert x′ (sort ys)) ∎
  where open SetoidReasoning ≋-setoid
sort-cong-↭-≋ {xs} {ys} (PStrans {ys = zs} xs↭zs zs↭ys) = begin
  sort xs ≈⟨ sort-cong-↭-≋ xs↭zs ⟩
  sort zs ≈⟨ sort-cong-↭-≋ zs↭ys ⟩
  sort ys ∎
  where open SetoidReasoning ≋-setoid

-- TODO move to ListRelationProperties
IsSorted-transport : ∀ {xs ys} → xs ≋ ys → IsSorted xs → IsSorted ys
IsSorted-transport []                []        = []
IsSorted-transport (x≈y ∷ [])        [-]       = [-]
IsSorted-transport (e₁ ∷ e₂ ∷ xs≋ys) (x ∷ ixs) =
 (≤-respʳ-≈ e₂ $ ≤-respˡ-≈ e₁ x) ∷ IsSorted-transport (e₂ ∷ xs≋ys) ixs

isSorted-unique : ∀ {xs ys} → xs ↭ ys → IsSorted xs → IsSorted ys → xs ≋ ys
isSorted-unique {xs} {ys} xs↭ys ixs iys = begin
  xs      ≈⟨ ≋-sym $ sort-isSorted-id xs ixs ⟩
  sort xs ≈⟨ sort-cong-↭-≋ xs↭ys ⟩
  sort ys ≈⟨ sort-isSorted-id ys iys ⟩
  ys      ∎
  where open SetoidReasoning ≋-setoid
