-- Solver for cartesian category

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Cartesian

module Experiment.Categories.Category.Cartesian.BinaryProductsSolver
  {o ℓ e} {𝒞 : Category o ℓ e} (prods : BinaryProducts 𝒞) where

open import Level
open import Relation.Binary using (Rel)

import Categories.Morphism.Reasoning as MR

open Category 𝒞
open BinaryProducts prods
open HomReasoning
open MR 𝒞

private
  variable
    A B C : Obj

infixr 9 _:∘_
infixr 7 _:×_
infix 11 :⟨_,_⟩

data Sig : Set o where
  ∥_∥  : Obj → Sig
  _:×_ : Sig → Sig → Sig

⟦_⟧Sig : Sig → Obj
⟦ ∥ A ∥    ⟧Sig = A
⟦ S₁ :× S₂ ⟧Sig = ⟦ S₁ ⟧Sig × ⟦ S₂ ⟧Sig

private
  variable
    S T U V : Sig

data Expr : Rel Sig (o ⊔ ℓ) where
  :id    : Expr S S
  _:∘_   : Expr T U → Expr S T → Expr S U
  :π₁    : Expr (S :× T) S
  :π₂    : Expr (S :× T) T
  :⟨_,_⟩ : Expr U S → Expr U T → Expr U (S :× T)
  ∥_∥    : A ⇒ B → Expr ∥ A ∥ ∥ B ∥

-- normalized expression
data NExpr : Rel Sig (o ⊔ ℓ) where
  :id    : NExpr ∥ A ∥ ∥ A ∥
  :π₁    : NExpr (S :× T) S
  :π₂    : NExpr (S :× T) T
  :π₁∘_  : NExpr S (T :× U) → NExpr S T
  :π₂∘_  : NExpr S (T :× U) → NExpr S U
  ∥_∥∘_  : B ⇒ C → NExpr S ∥ B ∥ → NExpr S ∥ C ∥
  :⟨_,_⟩ : NExpr U S → NExpr U T → NExpr U (S :× T)

⟦_⟧ : Expr S T → ⟦ S ⟧Sig ⇒ ⟦ T ⟧Sig
⟦ :id          ⟧ = id
⟦ e₁ :∘ e₂     ⟧ = ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧
⟦ :π₁          ⟧ = π₁
⟦ :π₂          ⟧ = π₂
⟦ :⟨ e₁ , e₂ ⟩ ⟧ = ⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩
⟦ ∥ f ∥        ⟧ = f

⟦_⟧N : NExpr S T → ⟦ S ⟧Sig ⇒ ⟦ T ⟧Sig
⟦ :id          ⟧N = id
⟦ :π₁          ⟧N = π₁
⟦ :π₂          ⟧N = π₂
⟦ :π₁∘ e       ⟧N = π₁ ∘ ⟦ e ⟧N
⟦ :π₂∘ e       ⟧N = π₂ ∘ ⟦ e ⟧N
⟦ ∥ f ∥∘ e     ⟧N = f ∘ ⟦ e ⟧N
⟦ :⟨ e₁ , e₂ ⟩ ⟧N = ⟨ ⟦ e₁ ⟧N , ⟦ e₂ ⟧N ⟩

_∘N_ : NExpr T U → NExpr S T → NExpr S U
:id          ∘N e₂ = e₂
:π₁          ∘N e₂ = :π₁∘ e₂
:π₂          ∘N e₂ = :π₂∘ e₂
(:π₁∘ e₁)    ∘N e₂ = :π₁∘ (e₁ ∘N e₂)
(:π₂∘ e₁)    ∘N e₂ = :π₂∘ (e₁ ∘N e₂)
(∥ f ∥∘ e₁)  ∘N e₂ = ∥ f ∥∘ (e₁ ∘N e₂)
:⟨ e₁ , e₂ ⟩ ∘N e₃ = :⟨ e₁ ∘N e₃ , e₂ ∘N e₃ ⟩

:π₁′ : ∀ S T → NExpr (S :× T) S
:π₁′ S T = :π₁

:π₂′ : ∀ S T → NExpr (S :× T) T
:π₂′ S T = :π₂

:π₁-N : ∀ S T → NExpr (S :× T) S
:π₂-N : ∀ S T → NExpr (S :× T) T
:π₁-N ∥ A ∥      T = :π₁
:π₁-N (S₁ :× S₂) T = :⟨ :π₁-N _ _ ∘N :π₁ , :π₂-N _ _ ∘N :π₁ ⟩
:π₂-N S ∥ A ∥      = :π₂
:π₂-N S (T₁ :× T₂) = :⟨ :π₁-N _ _ ∘N :π₂ , :π₂-N _ _ ∘N :π₂ ⟩

:id-N : ∀ S → NExpr S S
:id-N ∥ A ∥    = :id
:id-N (S :× T) = :⟨ :π₁-N S T , :π₂-N S T ⟩

-- normalize _∘_ and distribute ⟨_,_⟩ and expand id, π₁ and π₂
toNExpr : Expr S T → NExpr S T
toNExpr :id          = :id-N _
toNExpr (e₁ :∘ e₂)   = toNExpr e₁ ∘N toNExpr e₂
toNExpr :π₁          = :π₁-N _ _
toNExpr :π₂          = :π₂-N _ _
toNExpr :⟨ e₁ , e₂ ⟩ = :⟨ toNExpr e₁ , toNExpr e₂ ⟩
toNExpr ∥ f ∥        = ∥ f ∥∘ :id

reduce-π₁ : NExpr S (T :× U) → NExpr S T
reduce-π₁ :π₁          = :π₁∘ :π₁
reduce-π₁ :π₂          = :π₁∘ :π₂
reduce-π₁ (:π₁∘ e)     = :π₁∘ :π₁∘ e
reduce-π₁ (:π₂∘ e)     = :π₁∘ :π₂∘ e
reduce-π₁ :⟨ e₁ , e₂ ⟩ = e₁

reduce-π₂ : NExpr S (T :× U) → NExpr S U
reduce-π₂ :π₁          = :π₂∘ :π₁
reduce-π₂ :π₂          = :π₂∘ :π₂
reduce-π₂ (:π₁∘ e)     = :π₂∘ :π₁∘ e
reduce-π₂ (:π₂∘ e)     = :π₂∘ :π₂∘ e
reduce-π₂ :⟨ e₁ , e₂ ⟩ = e₂

reduce : NExpr S T → NExpr S T
reduce :id          = :id
reduce :π₁          = :π₁
reduce :π₂          = :π₂
reduce (:π₁∘ e)     = reduce-π₁ (reduce e)
reduce (:π₂∘ e)     = reduce-π₂ (reduce e)
reduce (∥ f ∥∘ e)   = ∥ f ∥∘ reduce e
reduce :⟨ e₁ , e₂ ⟩ = :⟨ reduce e₁ , reduce e₂ ⟩

reduceN : Expr S T → NExpr S T
reduceN e = reduce (toNExpr e)

∘N-homo : (e₁ : NExpr T U) (e₂ : NExpr S T) → ⟦ e₁ ∘N e₂ ⟧N ≈ ⟦ e₁ ⟧N ∘ ⟦ e₂ ⟧N
∘N-homo :id          e₂ = ⟺ identityˡ
∘N-homo :π₁          e₂ = refl
∘N-homo :π₂          e₂ = refl
∘N-homo (:π₁∘ e₁)    e₂ = pushʳ (∘N-homo e₁ e₂)
∘N-homo (:π₂∘ e₁)    e₂ = pushʳ (∘N-homo e₁ e₂)
∘N-homo (∥ f ∥∘ e₁)  e₂ = pushʳ (∘N-homo e₁ e₂)
∘N-homo :⟨ e₁ , e₂ ⟩ e₃ = begin
  ⟨ ⟦ e₁ ∘N e₃ ⟧N , ⟦ e₂ ∘N e₃ ⟧N ⟩
    ≈⟨ ⟨⟩-cong₂ (∘N-homo e₁ e₃) (∘N-homo e₂ e₃) ⟩
  ⟨ ⟦ e₁ ⟧N ∘ ⟦ e₃ ⟧N , ⟦ e₂ ⟧N ∘ ⟦ e₃ ⟧N ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ e₁ ⟧N , ⟦ e₂ ⟧N ⟩ ∘ ⟦ e₃ ⟧N
    ∎

:π₁-N-correct : ∀ S T → ⟦ :π₁-N S T ⟧N ≈ π₁
:π₂-N-correct : ∀ S T → ⟦ :π₂-N S T ⟧N ≈ π₂
:π₁-N-correct ∥ A ∥      T = refl
:π₁-N-correct (S₁ :× S₂) T = begin
  ⟨ ⟦ :π₁-N S₁ S₂ ∘N :π₁′ (S₁ :× S₂) T ⟧N ,
    ⟦ :π₂-N S₁ S₂ ∘N :π₁′ (S₁ :× S₂) T ⟧N ⟩
    ≈⟨ ⟨⟩-cong₂ (∘N-homo (:π₁-N S₁ S₂) (:π₁′ _ T))
                (∘N-homo (:π₂-N S₁ S₂) (:π₁′ _ T)) ⟩
  ⟨ ⟦ :π₁-N S₁ S₂ ⟧N ∘ ⟦ :π₁′ (S₁ :× S₂) T ⟧N ,
    ⟦ :π₂-N S₁ S₂ ⟧N ∘ ⟦ :π₁′ (S₁ :× S₂) T ⟧N ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ :π₁-N S₁ S₂ ⟧N , ⟦ :π₂-N S₁ S₂ ⟧N ⟩ ∘ ⟦ :π₁′ (S₁ :× S₂) T ⟧N
    ≈⟨ ⟨⟩-cong₂ (:π₁-N-correct S₁ S₂) (:π₂-N-correct S₁ S₂) ⟩∘⟨refl ⟩
  ⟨ π₁ , π₂ ⟩ ∘ π₁
    ≈⟨ elimˡ η ⟩
  π₁
    ∎
:π₂-N-correct S ∥ A ∥      = refl
:π₂-N-correct S (T₁ :× T₂) = begin
  ⟨ ⟦ :π₁-N T₁ T₂ ∘N :π₂′ S (T₁ :× T₂) ⟧N ,
    ⟦ :π₂-N T₁ T₂ ∘N :π₂′ S (T₁ :× T₂) ⟧N ⟩
    ≈⟨ ⟨⟩-cong₂ (∘N-homo (:π₁-N T₁ T₂) (:π₂′ S _))
                (∘N-homo (:π₂-N T₁ T₂) (:π₂′ S _)) ⟩
  ⟨ ⟦ :π₁-N T₁ T₂ ⟧N ∘ ⟦ :π₂′ S (T₁ :× T₂) ⟧N ,
    ⟦ :π₂-N T₁ T₂ ⟧N ∘ ⟦ :π₂′ S (T₁ :× T₂) ⟧N ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ :π₁-N T₁ T₂ ⟧N , ⟦ :π₂-N T₁ T₂ ⟧N ⟩ ∘ ⟦ :π₂′ S (T₁ :× T₂) ⟧N
    ≈⟨ ⟨⟩-cong₂ (:π₁-N-correct T₁ T₂) (:π₂-N-correct T₁ T₂) ⟩∘⟨refl ⟩
  ⟨ π₁ , π₂ ⟩ ∘ π₂
    ≈⟨ elimˡ η ⟩
  π₂
    ∎

:id-N-correct : ∀ S → ⟦ :id-N S ⟧N ≈ id
:id-N-correct ∥ A ∥      = refl
:id-N-correct (S₁ :× S₂) =
  ⟨⟩-cong₂ (:π₁-N-correct S₁ S₂) (:π₂-N-correct S₁ S₂) ○ η

toNExpr-correct : ∀ (e : Expr S T) → ⟦ toNExpr e ⟧N ≈ ⟦ e ⟧
toNExpr-correct {S = S} :id          = :id-N-correct S
toNExpr-correct (e₁ :∘ e₂)           = begin
  ⟦ toNExpr e₁ ∘N toNExpr e₂ ⟧N     ≈⟨ ∘N-homo (toNExpr e₁) (toNExpr e₂) ⟩
  ⟦ toNExpr e₁ ⟧N ∘ ⟦ toNExpr e₂ ⟧N ≈⟨ toNExpr-correct e₁ ⟩∘⟨ toNExpr-correct e₂ ⟩
  ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧                   ∎
toNExpr-correct {S = S :× T} {S} :π₁ = :π₁-N-correct S T
toNExpr-correct {S = S :× T} {T} :π₂ = :π₂-N-correct S T
toNExpr-correct :⟨ e₁ , e₂ ⟩         = ⟨⟩-cong₂ (toNExpr-correct e₁) (toNExpr-correct e₂)
toNExpr-correct ∥ f ∥                = identityʳ

reduce-π₁-correct : (e : NExpr S (T :× U)) → ⟦ reduce-π₁ e ⟧N ≈ π₁ ∘ ⟦ e ⟧N
reduce-π₁-correct :π₁          = refl
reduce-π₁-correct :π₂          = refl
reduce-π₁-correct (:π₁∘ e)     = refl
reduce-π₁-correct (:π₂∘ e)     = refl
reduce-π₁-correct :⟨ e₁ , e₂ ⟩ = ⟺ project₁

reduce-π₂-correct : (e : NExpr S (T :× U)) → ⟦ reduce-π₂ e ⟧N ≈ π₂ ∘ ⟦ e ⟧N
reduce-π₂-correct :π₁          = refl
reduce-π₂-correct :π₂          = refl
reduce-π₂-correct (:π₁∘ e)     = refl
reduce-π₂-correct (:π₂∘ e)     = refl
reduce-π₂-correct :⟨ e₁ , e₂ ⟩ = ⟺ project₂

reduce-correct : (e : NExpr S T) → ⟦ reduce e ⟧N ≈ ⟦ e ⟧N
reduce-correct :id          = refl
reduce-correct :π₁          = refl
reduce-correct :π₂          = refl
reduce-correct (:π₁∘ e)     =
  reduce-π₁-correct (reduce e) ○ ∘-resp-≈ʳ (reduce-correct e)
reduce-correct (:π₂∘ e)     =
  reduce-π₂-correct (reduce e) ○ ∘-resp-≈ʳ (reduce-correct e)
reduce-correct (∥ f ∥∘ e)   = ∘-resp-≈ʳ (reduce-correct e)
reduce-correct :⟨ e₁ , e₂ ⟩ = ⟨⟩-cong₂ (reduce-correct e₁) (reduce-correct e₂)

reduceN-correct : (e : Expr S T) → ⟦ reduceN e ⟧N ≈ ⟦ e ⟧
reduceN-correct e = reduce-correct (toNExpr e) ○ toNExpr-correct e

solve : (e₁ e₂ : Expr S T) → ⟦ reduceN e₁ ⟧N ≈ ⟦ reduceN e₂ ⟧N → ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
solve e₁ e₂ eq = begin
  ⟦ e₁ ⟧          ≈˘⟨ reduceN-correct e₁ ⟩
  ⟦ reduceN e₁ ⟧N ≈⟨ eq ⟩
  ⟦ reduceN e₂ ⟧N ≈⟨ reduceN-correct e₂ ⟩
  ⟦ e₂ ⟧          ∎

-- combinators
-- TODO add more
:swap : Expr (S :× T) (T :× S)
:swap = :⟨ :π₂ , :π₁ ⟩

:assocˡ : Expr ((S :× T) :× U) (S :× T :× U)
:assocˡ = :⟨ :π₁ :∘ :π₁ , :⟨ :π₂ :∘ :π₁ , :π₂ ⟩ ⟩

:assocʳ : Expr (S :× T :× U) ((S :× T) :× U)
:assocʳ = :⟨ :⟨ :π₁ , :π₁ :∘ :π₂ ⟩ , :π₂ :∘ :π₂ ⟩

infixr 8 _:⁂_

_:⁂_ : Expr S T → Expr U V → Expr (S :× U) (T :× V)
e₁ :⁂ e₂ = :⟨ e₁ :∘ :π₁ , e₂ :∘ :π₂ ⟩

-- Example
private
  swap∘swap≈id : ∀ {A B} → swap {A}{B} ∘ swap {B}{A} ≈ id
  swap∘swap≈id {A} {B} =
    solve (:swap {S = ∥ A ∥} {T = ∥ B ∥} :∘ :swap) :id refl

  assocʳ∘assocˡ≈id : ∀ {A B C} → assocʳ {A}{B}{C} ∘ assocˡ {A}{B}{C} ≈ id
  assocʳ∘assocˡ≈id {A} {B} {C} =
    solve (:assocʳ {S = ∥ A ∥} {T = ∥ B ∥} {U = ∥ C ∥} :∘ :assocˡ) :id refl

  module _ {A B C D E F} {f : B ⇒ C} (f′ : A ⇒ B) {g : E ⇒ F} {g′ : D ⇒ E} where
    ⁂-∘ : (f ⁂ g) ∘ (f′ ⁂ g′) ≈ (f ∘ f′) ⁂ (g ∘ g′)
    ⁂-∘ = solve lhs rhs refl
      where
      lhs = (∥ f ∥ :⁂ ∥ g ∥) :∘ (∥ f′ ∥ :⁂ ∥ g′ ∥)
      rhs = (∥ f ∥ :∘ ∥ f′ ∥) :⁂ (∥ g ∥ :∘ ∥ g′ ∥)

  module _ {A B C D} where
    pentagon′ : (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ≈
                assocˡ ∘ assocˡ {A = A × B} {B = C} {C = D}
    pentagon′ = solve lhs rhs refl
      where
      lhs = (:id :⁂ :assocˡ) :∘ :assocˡ :∘ (:assocˡ :⁂ :id)
      rhs = :assocˡ :∘ :assocˡ {S = ∥ A ∥ :× ∥ B ∥} {T = ∥ C ∥} {U = ∥ D ∥}
