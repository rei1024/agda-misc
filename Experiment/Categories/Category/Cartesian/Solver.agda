-- Solver for cartesian category

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Cartesian

module Experiment.Categories.Category.Cartesian.Solver
  {o ℓ e} {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) where

open import Level
open import Relation.Binary using (Rel)

import Categories.Morphism.Reasoning as MR

open Category 𝒞
open Cartesian cartesian
open HomReasoning
open MR 𝒞

private
  variable
    A B C : Obj

infixr 9 _:∘_
infixr 7 _:×_
infix 11 :⟨_,_⟩

data Sig : Set o where
  ∥_∥ : Obj → Sig
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
  -- TODO
  -- ∥⟨_⟩∥ : C ⇒ (A × B) → Expr C (A × B)
  -- ∥ !∥ : A ⇒ ⊤ → Expr A ⊤
  -- :! = ∥ ! !∥

data LExpr : Rel Sig (o ⊔ ℓ) where
  -- TODO change to :id : LExpr ∥ A ∥ ∥ A ∥
  :id    : LExpr S S
  :π₁∘_  : LExpr S (T :× U) → LExpr S T
  :π₂∘_  : LExpr S (T :× U) → LExpr S U
  ∥_∥∘_  : B ⇒ C → LExpr S ∥ B ∥ → LExpr S ∥ C ∥
  :⟨_,_⟩ : LExpr U S → LExpr U T → LExpr U (S :× T)

⟦_⟧ : Expr S T → ⟦ S ⟧Sig ⇒ ⟦ T ⟧Sig
⟦ :id          ⟧ = id
⟦ e₁ :∘ e₂     ⟧ = ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧
⟦ :π₁          ⟧ = π₁
⟦ :π₂          ⟧ = π₂
⟦ :⟨ e₁ , e₂ ⟩ ⟧ = ⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩
⟦ ∥ f ∥        ⟧ = f

⟦_⟧L : LExpr S T → ⟦ S ⟧Sig ⇒ ⟦ T ⟧Sig
⟦ :id          ⟧L = id
⟦ :π₁∘ e       ⟧L = π₁ ∘ ⟦ e ⟧L
⟦ :π₂∘ e       ⟧L = π₂ ∘ ⟦ e ⟧L
⟦ ∥ f ∥∘ e     ⟧L = f ∘ ⟦ e ⟧L
⟦ :⟨ e₁ , e₂ ⟩ ⟧L = ⟨ ⟦ e₁ ⟧L , ⟦ e₂ ⟧L ⟩

_∘L_ : LExpr T U → LExpr S T → LExpr S U
:id          ∘L e₂ = e₂
(:π₁∘ e₁)    ∘L e₂ = :π₁∘ (e₁ ∘L e₂)
(:π₂∘ e₁)    ∘L e₂ = :π₂∘ (e₁ ∘L e₂)
(∥ x ∥∘ e₁)  ∘L e₂ = ∥ x ∥∘ (e₁ ∘L e₂)
:⟨ e₁ , e₂ ⟩ ∘L e₃ = :⟨ e₁ ∘L e₃ , e₂ ∘L e₃ ⟩

:π₁-L′ : ∀ S T → LExpr (S :× T) S
:π₁-L′ S T = :π₁∘ :id

:π₂-L′ : ∀ S T → LExpr (S :× T) T
:π₂-L′ S T = :π₂∘ :id

:π₁-L : ∀ S T → LExpr (S :× T) S
:π₂-L : ∀ S T → LExpr (S :× T) T
:π₁-L ∥ A ∥      T = :π₁-L′ _ _
:π₁-L (S₁ :× S₂) T = :⟨ :π₁-L _ _ ∘L :π₁-L′ _ _ , :π₂-L _ _ ∘L :π₁-L′ _ _ ⟩
:π₂-L S ∥ A ∥      = :π₂-L′ _ _
:π₂-L S (T₁ :× T₂) = :⟨ :π₁-L _ _ ∘L :π₂-L′ _ _ , :π₂-L _ _ ∘L :π₂-L′ _ _ ⟩

:id-L : ∀ S → LExpr S S
:id-L ∥ A ∥    = :id
:id-L (S :× T) = :⟨ :π₁-L S T , :π₂-L S T ⟩

-- normalize _∘_ and distribute ⟨_,_⟩ and expand id, π₁ and π₂
toLExpr : Expr S T → LExpr S T
toLExpr :id          = :id-L _
toLExpr (e₁ :∘ e₂)   = toLExpr e₁ ∘L toLExpr e₂
toLExpr :π₁          = :π₁-L _ _
toLExpr :π₂          = :π₂-L _ _
toLExpr :⟨ e₁ , e₂ ⟩ = :⟨ toLExpr e₁ , toLExpr e₂ ⟩
toLExpr ∥ f ∥        = ∥ f ∥∘ :id

reduce-π₁ : LExpr S (T :× U) → LExpr S T
reduce-π₁ :id          = :π₁∘ :id
reduce-π₁ (:π₁∘ e)     = :π₁∘ :π₁∘ e
reduce-π₁ (:π₂∘ e)     = :π₁∘ :π₂∘ e
reduce-π₁ :⟨ e₁ , e₂ ⟩ = e₁

reduce-π₂ : LExpr S (T :× U) → LExpr S U
reduce-π₂ :id          = :π₂∘ :id
reduce-π₂ (:π₁∘ e)     = :π₂∘ :π₁∘ e
reduce-π₂ (:π₂∘ e)     = :π₂∘ :π₂∘ e
reduce-π₂ :⟨ e₁ , e₂ ⟩ = e₂

reduce : LExpr S T → LExpr S T
reduce :id          = :id
reduce (:π₁∘ e)     = reduce-π₁ (reduce e)
reduce (:π₂∘ e)     = reduce-π₂ (reduce e)
reduce (∥ f ∥∘ e)   = ∥ f ∥∘ reduce e
reduce :⟨ e₁ , e₂ ⟩ = :⟨ reduce e₁ , reduce e₂ ⟩

reduceL : Expr S T → LExpr S T
reduceL e = reduce (toLExpr e)

∘L-homo : (e₁ : LExpr T U) (e₂ : LExpr S T) → ⟦ e₁ ∘L e₂ ⟧L ≈ ⟦ e₁ ⟧L ∘ ⟦ e₂ ⟧L
∘L-homo :id          e₂ = ⟺ identityˡ
∘L-homo (:π₁∘ e₁)    e₂ = pushʳ (∘L-homo e₁ e₂)
∘L-homo (:π₂∘ e₁)    e₂ = pushʳ (∘L-homo e₁ e₂)
∘L-homo (∥ f ∥∘ e₁)  e₂ = pushʳ (∘L-homo e₁ e₂)
∘L-homo :⟨ e₁ , e₂ ⟩ e₃ = begin
  ⟨ ⟦ e₁ ∘L e₃ ⟧L , ⟦ e₂ ∘L e₃ ⟧L ⟩
    ≈⟨ ⟨⟩-cong₂ (∘L-homo e₁ e₃) (∘L-homo e₂ e₃) ⟩
  ⟨ ⟦ e₁ ⟧L ∘ ⟦ e₃ ⟧L , ⟦ e₂ ⟧L ∘ ⟦ e₃ ⟧L ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ e₁ ⟧L , ⟦ e₂ ⟧L ⟩ ∘ ⟦ e₃ ⟧L
    ∎

:π₁-L-correct : ∀ S T → ⟦ :π₁-L S T ⟧L ≈ π₁
:π₂-L-correct : ∀ S T → ⟦ :π₂-L S T ⟧L ≈ π₂
:π₁-L-correct ∥ A ∥      T = identityʳ
:π₁-L-correct (S₁ :× S₂) T = begin
  ⟨ ⟦ :π₁-L S₁ S₂ ∘L :π₁-L′ (S₁ :× S₂) T ⟧L ,
    ⟦ :π₂-L S₁ S₂ ∘L :π₁-L′ (S₁ :× S₂) T ⟧L ⟩
    ≈⟨ ⟨⟩-cong₂ (∘L-homo (:π₁-L S₁ S₂) (:π₁-L′ _ T))
                (∘L-homo (:π₂-L S₁ S₂) (:π₁-L′ _ T)) ⟩
  ⟨ ⟦ :π₁-L S₁ S₂ ⟧L ∘ ⟦ :π₁-L′ (S₁ :× S₂) T ⟧L ,
    ⟦ :π₂-L S₁ S₂ ⟧L ∘ ⟦ :π₁-L′ (S₁ :× S₂) T ⟧L ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ :π₁-L S₁ S₂ ⟧L , ⟦ :π₂-L S₁ S₂ ⟧L ⟩ ∘ ⟦ :π₁-L′ (S₁ :× S₂) T ⟧L
    ≈⟨ ⟨⟩-cong₂ (:π₁-L-correct S₁ S₂) (:π₂-L-correct S₁ S₂) ⟩∘⟨ identityʳ ⟩
  ⟨ π₁ , π₂ ⟩ ∘ π₁
    ≈⟨ elimˡ η ⟩
  π₁
    ∎
:π₂-L-correct S ∥ A ∥      = identityʳ
:π₂-L-correct S (T₁ :× T₂) = begin
  ⟨ ⟦ :π₁-L T₁ T₂ ∘L :π₂-L′ S (T₁ :× T₂) ⟧L ,
    ⟦ :π₂-L T₁ T₂ ∘L :π₂-L′ S (T₁ :× T₂) ⟧L ⟩
    ≈⟨ ⟨⟩-cong₂ (∘L-homo (:π₁-L T₁ T₂) (:π₂-L′ S _))
                (∘L-homo (:π₂-L T₁ T₂) (:π₂-L′ S _)) ⟩
  ⟨ ⟦ :π₁-L T₁ T₂ ⟧L ∘ ⟦ :π₂-L′ S (T₁ :× T₂) ⟧L ,
    ⟦ :π₂-L T₁ T₂ ⟧L ∘ ⟦ :π₂-L′ S (T₁ :× T₂) ⟧L ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ :π₁-L T₁ T₂ ⟧L , ⟦ :π₂-L T₁ T₂ ⟧L ⟩ ∘ ⟦ :π₂-L′ S (T₁ :× T₂) ⟧L
    ≈⟨ ⟨⟩-cong₂ (:π₁-L-correct T₁ T₂) (:π₂-L-correct T₁ T₂) ⟩∘⟨ identityʳ ⟩
  ⟨ π₁ , π₂ ⟩ ∘ π₂
    ≈⟨ elimˡ η ⟩
  π₂
    ∎

:id-L-correct : ∀ S → ⟦ :id-L S ⟧L ≈ id
:id-L-correct ∥ A ∥      = refl
:id-L-correct (S₁ :× S₂) =
  ⟨⟩-cong₂ (:π₁-L-correct S₁ S₂) (:π₂-L-correct S₁ S₂) ○ η

toLExpr-correct : ∀ (e : Expr S T) → ⟦ toLExpr e ⟧L ≈ ⟦ e ⟧
toLExpr-correct {S = S} :id          = :id-L-correct S
toLExpr-correct (e₁ :∘ e₂)           = begin
  ⟦ toLExpr e₁ ∘L toLExpr e₂ ⟧L     ≈⟨ ∘L-homo (toLExpr e₁) (toLExpr e₂) ⟩
  ⟦ toLExpr e₁ ⟧L ∘ ⟦ toLExpr e₂ ⟧L ≈⟨ toLExpr-correct e₁ ⟩∘⟨ toLExpr-correct e₂ ⟩
  ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧                   ∎
toLExpr-correct {S = S :× T} {S} :π₁ = :π₁-L-correct S T
toLExpr-correct {S = S :× T} {T} :π₂ = :π₂-L-correct S T
toLExpr-correct :⟨ e₁ , e₂ ⟩         = ⟨⟩-cong₂ (toLExpr-correct e₁) (toLExpr-correct e₂)
toLExpr-correct ∥ f ∥                = identityʳ

reduce-π₁-correct : (e : LExpr S (T :× U)) → ⟦ reduce-π₁ e ⟧L ≈ π₁ ∘ ⟦ e ⟧L
reduce-π₁-correct :id          = refl
reduce-π₁-correct (:π₁∘ e)     = refl
reduce-π₁-correct (:π₂∘ e)     = refl
reduce-π₁-correct :⟨ e₁ , e₂ ⟩ = ⟺ project₁

reduce-π₂-correct : (e : LExpr S (T :× U)) → ⟦ reduce-π₂ e ⟧L ≈ π₂ ∘ ⟦ e ⟧L
reduce-π₂-correct :id          = refl
reduce-π₂-correct (:π₁∘ e)     = refl
reduce-π₂-correct (:π₂∘ e)     = refl
reduce-π₂-correct :⟨ e₁ , e₂ ⟩ = ⟺ project₂

reduce-correct : (e : LExpr S T) → ⟦ reduce e ⟧L ≈ ⟦ e ⟧L
reduce-correct :id          = refl
reduce-correct (:π₁∘ e)     =
  reduce-π₁-correct (reduce e) ○ ∘-resp-≈ʳ (reduce-correct e)
reduce-correct (:π₂∘ e)     =
  reduce-π₂-correct (reduce e) ○ ∘-resp-≈ʳ (reduce-correct e)
reduce-correct (∥ f ∥∘ e)   = ∘-resp-≈ʳ (reduce-correct e)
reduce-correct :⟨ e₁ , e₂ ⟩ = ⟨⟩-cong₂ (reduce-correct e₁) (reduce-correct e₂)

reduceL-correct : (e : Expr S T) → ⟦ reduceL e ⟧L ≈ ⟦ e ⟧
reduceL-correct e = reduce-correct (toLExpr e) ○ toLExpr-correct e

solve : (e₁ e₂ : Expr S T) → ⟦ reduceL e₁ ⟧L ≈ ⟦ reduceL e₂ ⟧L → ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
solve e₁ e₂ eq = begin
  ⟦ e₁ ⟧          ≈˘⟨ reduceL-correct e₁ ⟩
  ⟦ reduceL e₁ ⟧L ≈⟨ eq ⟩
  ⟦ reduceL e₂ ⟧L ≈⟨ reduceL-correct e₂ ⟩
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
