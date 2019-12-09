-- Solver for cartesian category
-- Normalisation is based on https://arxiv.org/abs/math/9911059

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Cartesian

module Experiment.Categories.Solver.Category.Cartesian
  {o ℓ e} {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) where

open import Level
open import Relation.Binary using (Rel; REL)

import Categories.Morphism.Reasoning as MR

open Category 𝒞
open Cartesian cartesian
open HomReasoning
open MR 𝒞

private
  variable
    A B C D E F : Obj

infixr 9 _:∘_
infixr 7 _:×_
infix 11 :⟨_,_⟩

data Sig : Set o where
  ∥_∥  : Obj → Sig
  :⊤   : Sig
  _:×_ : Sig → Sig → Sig

⟦_⟧Sig : Sig → Obj
⟦ ∥ A ∥    ⟧Sig = A
⟦ :⊤       ⟧Sig = ⊤
⟦ S₁ :× S₂ ⟧Sig = ⟦ S₁ ⟧Sig × ⟦ S₂ ⟧Sig

private
  variable
    S T U V : Sig

-- Expression for cartesian category
data Expr : Rel Sig (o ⊔ ℓ) where
  :id    : Expr S S
  _:∘_   : Expr T U → Expr S T → Expr S U
  :π₁    : Expr (S :× T) S
  :π₂    : Expr (S :× T) T
  :⟨_,_⟩ : Expr U S → Expr U T → Expr U (S :× T)
  ∥_∥    : A ⇒ B → Expr ∥ A ∥ ∥ B ∥
  ∥_!∥   : A ⇒ ⊤ → Expr ∥ A ∥ :⊤

-- Atomised expression
data AExpr : REL Sig Obj (o ⊔ ℓ) where
  :π₁   : AExpr (∥ A ∥ :× T) A
  :π₂   : AExpr (S :× ∥ B ∥) B
  _:∘π₁ : AExpr S A → AExpr (S :× T) A
  _:∘π₂ : AExpr T A → AExpr (S :× T) A

-- Normalised expression
data NExpr : Rel Sig (o ⊔ ℓ) where
  :id    : NExpr ∥ A ∥ ∥ A ∥
  :!N   : NExpr S :⊤
  ⟪_⟫    : AExpr S A → NExpr S ∥ A ∥
  :⟨_,_⟩ : NExpr U S → NExpr U T → NExpr U (S :× T)
  ∥_∥∘_  : B ⇒ C → NExpr S ∥ B ∥ → NExpr S ∥ C ∥

-- Semantics
⟦_⟧ : Expr S T → ⟦ S ⟧Sig ⇒ ⟦ T ⟧Sig
⟦ :id          ⟧ = id
⟦ e₁ :∘ e₂     ⟧ = ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧
⟦ :π₁          ⟧ = π₁
⟦ :π₂          ⟧ = π₂
⟦ :⟨ e₁ , e₂ ⟩ ⟧ = ⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩
⟦ ∥ f ∥        ⟧ = f
⟦ ∥ g !∥       ⟧ = g

⟦_⟧A : AExpr S B → ⟦ S ⟧Sig ⇒ B
⟦ :π₁      ⟧A = π₁
⟦ :π₂      ⟧A = π₂
⟦ e :∘π₁   ⟧A = ⟦ e ⟧A ∘ π₁
⟦ e :∘π₂   ⟧A = ⟦ e ⟧A ∘ π₂

⟦_⟧N : NExpr S T → ⟦ S ⟧Sig ⇒ ⟦ T ⟧Sig
⟦ :id          ⟧N = id
⟦ :!N          ⟧N = !
⟦ ⟪ e ⟫        ⟧N = ⟦ e ⟧A
⟦ :⟨ e₁ , e₂ ⟩ ⟧N = ⟨ ⟦ e₁ ⟧N , ⟦ e₂ ⟧N ⟩
⟦ ∥ f ∥∘ e     ⟧N = f ∘ ⟦ e ⟧N

_∘AN_ : AExpr T A → NExpr S T → NExpr S ∥ A ∥
:π₁       ∘AN :⟨ e₂ , e₃ ⟩ = e₂
:π₂       ∘AN :⟨ e₂ , e₃ ⟩ = e₃
(e₁ :∘π₁) ∘AN :⟨ e₂ , e₃ ⟩ = e₁ ∘AN e₂
(e₁ :∘π₂) ∘AN :⟨ e₂ , e₃ ⟩ = e₁ ∘AN e₃

_∘π₁N : NExpr S U → NExpr (S :× T) U
:id          ∘π₁N = ⟪ :π₁ ⟫
:!N          ∘π₁N = :!N
⟪ e ⟫        ∘π₁N = ⟪ e :∘π₁ ⟫
:⟨ e₁ , e₂ ⟩ ∘π₁N = :⟨ e₁ ∘π₁N , e₂ ∘π₁N ⟩
(∥ f ∥∘ e)   ∘π₁N = ∥ f ∥∘ (e ∘π₁N)

_∘π₂N : NExpr T U → NExpr (S :× T) U
:id          ∘π₂N = ⟪ :π₂ ⟫
:!N          ∘π₂N = :!N
⟪ e ⟫        ∘π₂N = ⟪ e :∘π₂ ⟫
:⟨ e₁ , e₂ ⟩ ∘π₂N = :⟨ e₁ ∘π₂N , e₂ ∘π₂N ⟩
(∥ f ∥∘ e)   ∘π₂N = ∥ f ∥∘ (e ∘π₂N)

_∘N_ : NExpr T U → NExpr S T → NExpr S U
:id          ∘N e₂ = e₂
:!N          ∘N e₂ = :!N
⟪ e₁ ⟫       ∘N e₂ = e₁ ∘AN e₂
:⟨ e₁ , e₂ ⟩ ∘N e₃ = :⟨ e₁ ∘N e₃ , e₂ ∘N e₃ ⟩
(∥ f ∥∘ e₁)  ∘N e₂ = ∥ f ∥∘ (e₁ ∘N e₂)

π₁N : ∀ S T → NExpr (S :× T) S
π₂N : ∀ S T → NExpr (S :× T) T
π₁N ∥ _ ∥      T = ⟪ :π₁ ⟫
π₁N :⊤         T = :!N
π₁N (S₁ :× S₂) T = :⟨ (π₁N S₁ S₂) ∘π₁N , (π₂N S₁ S₂) ∘π₁N ⟩
π₂N S ∥ _ ∥      = ⟪ :π₂ ⟫
π₂N S :⊤         = :!N
π₂N S (T₁ :× T₂) = :⟨ (π₁N T₁ T₂) ∘π₂N , (π₂N T₁ T₂) ∘π₂N ⟩

idN : ∀ S → NExpr S S
idN ∥ _ ∥    = :id
idN :⊤       = :!N
idN (S :× T) = :⟨ π₁N S T , π₂N S T ⟩

-- expand id, π₁ and π₂
normalise : Expr S T → NExpr S T
normalise :id          = idN _
normalise (e₁ :∘ e₂)   = normalise e₁ ∘N normalise e₂
normalise :π₁          = π₁N _ _
normalise :π₂          = π₂N _ _
normalise :⟨ e₁ , e₂ ⟩ = :⟨ normalise e₁ , normalise e₂ ⟩
normalise ∥ f ∥        = ∥ f ∥∘ :id
normalise ∥ g !∥       = :!N

∘AN-homo : (e₁ : AExpr T A) (e₂ : NExpr S T) → ⟦ e₁ ∘AN e₂ ⟧N ≈ ⟦ e₁ ⟧A ∘ ⟦ e₂ ⟧N
∘AN-homo :π₁       :⟨ e₂ , e₃ ⟩ = ⟺ project₁
∘AN-homo :π₂       :⟨ e₂ , e₃ ⟩ = ⟺ project₂
∘AN-homo (e₁ :∘π₁) :⟨ e₂ , e₃ ⟩ = ∘AN-homo e₁ e₂ ○ pushʳ (⟺ project₁)
∘AN-homo (e₁ :∘π₂) :⟨ e₂ , e₃ ⟩ = ∘AN-homo e₁ e₃ ○ pushʳ (⟺ project₂)

∘N-homo : (e₁ : NExpr T U) (e₂ : NExpr S T) → ⟦ e₁ ∘N e₂ ⟧N ≈ ⟦ e₁ ⟧N ∘ ⟦ e₂ ⟧N
∘N-homo :id          e₂ = ⟺ identityˡ
∘N-homo :!N          e₂ = !-unique _
∘N-homo ⟪ e₁ ⟫       e₂ = ∘AN-homo e₁ e₂
∘N-homo :⟨ e₁ , e₂ ⟩ e₃ = ⟨⟩-cong₂ (∘N-homo e₁ e₃) (∘N-homo e₂ e₃) ○ ⟺ ⟨⟩∘
∘N-homo (∥ f ∥∘ e₁)  e₂ = pushʳ (∘N-homo e₁ e₂)

∘π₁N-homo : ∀ (e : NExpr S U) → ⟦ (_∘π₁N {T = T}) e ⟧N ≈ ⟦ e ⟧N ∘ π₁
∘π₁N-homo :id          = ⟺ identityˡ
∘π₁N-homo :!N          = !-unique _
∘π₁N-homo ⟪ e ⟫        = refl
∘π₁N-homo :⟨ e₁ , e₂ ⟩ = ⟨⟩-cong₂ (∘π₁N-homo e₁) (∘π₁N-homo e₂) ○ ⟺ ⟨⟩∘
∘π₁N-homo (∥ f ∥∘ e)   = pushʳ (∘π₁N-homo e)

∘π₂N-homo : ∀ (e : NExpr T U) → ⟦ (_∘π₂N {S = S}) e ⟧N ≈ ⟦ e ⟧N ∘ π₂
∘π₂N-homo :id          = ⟺ identityˡ
∘π₂N-homo :!N          = !-unique _
∘π₂N-homo ⟪ e ⟫        = refl
∘π₂N-homo :⟨ e₁ , e₂ ⟩ = ⟨⟩-cong₂ (∘π₂N-homo e₁) (∘π₂N-homo e₂) ○ ⟺ ⟨⟩∘
∘π₂N-homo (∥ f ∥∘ e)   = pushʳ (∘π₂N-homo e)

private
  ∘π₁N′ : ∀ S T → NExpr S U → NExpr (S :× T) U
  ∘π₁N′ _ _ = _∘π₁N
  ∘π₂N′ : ∀ S T → NExpr T U → NExpr (S :× T) U
  ∘π₂N′ _ _ = _∘π₂N

π₁N-homo : ∀ S T → ⟦ π₁N S T ⟧N ≈ π₁
π₂N-homo : ∀ S T → ⟦ π₂N S T ⟧N ≈ π₂
π₁N-homo ∥ A ∥      T = refl
π₁N-homo :⊤         T = !-unique _
π₁N-homo (S₁ :× S₂) T = begin
  ⟨ ⟦ ∘π₁N′ (S₁ :× S₂) T (π₁N S₁ S₂) ⟧N , ⟦ ∘π₁N′ (S₁ :× S₂) T (π₂N S₁ S₂) ⟧N ⟩
    ≈⟨ ⟨⟩-cong₂ (∘π₁N-homo (π₁N S₁ S₂)) (∘π₁N-homo (π₂N S₁ S₂)) ⟩
  ⟨ ⟦ π₁N S₁ S₂ ⟧N ∘ π₁ , ⟦ π₂N S₁ S₂ ⟧N ∘ π₁ ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ π₁N S₁ S₂ ⟧N , ⟦ π₂N S₁ S₂ ⟧N ⟩ ∘ π₁
    ≈⟨ ⟨⟩-cong₂ (π₁N-homo S₁ S₂) (π₂N-homo S₁ S₂) ⟩∘⟨refl ⟩
  ⟨ π₁ , π₂ ⟩ ∘ π₁
    ≈⟨ elimˡ η ⟩
  π₁
    ∎
π₂N-homo S ∥ A ∥      = refl
π₂N-homo S :⊤         = !-unique _
π₂N-homo S (T₁ :× T₂) = begin
  ⟨ ⟦ ∘π₂N′ S (T₁ :× T₂) (π₁N T₁ T₂) ⟧N , ⟦ ∘π₂N′ S (T₁ :× T₂) (π₂N T₁ T₂) ⟧N ⟩
    ≈⟨ ⟨⟩-cong₂ (∘π₂N-homo (π₁N T₁ T₂)) (∘π₂N-homo (π₂N T₁ T₂)) ⟩
  ⟨ ⟦ π₁N T₁ T₂ ⟧N ∘ π₂ , ⟦ π₂N T₁ T₂ ⟧N ∘ π₂ ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ π₁N T₁ T₂ ⟧N , ⟦ π₂N T₁ T₂ ⟧N ⟩ ∘ π₂
    ≈⟨ ⟨⟩-cong₂ (π₁N-homo T₁ T₂) (π₂N-homo T₁ T₂) ⟩∘⟨refl ⟩
  ⟨ π₁ , π₂ ⟩ ∘ π₂
    ≈⟨ elimˡ η ⟩
  π₂
    ∎

idN-homo : ∀ S → ⟦ idN S ⟧N ≈ id
idN-homo ∥ _ ∥      = refl
idN-homo :⊤         = !-unique id
idN-homo (S₁ :× S₂) = ⟨⟩-cong₂ (π₁N-homo S₁ S₂) (π₂N-homo S₁ S₂) ○ η

correct : ∀ (e : Expr S T) → ⟦ normalise e ⟧N ≈ ⟦ e ⟧
correct {S} :id          = idN-homo S
correct (e₁ :∘ e₂)       = begin
  ⟦ normalise e₁ ∘N normalise e₂ ⟧N     ≈⟨ ∘N-homo (normalise e₁) (normalise e₂) ⟩
  ⟦ normalise e₁ ⟧N ∘ ⟦ normalise e₂ ⟧N ≈⟨ correct e₁ ⟩∘⟨ correct e₂ ⟩
  ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧                       ∎
correct {S :× T} {S} :π₁ = π₁N-homo S T
correct {S :× T} {T} :π₂ = π₂N-homo S T
correct :⟨ e₁ , e₂ ⟩     = ⟨⟩-cong₂ (correct e₁) (correct e₂)
correct ∥ f ∥            = identityʳ
correct ∥ g !∥           = !-unique g

solve : (e₁ e₂ : Expr S T) →
        ⟦ normalise e₁ ⟧N ≈ ⟦ normalise e₂ ⟧N → ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
solve e₁ e₂ eq = begin
  ⟦ e₁ ⟧            ≈˘⟨ correct e₁ ⟩
  ⟦ normalise e₁ ⟧N ≈⟨ eq ⟩
  ⟦ normalise e₂ ⟧N ≈⟨ correct e₂ ⟩
  ⟦ e₂ ⟧            ∎

∥-∥ : ∀ {f : A ⇒ B} → Expr ∥ A ∥ ∥ B ∥
∥-∥ {f = f} = ∥ f ∥

-- Combinators
:! : Expr ∥ A ∥ :⊤
:! = ∥ ! !∥

:swap : Expr (S :× T) (T :× S)
:swap = :⟨ :π₂ , :π₁ ⟩

:assocˡ : Expr ((S :× T) :× U) (S :× T :× U)
:assocˡ = :⟨ :π₁ :∘ :π₁ , :⟨ :π₂ :∘ :π₁ , :π₂ ⟩ ⟩

:assocʳ : Expr (S :× T :× U) ((S :× T) :× U)
:assocʳ = :⟨ :⟨ :π₁ , :π₁ :∘ :π₂ ⟩ , :π₂ :∘ :π₂ ⟩

infixr 8 _:⁂_

_:⁂_ : Expr S T → Expr U V → Expr (S :× U) (T :× V)
e₁ :⁂ e₂ = :⟨ e₁ :∘ :π₁ , e₂ :∘ :π₂ ⟩

:first : Expr S T → Expr (S :× U) (T :× U)
:first e = e :⁂ :id

:second : Expr T U → Expr (S :× T) (S :× U)
:second e = :id :⁂ e
