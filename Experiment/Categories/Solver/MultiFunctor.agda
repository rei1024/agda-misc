-- Solver for functors

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor renaming (id to idF)

module Experiment.Categories.Solver.MultiFunctor {o ℓ e} where

import Categories.Morphism.Reasoning as MR

open import Level
open import Relation.Binary using (Rel)

infixr 9 _:∘_

data Expr : (𝒞 : Category o ℓ e) → Rel (Category.Obj 𝒞) (suc (o ⊔ ℓ ⊔ e)) where
  :id  : ∀ {𝒞 A} → Expr 𝒞 A A
  _:∘_ : ∀ {𝒞 A B C} → Expr 𝒞 B C → Expr 𝒞 A B → Expr 𝒞 A C
  :F₁  : ∀ {𝒞 𝒟} (F : Functor 𝒟 𝒞) {A B} →
         Expr 𝒟 A B → Expr 𝒞 (Functor.F₀ F A) (Functor.F₀ F B)
  ∥_∥  : ∀ {𝒞 A B} → 𝒞 [ A , B ] → Expr 𝒞 A B

_⟦_⟧ : ∀ 𝒞 {A B} → Expr 𝒞 A B → 𝒞 [ A , B ]
𝒞 ⟦ :id ⟧      = Category.id 𝒞
𝒞 ⟦ e₁ :∘ e₂ ⟧ = 𝒞 [ 𝒞 ⟦ e₁ ⟧ ∘ 𝒞 ⟦ e₂ ⟧ ]
𝒞 ⟦ :F₁ F e ⟧  = Functor.F₁ F (_ ⟦ e ⟧)
𝒞 ⟦ ∥ f ∥ ⟧    = f

N∘ : ∀ (𝒞 𝒟 : Category o ℓ e) (F : Functor 𝒟 𝒞) {A B C} →
     Expr 𝒟 B C → 𝒞 [ A , Functor.F₀ F B ] → 𝒞 [ A , Functor.F₀ F C ]
N∘ 𝒞 𝒟 F :id                g = g
N∘ 𝒞 𝒟 F (e₁ :∘ e₂)         g = N∘ 𝒞 𝒟 F e₁ (N∘ 𝒞 𝒟 F e₂ g)
N∘ 𝒞 𝒟 F (:F₁ {𝒟 = ℰ} G e) g = N∘ 𝒞 ℰ (F ∘F G) e g
N∘ 𝒞 𝒟 F ∥ f ∥              g = 𝒞 [ Functor.F₁ F f ∘ g ]

_⟦_⟧N : ∀ 𝒞 {A B} → Expr 𝒞 A B → 𝒞 [ A , B ]
𝒞 ⟦ e ⟧N = N∘ 𝒞 𝒞 idF e (Category.id 𝒞)

N∘≈⟦⟧ : ∀ 𝒞 𝒟 (F : Functor 𝒟 𝒞) {A B C}
        (e : Expr 𝒟 B C) (g : 𝒞 [ A , Functor.F₀ F B ]) →
        𝒞 [ N∘ 𝒞 𝒟 F e g ≈ 𝒞 [ Functor.F₁ F (𝒟 ⟦ e ⟧) ∘ g ] ]
N∘≈⟦⟧ 𝒞 𝒟 F :id                g = begin
  g                       ≈˘⟨ identityˡ ⟩
  id ∘ g                  ≈˘⟨ identity ⟩∘⟨refl ⟩
  F₁ (Category.id 𝒟) ∘ g ∎
  where open Category 𝒞
        open Functor F
        open HomReasoning
N∘≈⟦⟧ 𝒞 𝒟 F (e₁ :∘ e₂)         g = begin
  N∘ 𝒞 𝒟 F e₁ (N∘ 𝒞 𝒟 F e₂ g)       ≈⟨ N∘≈⟦⟧ 𝒞 𝒟 F e₁ (N∘ 𝒞 𝒟 F e₂ g) ⟩
  F₁ (𝒟 ⟦ e₁ ⟧) ∘ N∘ 𝒞 𝒟 F e₂ g      ≈⟨ pushʳ (N∘≈⟦⟧ 𝒞 𝒟 F e₂ g) ⟩
  (F₁ (𝒟 ⟦ e₁ ⟧) ∘ F₁ (𝒟 ⟦ e₂ ⟧)) ∘ g ≈˘⟨ homomorphism ⟩∘⟨refl ⟩
  F₁ (𝒟 [ 𝒟 ⟦ e₁ ⟧ ∘ 𝒟 ⟦ e₂ ⟧ ]) ∘ g ∎
  where open Category 𝒞
        open HomReasoning
        open MR 𝒞
        open Functor F
N∘≈⟦⟧ 𝒞 𝒟 F (:F₁ {𝒟 = ℰ} G e) g = N∘≈⟦⟧ 𝒞 ℰ (F ∘F G) e g
N∘≈⟦⟧ 𝒞 𝒟 F ∥ f ∥              g = Category.Equiv.refl 𝒞

⟦e⟧N≈⟦e⟧ : ∀ 𝒞 {A B} (e : Expr 𝒞 A B) → 𝒞 [ 𝒞 ⟦ e ⟧N ≈ 𝒞 ⟦ e ⟧ ]
⟦e⟧N≈⟦e⟧ 𝒞 e = N∘≈⟦⟧ 𝒞 𝒞 idF e id ○ identityʳ
  where open Category 𝒞
        open HomReasoning

solve : ∀ {𝒞 A B} (e₁ e₂ : Expr 𝒞 A B) →
        𝒞 [ 𝒞 ⟦ e₁ ⟧N ≈ 𝒞 ⟦ e₂ ⟧N ] → 𝒞 [ 𝒞 ⟦ e₁ ⟧ ≈ 𝒞 ⟦ e₂ ⟧ ]
solve {𝒞 = 𝒞} e₁ e₂ eq = begin
  𝒞 ⟦ e₁ ⟧  ≈˘⟨ ⟦e⟧N≈⟦e⟧ 𝒞 e₁ ⟩
  𝒞 ⟦ e₁ ⟧N ≈⟨ eq ⟩
  𝒞 ⟦ e₂ ⟧N ≈⟨ ⟦e⟧N≈⟦e⟧ 𝒞 e₂ ⟩
  𝒞 ⟦ e₂ ⟧  ∎
  where open Category 𝒞
        open HomReasoning

∥-∥ : ∀ {𝒞 A B} {f : 𝒞 [ A , B ]} → Expr 𝒞 A B
∥-∥ {f = f} = ∥ f ∥

-- Example
private
  module _ {𝒞 𝒟 ℰ : Category o ℓ e} (F : Functor 𝒞 𝒟) (G : Functor 𝒟 ℰ) where
    module F = Functor F
    module G = Functor G
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    open Category ℰ
    open HomReasoning
    module _ {A B C D}
             (f : 𝒞 [ C , D ]) (g : 𝒞 [ B , C ]) (h : 𝒟 [ A , F.F₀ B ]) where

      _ : G.F₁ (F.F₁ f) ∘ G.F₁ 𝒟.id ∘ G.F₁ (F.F₁ g) ∘ G.F₁ h ≈
          G.F₁ (𝒟 [ F.F₁ (𝒞 [ f ∘ g ]) ∘ h ])
      _ = solve
           (:F₁ G (:F₁ F ∥-∥) :∘ :F₁ G :id :∘ :F₁ G (:F₁ F ∥-∥) :∘ :F₁ G ∥-∥)
           (:F₁ G (:F₁ F (∥-∥ :∘ ∥-∥) :∘ ∥-∥))
           refl
