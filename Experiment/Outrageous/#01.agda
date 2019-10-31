{-# OPTIONS --without-K --safe #-}

-- https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf

module Experiment.Outrageous.#01 where

open import Data.Unit using (⊤)
open import Data.Product using (_×_) renaming (_,_ to _,,_)
open import Data.Nat using (ℕ)

infixl 30 _,_
infixr 40 _:→_

-- Star
data St : Set where
  :ℕ : St
  _:→_ : St → St → St

data Cx : Set where
  ε   : Cx
  _,_ : Cx → St → Cx

data _∈_ : St → Cx → Set where
  top : ∀ {Γ τ} → τ ∈ Γ , τ
  pop : ∀ {Γ σ τ} → τ ∈ Γ → τ ∈ Γ , σ

data _⊢_ : Cx → St → Set where
  var : ∀ {Γ τ} → τ ∈ Γ → Γ ⊢ τ
  lam : ∀ {Γ σ τ} → Γ , σ ⊢ τ → Γ ⊢ σ :→ τ
  app : ∀ {Γ σ τ} → Γ ⊢ σ :→ τ → Γ ⊢ σ → Γ ⊢ τ

⟦_⟧St : St → Set
⟦ :ℕ ⟧St     = ℕ
⟦ σ :→ τ ⟧St = ⟦ σ ⟧St → ⟦ τ ⟧St

⟦_⟧Cx : Cx → Set
⟦ ε ⟧Cx     = ⊤
⟦ Γ , σ ⟧Cx = ⟦ Γ ⟧Cx × ⟦ σ ⟧St

⟦_⟧∈ : ∀ {Γ τ} → τ ∈ Γ → ⟦ Γ ⟧Cx → ⟦ τ ⟧St
⟦ top ⟧∈   (γ ,, t) = t
⟦ pop i ⟧∈ (γ ,, s) = ⟦ i ⟧∈ γ

⟦_⟧⊢ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧Cx → ⟦ τ ⟧St
⟦ var i ⟧⊢   γ = ⟦ i ⟧∈ γ
⟦ lam t ⟧⊢   γ = λ s → ⟦ t ⟧⊢ (γ ,, s)
⟦ app f a ⟧⊢ γ = ⟦ f ⟧⊢ γ (⟦ a ⟧⊢ γ)
