{-# OPTIONS --without-K --safe #-}
module Experiment.Applicative where

open import Function.Base
open import Relation.Binary.PropositionalEquality

record Functor (F : Set → Set) : Set₁ where
  field
    fmap    : ∀ {A B} → (A → B) → F A → F B
  field
    fmap-id : ∀ {A} (x : F A) → fmap id x ≡ x
    fmap-∘  : ∀ {A B C} (f : B → C) (g : A → B) (x : F A) →
      fmap f (fmap g x) ≡ fmap (f ∘′ g) x
    fmap-cong : ∀ {A B} {f g : A → B} {x : F A} →
      (∀ v → f v ≡ g v) → fmap f x ≡ fmap g x

record Applicative (F : Set → Set) : Set₁ where
  infixl 5 _<*>_
  field
    pure  : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
  field
    identity : ∀ {A} (v : F A) → pure id <*> v ≡ v
    composition : ∀ {A B C} (u : F (A → C)) (v : F (B → A)) (w : F B) →
      pure _∘′_ <*> u <*> v <*> w ≡ u <*> (v <*> w)
    homomorphism : ∀ {A B} (f : A → B) (x : A) → pure f <*> pure x ≡ pure (f x)
    interchange : ∀ {A B} (u : F (A → B)) (y : A) →
      u <*> pure y ≡ pure (_$ y) <*> u
    -- <*>-cong : (∀ x → ff <*> pure x ≡ fg <*> pure x) → ff <*> fx ≡ fg <*> fx
  homomorphism₂ : ∀ {A B C} (f : A → B → C) (x : A) (y : B) →
    pure f <*> pure x <*> pure y ≡ pure (f x y)
  homomorphism₂ f x y = begin
    pure f <*> pure x <*> pure y ≡⟨ cong (_<*> pure y) $ homomorphism f x ⟩
    pure (f x) <*> pure y        ≡⟨ homomorphism (f x) y ⟩
    pure (f x y)                 ∎
    where open ≡-Reasoning

  functor : Functor F
  functor = record
    { fmap    = λ f fx → pure f <*> fx
    ; fmap-id = identity
    ; fmap-∘  = λ f g x → begin
      pure f <*> (pure g <*> x)
        ≡⟨ sym $ composition (pure f) (pure g) x ⟩
      pure _∘′_ <*> pure f <*> pure g <*> x
        ≡⟨ cong (λ v → v <*> x) $ homomorphism₂ _∘′_ f g ⟩
      pure (f ∘′ g) <*> x
        ∎
    ; fmap-cong = λ {A} {B} {f = f} {g = g} {x = x} f≡g → {!   !}
    }
    where open ≡-Reasoning

  liftA2 : ∀ {A B C} → (A → B → C) → F A → F B → F C
  liftA2 f fx fy = pure f <*> fx <*> fy
{-
forall x y. p (q x y) = f x . g y
it follows from the above that

liftA2 p (liftA2 q u v) = liftA2 f u . liftA2 g v
-}
record ApplicativeViaZip (F : Set → Set) : Set₁ where
  field
    pair : F A → F B → F (A × B)
    pair fx fy = ?
record Monad (F : Set → Set) : Set₁ where
  infixl 5 _>>=_
  field
    return : ∀ {A} → A → F A
    _>>=_ : ∀ {A B} → F A → (A → F B) → F B
  field
    identityˡ : ∀ {A B} (a : A) (k : A → F B) → return a >>= k ≡ k a
    identityʳ : ∀ {A} (m : F A) → m >>= return ≡ m
    assoc : ∀ {A B C} (m : F A) (k : A → F B) (h : B → F C) →
      m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h

  join : ∀ {A} → F (F A) → F A
  join x = x >>= id
-- pure f <*> x ≡ pure g <*> x
  m >>= k = join (fmap k m)
  (∀ x → k x ≡ l x)
  join (fmap k m)
  join (fmap l m

  liftM1 : ∀ {A B} → (A → B) → F A → F B
  liftM1 f mx = mx >>= (λ x → return (f x))

  functor : Functor F
  functor = record
    { fmap    = liftM1
    ; fmap-id = λ fx → identityʳ fx
    ; fmap-∘  = λ f g x → begin
      liftM1 f (liftM1 g x) ≡⟨ refl ⟩
      liftM1 g x >>= (λ y → return (f y)) ≡⟨ refl ⟩
      (x >>= (λ y → return (g y))) >>= (λ y → return (f y))
        ≡⟨ sym $ assoc x (λ y → return (g y)) (λ y → return (f y)) ⟩
      x >>= (λ y → return (g y) >>= (return ∘ f) )
        ≡⟨ cong (λ v → x >>= v) $ {!   !} ⟩
      x >>= (λ y → return (f (g y))) ≡⟨ refl ⟩
      liftM1 (f ∘′ g) x ∎
    }
    where open ≡-Reasoning

  applicative : Applicative F
  applicative = record
    { pure         = return
    ; _<*>_        = λ fab fa → fab >>= λ ab → fa >>= λ a → return (ab a)
    ; identity     = λ v → begin
      return id >>= (λ ab → v >>= λ a → return (ab a)) ≡⟨ identityˡ id _ ⟩
      v >>= return                                     ≡⟨ identityʳ v ⟩
      v                                                ∎
    ; composition  = λ u v w → begin
      return _∘′_ >>= (λ f → u >>= (return ∘ f)) >>= (λ f → v >>= (return ∘ f))
        >>= (λ f → w >>= (return ∘ f)) ≡⟨ {!   !} ⟩
      u >>= (λ f → v >>= (λ g → w >>= (return ∘ g)) >>= (return ∘ f))
       ∎
    ; homomorphism = {!   !}
    ; interchange  = {!   !}
    }
    where open ≡-Reasoning
{-
return _∘′_ >>= (λ f → u >>= (λ a → return (f a))) >>=
(λ f → v >>= (λ a → return (f a)))
>>= (λ f → w >>= (λ a → return (f a)))
≡
u >>=
(λ f →
   v >>= (λ g → w >>= (λ a → return (g a))) >>=
   (λ a → return (f a)))
-}
-- Traversable
