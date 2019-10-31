{-# OPTIONS --without-K --safe #-}
module Experiment.Applicative where

open import Function.Core
open import Relation.Binary.PropositionalEquality
open import Data.Product as Prod
open import Data.Unit

record Functor (F : Set → Set) : Set₁ where
  field
    fmap    : ∀ {A B} → (A → B) → F A → F B
  field
    fmap-id : ∀ {A} (x : F A) → fmap id x ≡ x
    fmap-∘  : ∀ {A B C} (f : B → C) (g : A → B) (x : F A) →
      fmap f (fmap g x) ≡ fmap (f ∘′ g) x
    fmap-cong : ∀ {A B} {f g : A → B} {x : F A} →
      (∀ v → f v ≡ g v) → fmap f x ≡ fmap g x

  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap

×-assoc : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A × B) × C → A × (B × C)
×-assoc ((x , y) , z) = x , (y , z)

×-assoc⁻¹ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → A × (B × C) → (A × B) × C
×-assoc⁻¹ (x , (y , z)) = (x , y) , z

app : ∀ {a} {b} {A : Set a} {B : Set b} → (A → B) × A → B
app = uncurry _$′_

record Applicative (F : Set → Set) : Set₁ where
  infixl 5 _<*>_
  field
    functor : Functor F
    unit    : F ⊤
    _<,>_   : ∀ {A B} → F A → F B → F (A × B)
  open Functor functor public

  field
    natural : ∀ {A B C D} (f : A → C) (g : B → D) (fx : F A) (fy : F B) →
      fmap f fx <,> fmap g fy ≡ fmap (Prod.map f g) (fx <,> fy)
    assoc : ∀ {A B C} (fx : F A) (fy : F B) (fz : F C) →
      fmap ×-assoc ((fx <,> fy) <,> fz) ≡ (fx <,> (fy <,> fz))
    unitˡ : ∀ {B} (fy : F B) → fmap proj₂ (unit <,> fy) ≡ fy
    unitʳ : ∀ {A} (fx : F A) → fmap proj₁ (fx <,> unit) ≡ fx

  pure : ∀ {A} → A → F A
  pure {A} x = fmap (λ _ → x) unit

  _<*>_ : ∀ {A B} → F (A → B) → F A → F B
  _<*>_ ff fx = fmap app (ff <,> fx)

  liftA2 : ∀ {A B C} → (A → B → C) → F A → F B → F C
  liftA2 f fx fy = fmap (uncurry f) (fx <,> fy)

  natural₁ : ∀ {A B C} (f : A → C) (fx : F A) (fy : F B) →
    fmap f fx <,> fy ≡ fmap (Prod.map₁ f) (fx <,> fy)
  natural₁ f fx fy = begin
    fmap f fx <,> fy               ≡⟨ cong (fmap f fx <,>_) $ sym $ fmap-id fy ⟩
    fmap f fx <,> fmap id fy       ≡⟨ natural f id fx fy ⟩
    fmap (Prod.map₁ f) (fx <,> fy) ∎
    where open ≡-Reasoning

  natural₂ : ∀ {A B D} (g : B → D) (fx : F A) (fy : F B) →
    fx <,> fmap g fy ≡ fmap (Prod.map₂ g) (fx <,> fy)
  natural₂ g fx fy = begin
    fx <,> fmap g fy               ≡⟨ cong (_<,> fmap g fy) $ sym $ fmap-id fx ⟩
    fmap id fx <,> fmap g fy       ≡⟨ natural id g fx fy ⟩
    fmap (Prod.map₂ g) (fx <,> fy) ∎
    where open ≡-Reasoning

  assoc⁻¹ : ∀ {A B C} (fx : F A) (fy : F B) (fz : F C) →
    fmap ×-assoc⁻¹ (fx <,> (fy <,> fz)) ≡ (fx <,> fy) <,> fz
  assoc⁻¹ fx fy fz = begin
    fmap ×-assoc⁻¹ (fx <,> (fy <,> fz))
      ≡⟨ sym $ cong (fmap ×-assoc⁻¹) (assoc fx fy fz) ⟩
    fmap ×-assoc⁻¹ (fmap ×-assoc ((fx <,> fy) <,> fz))
      ≡⟨ fmap-∘ ×-assoc⁻¹ ×-assoc ((fx <,> fy) <,> fz) ⟩
    fmap (×-assoc⁻¹ ∘′ ×-assoc) ((fx <,> fy) <,> fz)
      ≡⟨⟩
    fmap id ((fx <,> fy) <,> fz)
      ≡⟨ fmap-id ((fx <,> fy) <,> fz) ⟩
    (fx <,> fy) <,> fz
      ∎
    where open ≡-Reasoning

  unit-pure : unit ≡ pure tt
  unit-pure = begin
    unit                 ≡⟨ sym $ fmap-id unit ⟩
    fmap id unit         ≡⟨ refl ⟩
    fmap (λ _ → tt) unit ∎
    where open ≡-Reasoning

  fmap-pure : ∀ {A B} (f : A → B) (x : A) → fmap f (pure x) ≡ pure (f x)
  fmap-pure f x = begin
    fmap f (fmap (λ _ → x) unit) ≡⟨ fmap-∘ f (λ _ → x) unit ⟩
    fmap (λ _ → f x) unit        ∎
    where open ≡-Reasoning

  unitˡʳ : ∀ {A} (fx : F A) → fmap proj₂ (unit <,> fx) ≡ fmap proj₁ (fx <,> unit)
  unitˡʳ fx = trans (unitˡ fx) (sym $ unitʳ fx)

  unitˡ′ : ∀ {B} (fy : F B) → unit <,> fy ≡ fmap (tt ,_) fy
  unitˡ′ fy = begin
    unit <,> fy
      ≡⟨ sym $ fmap-id (unit <,> fy) ⟩
    fmap id (unit <,> fy)
      ≡⟨ fmap-cong (λ _ → refl) ⟩
    fmap ((tt ,_) ∘′ proj₂) (unit <,> fy)
      ≡⟨ sym $ fmap-∘ (tt ,_) proj₂ (unit <,> fy) ⟩
    fmap (tt ,_) (fmap proj₂ (unit <,> fy))
      ≡⟨ cong (fmap (tt ,_)) (unitˡ fy) ⟩
    fmap (tt ,_) fy
      ∎
    where open ≡-Reasoning

  unitʳ′ : ∀ {A} (fx : F A) → fx <,> unit ≡ fmap (_, tt) fx
  unitʳ′ fx = begin
    fx <,> unit
      ≡⟨ sym $ fmap-id (fx <,> unit) ⟩
    fmap id (fx <,> unit)
      ≡⟨⟩
    fmap ((_, tt) ∘′ proj₁) (fx <,> unit)
      ≡⟨ sym $ fmap-∘ (_, tt) proj₁ (fx <,> unit) ⟩
    fmap (_, tt) (fmap proj₁ (fx <,> unit))
      ≡⟨ cong (fmap (_, tt)) (unitʳ fx) ⟩
    fmap (_, tt) fx
      ∎
    where open ≡-Reasoning

  <,>-pureˡ : ∀ {A B} (x : A) (fy : F B) → pure x <,> fy ≡ fmap (x ,_) fy
  <,>-pureˡ x fy = begin
    fmap (λ _ → x) unit <,> fy
      ≡⟨ natural₁ (λ _ → x) unit fy ⟩
    fmap (Prod.map₁ (λ _ → x)) (unit <,> fy)
      ≡⟨ cong (fmap (Prod.map₁ (λ _ → x))) (unitˡ′ fy) ⟩
    fmap (Prod.map₁ (λ _ → x)) (fmap (tt ,_) fy)
      ≡⟨ fmap-∘ (Prod.map₁ (λ _ → x)) (tt ,_) fy ⟩
    fmap (Prod.map₁ (λ _ → x) ∘′ (tt ,_)) fy
      ≡⟨⟩
    fmap (x ,_) fy
      ∎
    where open ≡-Reasoning

  <,>-pureʳ : ∀ {A B} (fx : F A) (y : B) → fx <,> pure y ≡ fmap (_, y) fx
  <,>-pureʳ fx y = begin
    fx <,> fmap (λ _ → y) unit
      ≡⟨ natural₂ (λ _ → y) fx unit ⟩
    fmap (Prod.map₂ (λ _ → y)) (fx <,> unit)
      ≡⟨ cong (fmap (Prod.map₂ (λ _ → y))) (unitʳ′ fx) ⟩
    fmap (Prod.map₂ (λ _ → y)) (fmap (_, tt) fx)
      ≡⟨ fmap-∘ (Prod.map₂ (λ _ → y)) (_, tt) fx ⟩
    fmap (Prod.map₂ (λ _ → y) ∘′ (_, tt)) fx
      ≡⟨⟩
    fmap (_, y) fx ∎
    where open ≡-Reasoning

  pure-<,> : ∀ {A B} (x : A) (y : B) → pure x <,> pure y ≡ pure (x , y)
  pure-<,> x y = begin
    pure x <,> pure y    ≡⟨ <,>-pureˡ x (pure y) ⟩
    fmap (x ,_) (pure y) ≡⟨ fmap-pure (x ,_) y ⟩
    pure (x , y)         ∎
    where open ≡-Reasoning

  <*>-fmap : ∀ {A B} (f : A → B) (fx : F A) → pure f <*> fx ≡ fmap f fx
  <*>-fmap f fx = begin
    fmap app (pure f <,> fx)  ≡⟨ cong (fmap app) $ <,>-pureˡ f fx ⟩
    fmap app (fmap (f ,_) fx) ≡⟨ fmap-∘ app (f ,_) fx ⟩
    fmap (app ∘′ (f ,_)) fx   ≡⟨⟩
    fmap f fx                 ∎
    where open ≡-Reasoning

  <*>-identity : ∀ {A} (v : F A) → pure id <*> v ≡ v
  <*>-identity v = begin
   fmap (uncurry _$′_) (pure id <,> v)  ≡⟨ cong (fmap (uncurry _$′_)) $ <,>-pureˡ id v ⟩
   fmap (uncurry _$′_) (fmap (id ,_) v) ≡⟨ fmap-∘ (uncurry _$′_) (id ,_) v ⟩
   fmap (uncurry _$′_ ∘′ (id ,_)) v     ≡⟨ fmap-cong (λ _ → refl) ⟩
   fmap id v                            ≡⟨ fmap-id v ⟩
   v                                    ∎
   where open ≡-Reasoning

  <*>-composition : ∀ {A B C} (u : F (A → C)) (v : F (B → A)) (w : F B) →
     pure _∘′_ <*> u <*> v <*> w ≡ u <*> (v <*> w)
  <*>-composition u v w = begin
    pure _∘′_ <*> u <*> v <*> w
      ≡⟨ cong (λ t → t <*> v <*> w) $ <*>-fmap _∘′_ u ⟩
    fmap _∘′_ u <*> v <*> w
      ≡⟨ refl ⟩
    fmap app (fmap _∘′_ u <,> v) <*> w
      ≡⟨ refl ⟩
    fmap app (fmap app (fmap _∘′_ u <,> v) <,> w)
      ≡⟨ cong (λ t → fmap app (fmap app t <,> w)) $ natural₁ _∘′_ u v ⟩
    fmap app (fmap app (fmap (Prod.map₁ _∘′_) (u <,> v)) <,> w)
      ≡⟨ cong (fmap app) $ natural₁ app (fmap (Prod.map₁ _∘′_) (u <,> v)) w ⟩
    fmap app (fmap (Prod.map₁ app) (fmap (Prod.map₁ _∘′_) (u <,> v) <,> w))
      ≡⟨ fmap-∘ app (Prod.map₁ app) _ ⟩
    fmap (app ∘′ Prod.map₁ app) (fmap (Prod.map₁ _∘′_) (u <,> v) <,> w)
      ≡⟨ cong (fmap (app ∘′ Prod.map₁ app)) $ natural₁ (Prod.map₁ _∘′_) (u <,> v) w ⟩
    fmap (app ∘′ Prod.map₁ app) (fmap (Prod.map₁ (Prod.map₁ _∘′_)) ((u <,> v) <,> w))
      ≡⟨ fmap-∘ (app ∘′ Prod.map₁ app) (Prod.map₁ (Prod.map₁ _∘′_)) _ ⟩
    fmap (app ∘′ Prod.map₁ app ∘′ Prod.map₁ (Prod.map₁ _∘′_)) ((u <,> v) <,> w)
      ≡⟨ fmap-cong (λ _ → refl) ⟩
    fmap (app ∘′ Prod.map₂ app ∘′ ×-assoc) ((u <,> v) <,> w)
      ≡⟨ sym $ fmap-∘ (app ∘′ Prod.map₂ app) ×-assoc ((u <,> v) <,> w) ⟩
    fmap (app ∘′ Prod.map₂ app) (fmap ×-assoc ((u <,> v) <,> w))
      ≡⟨ cong (fmap (app ∘′ Prod.map₂ app)) (assoc u v w) ⟩
    fmap (app ∘′ Prod.map₂ app) (u <,> (v <,> w))
      ≡⟨ sym $ fmap-∘ app (Prod.map₂ app) (u <,> (v <,> w)) ⟩
    fmap app (fmap (Prod.map₂ app) (u <,> (v <,> w)))
      ≡⟨ sym $ cong (fmap app) $ natural₂ app u (v <,> w) ⟩
    fmap app (u <,> fmap app (v <,> w))
      ≡⟨ refl ⟩
    u <*> (v <*> w)
      ∎
    where open ≡-Reasoning

  <*>-homomorphism : ∀ {A B} (f : A → B) (x : A) → pure f <*> pure x ≡ pure (f x)
  <*>-homomorphism f x = begin
    pure f <*> pure x ≡⟨ <*>-fmap f (pure x) ⟩
    fmap f (pure x)   ≡⟨ fmap-pure f x ⟩
    pure (f x)        ∎
    where open ≡-Reasoning

  <*>-interchange : ∀ {A B} (u : F (A → B)) (y : A) →
    u <*> pure y ≡ pure (_$ y) <*> u
  <*>-interchange u y = begin
    u <*> pure y             ≡⟨⟩
    fmap app (u <,> pure y)  ≡⟨ cong (fmap app) (<,>-pureʳ u y) ⟩
    fmap app (fmap (_, y) u) ≡⟨ fmap-∘ app (_, y) u ⟩
    fmap (app ∘′ (_, y)) u   ≡⟨⟩
    fmap (_$ y) u            ≡⟨ sym $ <*>-fmap (_$ y) u ⟩
    pure (_$ y) <*> u        ∎
    where open ≡-Reasoning

  liftA2-defn : ∀ {A B C} (f : A → B → C) (fx : F A) (fy : F B) →
    liftA2 f fx fy ≡ pure f <*> fx <*> fy
  liftA2-defn f fx fy = begin
    fmap (uncurry f) (fx <,> fy)              ≡⟨⟩
    fmap (app ∘′ Prod.map₁ f) (fx <,> fy)     ≡⟨ sym $ fmap-∘ app (Prod.map₁ f) (fx <,> fy) ⟩
    fmap app (fmap (Prod.map₁ f) (fx <,> fy)) ≡⟨ cong (fmap app) $ sym $ natural₁ f fx fy ⟩
    fmap app (fmap f fx <,> fy)               ≡⟨⟩
    fmap f fx <*> fy                          ≡⟨ sym $ cong (_<*> fy) $ <*>-fmap f fx ⟩
    pure f <*> fx <*> fy                      ∎
    where open ≡-Reasoning

  liftA2-cong : ∀ {A B C} {f g : A → B → C} {fx : F A} {fy : F B} →
    (∀ x y → f x y ≡ g x y) → liftA2 f fx fy ≡ liftA2 g fx fy
  liftA2-cong {_} {_} {_} {f} {g} {fx} {gx} f≡g = fmap-cong λ v → f≡g (proj₁ v) (proj₂ v)

  <*>-defn : ∀ {A B C} (ff : F (A → B)) (fx : F A) → ff <*> fx ≡ liftA2 _$′_ ff fx
  <*>-defn ff fx = refl

  -- liftA2 f fx fy = pure f <*> fx <*> fy
{-
forall x y. p (q x y) = f x . g y
it follows from the above that

liftA2 p (liftA2 q u v) = liftA2 f u . liftA2 g v
-}

record ApplicativeViaAp (F : Set → Set) : Set₁ where
  infixl 5 _<*>_
  field
    functor : Functor F
    pure    : ∀ {A} → A → F A
    _<*>_   : ∀ {A B} → F (A → B) → F A → F B
  open Functor functor public
  field
    identity     : ∀ {A} (fx : F A) → pure id <*> fx ≡ fx
    composition  : ∀ {A B C} (u : F (A → C)) (v : F (B → A)) (w : F B) →
       pure _∘′_ <*> u <*> v <*> w ≡ u <*> (v <*> w)
    homomorphism : ∀ {A B} (f : A → B) (x : A) → pure f <*> pure x ≡ pure (f x)
    interchange  : ∀ {A B} (u : F (A → B)) (y : A) →
      u <*> pure y ≡ pure (_$ y) <*> u
    <*>-fmap     : ∀ {A B} (f : A → B) (fx : F A) → pure f <*> fx ≡ fmap f fx

  _<,>_ : ∀ {A B} → F A → F B → F (A × B)
  fx <,> fy = pure _,_ <*> fx <*> fy

  liftA2 : ∀ {A B C} → (A → B → C) → F A → F B → F C
  liftA2 f fx fy = fmap (uncurry f) (fx <,> fy)

  unit : F ⊤
  unit = pure tt

  <,>-natural : ∀ {A B C D} (f : A → C) (g : B → D) (fx : F A) (fy : F B) →
    fmap f fx <,> fmap g fy ≡ fmap (Prod.map f g) (fx <,> fy)
  <,>-natural f g fx fy = begin
    pure _,_ <*> fmap f fx <*> fmap g fy
      ≡⟨ cong (_<*> fmap g fy) $ <*>-fmap _,_ (fmap f fx) ⟩
    fmap _,_ (fmap f fx) <*> fmap g fy
      ≡⟨ cong (_<*> fmap g fy) $ fmap-∘ _,_ f fx ⟩
    fmap (_,_ ∘′ f) fx <*> fmap g fy
      ≡⟨ {!   !} ⟩
    fmap (Prod.map f g) (fmap _,_ fx <*> fy)
      ≡⟨ sym $ cong (λ t → fmap (Prod.map f g) (t <*> fy)) $ <*>-fmap _,_ fx ⟩
    fmap (Prod.map f g) (pure _,_ <*> fx <*> fy)
      ∎
    where open ≡-Reasoning

  liftA2-defn : ∀ {A B C} (f : A → B → C) (fx : F A) (fy : F B) →
    liftA2 f fx fy ≡ pure f <*> fx <*> fy
  liftA2-defn f fx fy = {!   !}

record Monad (F : Set → Set) : Set₁ where
  infixl 5 _>>=_
  field
    functor : Functor F
    return  : ∀ {A} → A → F A
    join    : ∀ {A} → F (F A) → F A

  open Functor functor public
  field
    assoc          : ∀ {A} (fffx : F (F (F A))) → join (fmap join fffx) ≡ join (join fffx)
    identityˡ      : ∀ {A} (fx : F A) → join (fmap return fx) ≡ fx
    identityʳ      : ∀ {A} (fx : F A) → join (return fx) ≡ fx
    join-natural   : ∀ {A B} (f : A → B) (ffx : F (F A)) →
      join (fmap (fmap f) ffx) ≡ fmap f (join ffx)
    return-natural : ∀ {A B} (f : A → B) (x : A) → return (f x) ≡ fmap f (return x)

  _>>=_ : ∀ {A B} → F A → (A → F B) → F B
  _>>=_ m k = join (fmap k m)

  _=<<_ : ∀ {A B} → (A → F B) → F A → F B
  _=<<_ = flip _>>=_

  liftM : ∀ {A B} → (A → B) → F A → F B
  liftM f fx = fx >>= λ x → return (f x)

  ap : ∀ {A B} → F (A → B) → F A → F B
  ap ff fx = ff >>= λ f → fmap f fx

  pair : ∀ {A B} → F A → F B → F (A × B)
  pair fx fy = fx >>= λ x → fmap (λ y → x , y) fy

  unitM : F ⊤
  unitM = return tt

  liftM-is-fmap : ∀ {A B} (f : A → B) (fx : F A) → liftM f fx ≡ fmap f fx
  liftM-is-fmap f fx = begin
    join (fmap (λ x → return (f x)) fx) ≡⟨ sym $ cong join $ fmap-∘ return f fx ⟩
    join (fmap return (fmap f fx))      ≡⟨ identityˡ (fmap f fx) ⟩
    fmap f fx                           ∎
    where open ≡-Reasoning

  >>=-cong : ∀ {A B} {f g : A → F B} {fx : F A} →
    (∀ x → f x ≡ g x) → fx >>= f ≡ fx >>= g
  >>=-cong f≡g = cong join (fmap-cong f≡g)

  fmap-lemma : ∀ {A B C} (f : A → B) (fx : F A) (k : B → F C) →
    fmap f fx >>= k ≡ fx >>= λ x → k (f x)
  fmap-lemma f fx k = begin
    fmap f fx >>= k                  ≡⟨⟩
    join (fmap k (fmap f fx))        ≡⟨ cong join (fmap-∘ k f fx) ⟩
    join (fmap (λ x → (k (f x))) fx) ∎
    where open ≡-Reasoning

  liftM-lemma : ∀ {A B C} (f : A → B) (fx : F A) (k : B → F C) →
    liftM f fx >>= k ≡ fx >>= λ x → k (f x)
  liftM-lemma f fx k = begin
    liftM f fx >>= k       ≡⟨ cong (_>>= k) $ liftM-is-fmap f fx ⟩
    fmap f fx >>= k        ≡⟨ fmap-lemma f fx k ⟩
    fx >>= (λ x → k (f x)) ∎
    where open ≡-Reasoning

{-
  kleisli-identityˡ : ∀ {A B : Set} (f : A → F B) (x : A) → join (fmap return (f x)) ≡ f x
  kleisli-identityˡ f x = identityˡ (f x)

  kleisli-identityʳ : ∀ {A B : Set} (f : A → F B) (x : A) → join (fmap f (return x)) ≡ f x
  kleisli-identityʳ f x = >>=-identityˡ f x
-}

  fmap-return : ∀ {A B} (f : A → B) (x : A) → fmap f (return x) ≡ return (f x)
  fmap-return f x = sym $ return-natural f x

  >>=-identityˡ : ∀ {A B} (a : A) (k : A → F B) → return a >>= k ≡ k a
  >>=-identityˡ a k = begin
    join (fmap k (return a)) ≡⟨ cong join $ fmap-return k a ⟩
    join (return (k a))      ≡⟨ identityʳ (k a) ⟩
    k a                      ∎
    where open ≡-Reasoning

  >>=-identityʳ : ∀ {A} (m : F A) → m >>= return ≡ m
  >>=-identityʳ m = identityˡ m

  >>=-assoc : ∀ {A B C} (m : F A) (k : A → F B) (h : B → F C) →
      m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
  >>=-assoc m k h = begin
    m >>= (λ x → k x >>= h)
      ≡⟨⟩
    join (fmap (λ x → join (fmap h (k x))) m)
      ≡⟨ sym $ cong join $ fmap-∘ join (fmap h ∘′ k) m ⟩
    join (fmap join (fmap (fmap h ∘′ k) m))
      ≡⟨ assoc (fmap (fmap h ∘′ k) m) ⟩
    join (join (fmap (fmap h ∘′ k) m))
      ≡⟨ cong join (begin
      join (fmap (fmap h ∘′ k) m)     ≡⟨ sym $ cong join $ fmap-∘ (fmap h) k m ⟩
      join (fmap (fmap h) (fmap k m)) ≡⟨ join-natural h (fmap k m) ⟩
      fmap h (join (fmap k m))        ∎ ) ⟩
    join (fmap h (join (fmap k m)))
      ≡⟨⟩
    (m >>= k) >>= h
      ∎
    where open ≡-Reasoning

  fmap->>= : ∀ {A B C} (f : B → C) (m : F A) (k : A → F B) →
    fmap f (m >>= k) ≡ m >>= (λ x → fmap f (k x))
  fmap->>= f m k = begin
    fmap f (m >>= k)                ≡⟨⟩
    fmap f (join (fmap k m))        ≡⟨ sym $ join-natural f (fmap k m) ⟩
    join (fmap (fmap f) (fmap k m)) ≡⟨ cong join $ fmap-∘ (fmap f) k m ⟩
    join (fmap (fmap f ∘′ k) m)     ≡⟨⟩
    m >>= (λ x → fmap f (k x))      ∎
    where open ≡-Reasoning

  fmap-move : ∀ {A B C D} (f : C → D) (g : A → B → C) (m1 : F A) (m2 : F B) →
    fmap f (m1 >>= λ x → fmap (g x) m2) ≡ m1 >>= (λ x → fmap (f ∘′ g x) m2)
  fmap-move f g m1 m2 = begin
    fmap f (m1 >>= λ x → fmap (g x) m2)   ≡⟨ fmap->>= f m1 (λ x → fmap (g x) m2) ⟩
    m1 >>= (λ x → fmap f (fmap (g x) m2)) ≡⟨ >>=-cong (λ x → fmap-∘ f (g x) m2) ⟩
    m1 >>= (λ x → fmap (f ∘′ g x) m2)     ∎
    where open ≡-Reasoning

  applicative : Applicative F
  applicative = record
    { functor = functor
    ; unit    = unitM
    ; _<,>_   = pair
    ; natural = λ f g fx fy → begin
      pair (fmap f fx) (fmap g fy)
        ≡⟨⟩
      fmap f fx >>= (λ x → fmap (λ y → x , y) (fmap g fy))
        ≡⟨ fmap-lemma f fx _ ⟩
      fx >>= (λ x → fmap (λ y → f x , y) (fmap g fy) )
        ≡⟨ >>=-cong (λ x → fmap-∘ (f x ,_) g fy) ⟩
      fx >>= (λ x → fmap (λ y → f x , g y) fy)
        ≡⟨⟩
      fx >>= (λ x → fmap (λ y → Prod.map f g (x , y) ) fy )
        ≡⟨ sym $ fmap-move (Prod.map f g) _,_ fx fy ⟩
      fmap (Prod.map f g) (fx >>= λ x → fmap (λ y → x , y) fy)
        ≡⟨⟩
      fmap (Prod.map f g) (pair fx fy)
        ∎
    ; assoc   = λ fx fy fz →
      fmap ×-assoc (pair (pair fx fy) fz)
        ≡⟨⟩
      fmap ×-assoc ((fx >>= λ x → fmap (x ,_) fy) >>= λ xy → fmap (xy ,_) fz)
        ≡⟨ {! sym $ >>=-assoc fx   !} ⟩
      fx >>= (λ x → fy >>= λ y → fmap (λ z → x , (y , z)) fz)
        ≡⟨ sym $ >>=-cong (λ x → fmap-move (x ,_) _,_ fy fz) ⟩
      fx >>= (λ x → fmap (x ,_) (fy >>= λ y → fmap (y ,_) fz))
        ≡⟨⟩
      pair fx (pair fy fz)
        ∎
    ; unitˡ   = {!   !}
    ; unitʳ   = {!   !}
    }
    where open ≡-Reasoning
