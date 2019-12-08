T-to-≡ : ∀ {x} → T x → x ≡ true
T-to-≡ {true} tx = refl

≡-to-T : ∀ {x} → x ≡ true → T x
≡-to-T {true} x≡true = tt

≤-to-→ : ∀ {x y} → x 𝔹.≤ y → T x → T y
≤-to-→ {true} {true} x≤y _ = tt

→-to-≤ : ∀ {x y} → (T x → T y) → x 𝔹.≤ y
→-to-≤ {false} {false} Tx→Ty = b≤b
→-to-≤ {false} {true}  Tx→Ty = f≤t
→-to-≤ {true}  {false} Tx→Ty = ⊥-elim (Tx→Ty tt)
→-to-≤ {true}  {true}  Tx→Ty = b≤b

toFun : (x : ℕ → Bool) → (∀ i → x (suc i) 𝔹.≤ x i) →
        ∀ i → T (x (suc i)) → T (x i)
toFun x p i = ≤-to-→ (p i)

fromFun : (x : ℕ → Bool) → (∀ i → T (x (suc i)) → T (x i)) →
          ∀ i → x (suc i) 𝔹.≤ x i
fromFun _ f i = →-to-≤ (f i)



Dec-T : ∀ b → Dec (T b)
Dec-T false = no id
Dec-T true  = yes tt

private
  _≈Decidable_ : ∀ {P Q : ℕ → Set} (P? : U.Decidable P) (Q? : U.Decidable Q) → Set
  P? ≈Decidable Q? = ∀ x → isYes (P? x) ≡ isYes (Q? x)

  make≈Decidable : {P Q : ℕ → Set} → (∀ x → P x → Q x) → (∀ x → Q x → P x) →
                   (P? : U.Decidable P) (Q? : U.Decidable Q) → P? ≈Decidable Q?
  make≈Decidable P→Q Q→P P? Q? x with P? x | Q? x
  ... | yes p | yes q = refl
  ... | yes p | no ¬q = contradiction (P→Q _ p) ¬q
  ... | no ¬p | yes q = contradiction (Q→P _ q) ¬p
  ... | no ¬p | no ¬q = refl

  ℕ≤-all-dec′ : ∀ {P : ℕ → Set} → U.Decidable P → U.Decidable (λ n → ∀ i → i ≤ n → P i)
  ℕ≤-all-dec′ P? = DecU⇒decidable $ ℕ≤-all-dec (decidable⇒DecU P?)

idem-map-Pred : (α : ℕ → Bool) → ℕ → Set
idem-map-Pred α n = ∀ i → i ≤ n → T (α i)

idem-map-Pred? : (α : ℕ → Bool) → U.Decidable (idem-map-Pred α)
idem-map-Pred? α = ℕ≤-all-dec′ (λ i → Dec-T (α i))

idem-map : (ℕ → Bool) → (ℕ → Bool)
idem-map α n = isYes (idem-map-Pred? α n)

idem-map-idem : ∀ α → idem-map (idem-map α) ≈ idem-map α
idem-map-idem α =
  make≈Decidable
    (λ n x i i≤n → {!   !})
    {!   !}
    (idem-map-Pred? (λ n → isYes (idem-map-Pred? α n)))
    (idem-map-Pred? α)

-- x : idem-map-Pred (λ n₁ → isYes (idem-map-Pred? α n₁)) n
-- x : ∀ i → i ≤ n → T (isYes (idem-map-Pred? α i))

-- True   toWitness
-- hyp : idem-map-Pred α i
-- hyp : ∀ i →

-- Goal : ∀ i → i ≤ n → T (α i)

-- idem-map α n
-- isYes (ℕ-all-dec′ (λ i → Dec-⊤ (α i)) n)

idem-map-image : ∀ α → let x = idem-map α in (∀ i → T (x (suc i)) → T (x i))
idem-map-image α n ppp with ℕ≤-all-dec′ (λ i → Dec-T (α i)) n
... | yes _ = {!   !}
... | no _  = {!   !}
