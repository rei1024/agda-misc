firstTrue : (f : ℕ → Bool) → ∃ (λ n → f n ≡ true) → ℕ
firstTrue f prf = mp-ℕ

firstTrue-true : firstTrue f prf ≡ n → f n ≡ true
firstTrue-true = ?

firstTrue-false : firstTrue f prf ≡ n → ∀ m → m < n → f m ≡ false
firstTrue-false = ?
