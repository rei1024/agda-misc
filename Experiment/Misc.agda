
-- suc[m]∸zero≡zero→m∸zer
{-
suc[m]∸n≡zero⇒m∸n≡zero : ∀ {m n} → suc m ∸ n ≡ zero → m ∸ n ≡ zero
suc[m]∸n≡zero⇒m∸n≡zero {m} {n} = ind (λ k → suc m ∸ k ≡ zero → m ∸ k ≡ zero)
  (λ suc[m]∸zero≡zero → begin
    m ∸ zero

    zero ∎
    )
  {!   !} n
-}
-- m≡n+o⇒m∸n≡o : ∀
m∸n≡zero⇒m+[n∸m]≡n : ∀ {m n} → m ∸ n ≡ zero → m + (n ∸ m) ≡ n
m∸n≡zero⇒m+[n∸m]≡n {m} {n} = ind (λ k → k ∸ n ≡ zero → k + (n ∸ k) ≡ n)
  (λ _ → begin
    zero + (n ∸ zero) ≡⟨ +-identityˡ (n ∸ zero) ⟩
    n ∸ zero ≡⟨ n∸zero≡n n ⟩
    n ∎)
  (λ k k∸n≡zero→k+[n∸k]≡n suc[k]∸n≡zero → begin
    suc k + (n ∸ suc k) ≡⟨ cong (suc k +_) $ m∸suc[n]≡pred[m∸n] n k ⟩
    suc k + (pred (n ∸ k)) ≡⟨ sym $ +-suc k (pred (n ∸ k)) ⟩
     k + suc (pred (n ∸ k)) ≡⟨ {! cong (k +_) $ p  !} ⟩
    k + (n ∸ k) ≡⟨ {!   !} ⟩
    n ∎ )
  m

--

{-
ind (λ k → m ∸ k ≡ zero → m + (k ∸ m) ≡ k)
  (λ m∸zero≡zero → begin
    m + (zero ∸ m) ≡⟨ cong (m +_) $ zero∸n≡zero m ⟩
    m + zero       ≡⟨ +-identityʳ m ⟩
    m              ≡⟨ sym $ n∸zero≡n m ⟩
    m ∸ zero       ≡⟨ m∸zero≡zero ⟩
    zero ∎ )
  (λ k m∸k≡zero→m+[k∸m]≡k m∸suc[k]≡zero → begin
    m + (suc k ∸ m) ≡⟨ {!   !} ⟩
    m + (suc (k ∸ m)) ≡⟨ {!   !} ⟩
    suc (m + (k ∸ m)) ≡⟨ {!   !} ⟩
    suc k ∎)
  n
-}
-----------------------------------------------------------------------------------

m∸n≡one⇒m≡suc[n] : ∀ {m n} → m ∸ n ≡ one → m ≡ suc n
m∸n≡one⇒m≡suc[n] {m} {n} = ind (λ k → m ∸ k ≡ one → m ≡ suc k)
  (λ m∸zero≡one → trans (sym $ n∸zero≡n m) m∸zero≡one)
  (λ k m∸k≡one→m≡suc[k] m∸suc[k]≡one →
      pred[m]≡suc[n]⇒m≡suc[suc[n]] {!   !}
    )
  n


-- m ≡ suc (suc k)

-- m ∸ suc k ≡ one
-- pred (m ∸ k) ≡ one
-- pred (m ∸ k) ≡ suc zero
-- m ∸ k ≡ suc (suc zero)


-- suc (pred (m ∸ k)) ≡ suc one

-- m ∸ k ≡ suc one

-- m - (n + o) ≡ n
-- m ∸ o ≡ zero


m∸n≡suc[o]⇒m≡n+suc[o] : ∀ {m n o} → m ∸ n ≡ suc o → m ≡ n + suc o
m∸n≡suc[o]⇒m≡n+suc[o] {m} {n₀} {o} =
  ind (λ n → m ∸ n ≡ suc o → m ≡ n + suc o)
  (λ m∸zero≡suc[o] → trans (trans (sym $ n∸zero≡n m) m∸zero≡suc[o]) (sym $ +-identityˡ (suc o)))
  (λ k m∸k≡suc[o]→m≡k+suc[o] m∸suc[k]≡suc[o] → {!   !}
    ) n₀
  -- m ∸ suc k ≡ suc o
  -- pred (m ∸ k) ≡ suc o
  -- m ∸ k ≡ suc (suc o)

  -- Goal m ≡ suc k + suc o

m∸n≡zero⇒m≤n : ∀ {m n} → m ∸ n ≡ zero → m ≤ n
m∸n≡zero⇒m≤n {m} {n} = ind (λ k → m ∸ k ≡ zero → m ≤ k)
  (λ m∸zero≡zero → ≤-reflexive (trans (sym $ n∸zero≡n m) m∸zero≡zero))
  (λ k m∸k≡zero→m≤k m∸suc[k]≡zero →
    let pred[m∸k]≡zero : pred (m ∸ k) ≡ zero
        pred[m∸k]≡zero = trans (sym (m∸suc[n]≡pred[m∸n] m k)) m∸suc[k]≡zero
        m∸k≡zero∨m∸k≡one : m ∸ k ≡ zero ⊎ m ∸ k ≡ one
        m∸k≡zero∨m∸k≡one = pred[n]≡zero⇒n≡zero∨n≡one (m ∸ k) pred[m∸k]≡zero
    in Sum.[ (λ m∸k≡zero → ≤-step $ m∸k≡zero→m≤k m∸k≡zero)
           , (λ m∸k≡one → {!   !}) ] m∸k≡zero∨m∸k≡one

    -- m ∸ suc k ≡ zero
    -- pred (m ∸ k) ≡ zero
    -- m ∸ k ≡ zero ∨ m ∸ k ≡ 1 → m ≡ k + 1 -- k + 1 ≤ suc k

    ) -- m ≤ suc k
  n
 -- n ∸ m , m∸n≡zero⇒m+[n∸m]≡n m∸n≡zero

-- m + (n ∸ m) ≡ n

-- n + (m ∸ n) ≡ n
