theorem numbertheory_3pow2pownm1mod2pownp3eq2pownp2 (n : ℕ) (h₀ : 0 < n) :
    (3 ^ 2 ^ n - 1) % 2 ^ (n + 3) = 2 ^ (n + 2) := by
  have h_main : (3 ^ 2 ^ n - 1) % 2 ^ (n + 3) = 2 ^ (n + 2) := by
    have h₁ : 3 ^ 2 ^ n % 2 ^ (n + 3) = 1 + 2 ^ (n + 2) := by
      have h₂ : ∀ k : ℕ, 0 < k → 3 ^ 2 ^ k % 2 ^ (k + 3) = 1 + 2 ^ (k + 2) := by
        intro k hk
        have h₃ : 3 ^ 2 ^ k % 2 ^ (k + 3) = 1 + 2 ^ (k + 2) := by
          have h₄ : ∀ n : ℕ, 0 < n → 3 ^ 2 ^ n % 2 ^ (n + 3) = 1 + 2 ^ (n + 2) := by
            intro n hn
            induction' hn with n hn IH
            · norm_num
            · cases n with
              | zero =>
                norm_num at hn ⊢
              | succ n =>
                simp [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.add_mod, Nat.mod_mod] at IH ⊢
                <;>
                  (try omega) <;>
                  (try
                    {
                      simp_all [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
                      <;>
                        ring_nf at *
                      <;>
                        omega
                    }) <;>
                  (try
                    {
                      norm_num at *
                      <;>
                        ring_nf at *
                      <;>
                        omega
                    })
          exact h₄ k hk
        exact h₃
      exact h₂ n h₀
    have h₂ : (3 ^ 2 ^ n - 1) % 2 ^ (n + 3) = 2 ^ (n + 2) := by
      have h₃ : 3 ^ 2 ^ n % 2 ^ (n + 3) = 1 + 2 ^ (n + 2) := h₁
      have h₄ : 3 ^ 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        <;> simp
        <;> positivity
      have h₅ : (3 ^ 2 ^ n - 1) % 2 ^ (n + 3) = (3 ^ 2 ^ n % 2 ^ (n + 3) - 1) % 2 ^ (n + 3) := by
        have h₅₁ : 3 ^ 2 ^ n % 2 ^ (n + 3) = 1 + 2 ^ (n + 2) := h₁
        have h₅₂ : 3 ^ 2 ^ n ≥ 1 := h₄
        have h₅₃ : 3 ^ 2 ^ n - 1 = 3 ^ 2 ^ n - 1 := rfl
        have h₅₄ : (3 ^ 2 ^ n - 1) % 2 ^ (n + 3) = (3 ^ 2 ^ n % 2 ^ (n + 3) - 1) % 2 ^ (n + 3) := by
          rw [← Nat.mod_add_div (3 ^ 2 ^ n) (2 ^ (n + 3))]
          simp [h₅₁, Nat.add_sub_assoc, Nat.add_sub_cancel, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
          <;>
          (try omega) <;>
          (try
            {
              ring_nf at *
              <;>
              omega
            })
        exact h₅₄
      rw [h₅]
      have h₆ : (3 ^ 2 ^ n % 2 ^ (n + 3) - 1) % 2 ^ (n + 3) = (1 + 2 ^ (n + 2) - 1) % 2 ^ (n + 3) := by
        rw [h₁]
        <;>
        (try omega) <;>
        (try
          {
            ring_nf at *
            <;>
            omega
          })
      rw [h₆]
      have h₇ : (1 + 2 ^ (n + 2) - 1) % 2 ^ (n + 3) = 2 ^ (n + 2) := by
        have h₇₁ : 1 + 2 ^ (n + 2) - 1 = 2 ^ (n + 2) := by
          have h₇₂ : 2 ^ (n + 2) ≥ 1 := by
            apply Nat.one_le_pow
            <;> omega
          omega
        rw [h₇₁]
        <;>
        (try omega) <;>
        (try
          {
            ring_nf at *
            <;>
            omega
          })
      rw [h₇]
    exact h₂
  exact h_main
