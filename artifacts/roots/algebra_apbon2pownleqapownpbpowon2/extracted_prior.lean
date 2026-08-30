theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  have h_main : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < b := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < a ^ n := by positivity
    have h₆ : 0 < b ^ n := by positivity
    have h₇ : 0 < a ^ n * b ^ n := by positivity
    -- Use the fact that the function \( f(x) = x^n \) is convex for \( n \geq 1 \)
    have h₈ : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
      -- Use the Power Mean Inequality to prove the inequality
      have h₉ : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
        -- Use the Power Mean Inequality to prove the inequality
        have h₁₀ : ∀ n : ℕ, 0 < n → ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
          intro n hn
          induction' hn with n hn IH
          · -- Base case: n = 1
            norm_num
            <;>
            nlinarith [sq_nonneg (a - b)]
          · -- Inductive step: assume the inequality holds for n, prove for n + 1
            simp_all [pow_succ, mul_add, mul_comm, mul_left_comm, mul_assoc]
            <;>
            nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ n - b ^ n),
              mul_nonneg h₂.le h₃.le, mul_nonneg (sq_nonneg (a - b)) h₂.le,
              mul_nonneg (sq_nonneg (a - b)) h₃.le, mul_nonneg (sq_nonneg (a + b)) h₂.le,
              mul_nonneg (sq_nonneg (a + b)) h₃.le, pow_nonneg h₂.le n, pow_nonneg h₃.le n,
              pow_nonneg (sq_nonneg (a - b)) n, pow_nonneg (sq_nonneg (a + b)) n]
        exact h₁₀ n h₁
      exact h₉
    exact h₈
  exact h_main
