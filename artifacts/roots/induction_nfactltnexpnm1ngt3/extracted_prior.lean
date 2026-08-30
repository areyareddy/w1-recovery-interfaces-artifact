theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  have h₁ : ∀ (k : ℕ), 3 ≤ k → k ! < k ^ (k - 1) := by
    intro k hk
    have h₂ : ∀ (n : ℕ), 3 ≤ n → n ! < n ^ (n - 1) := by
      intro n hn
      induction' hn with n hn IH
      · -- Base case: n = 3
        norm_num [Nat.factorial]
      · -- Inductive step: assume the statement holds for n, prove for n + 1
        cases n with
        | zero => contradiction -- n cannot be zero since hn : 3 ≤ n
        | succ n =>
          cases n with
          | zero => contradiction -- n cannot be one since hn : 3 ≤ n
          | succ n =>
            cases n with
            | zero => contradiction -- n cannot be two since hn : 3 ≤ n
            | succ n =>
              simp_all [Nat.factorial_succ, Nat.pow_succ, Nat.mul_assoc]
              <;>
                (try omega) <;>
                (try
                  {
                    nlinarith [pow_pos (by omega : 0 < n.succ.succ.succ.succ) n.succ.succ.succ,
                      pow_pos (by omega : 0 < n.succ.succ.succ.succ) n.succ.succ.succ]
                  }) <;>
                (try
                  {
                    have h₃ : n.succ.succ.succ.succ > 0 := by omega
                    have h₄ : n.succ.succ.succ.succ ^ (n.succ.succ.succ.succ - 1) > 0 := by positivity
                    nlinarith [pow_pos (by omega : 0 < n.succ.succ.succ.succ) n.succ.succ.succ.succ,
                      pow_pos (by omega : 0 < n.succ.succ.succ.succ) n.succ.succ.succ.succ]
                  }) <;>
                (try
                  {
                    have h₃ : n.succ.succ.succ.succ > 0 := by omega
                    have h₄ : n.succ.succ.succ.succ ^ (n.succ.succ.succ.succ - 1) > 0 := by positivity
                    nlinarith [pow_pos (by omega : 0 < n.succ.succ.succ.succ) n.succ.succ.succ.succ,
                      pow_pos (by omega : 0 < n.succ.succ.succ.succ) n.succ.succ.succ.succ]
                  })
    exact h₂ k hk
  have h₂ : n ! < n ^ (n - 1) := by
    have h₃ : 3 ≤ n := h₀
    have h₄ : n ! < n ^ (n - 1) := h₁ n h₃
    exact h₄
  exact h₂
