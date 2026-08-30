theorem imo_1982_p1 (f : ℕ → ℕ)
    (h₀ : ∀ m n, 0 < m ∧ 0 < n → f (m + n) - f m - f n = 0 ∨ f (m + n) - f m - f n = 1)
    (h₁ : f 2 = 0) (h₂ : 0 < f 3) (h₃ : f 9999 = 3333) : f 1982 = 660 := by
  have h_main : f 1982 = 660 := by
    have h₄ := h₀ 1 1 ⟨by norm_num, by norm_num⟩
    have h₅ := h₀ 2 1 ⟨by norm_num, by norm_num⟩
    have h₆ := h₀ 1 2 ⟨by norm_num, by norm_num⟩
    have h₇ := h₀ 3 1 ⟨by norm_num, by norm_num⟩
    have h₈ := h₀ 1 3 ⟨by norm_num, by norm_num⟩
    have h₉ := h₀ 2 2 ⟨by norm_num, by norm_num⟩
    have h₁₀ := h₀ 3 2 ⟨by norm_num, by norm_num⟩
    have h₁₁ := h₀ 2 3 ⟨by norm_num, by norm_num⟩
    have h₁₂ := h₀ 3 3 ⟨by norm_num, by norm_num⟩
    have h₁₃ := h₀ 4 1 ⟨by norm_num, by norm_num⟩
    have h₁₄ := h₀ 1 4 ⟨by norm_num, by norm_num⟩
    have h₁₅ := h₀ 4 2 ⟨by norm_num, by norm_num⟩
    have h₁₆ := h₀ 2 4 ⟨by norm_num, by norm_num⟩
    have h₁₇ := h₀ 4 3 ⟨by norm_num, by norm_num⟩
    have h₁₈ := h₀ 3 4 ⟨by norm_num, by norm_num⟩
    have h₁₉ := h₀ 5 1 ⟨by norm_num, by norm_num⟩
    have h₂₀ := h₀ 1 5 ⟨by norm_num, by norm_num⟩
    have h₂₁ := h₀ 5 2 ⟨by norm_num, by norm_num⟩
    have h₂₂ := h₀ 2 5 ⟨by norm_num, by norm_num⟩
    have h₂₃ := h₀ 5 3 ⟨by norm_num, by norm_num⟩
    have h₂₄ := h₀ 3 5 ⟨by norm_num, by norm_num⟩
    have h₂₅ := h₀ 5 4 ⟨by norm_num, by norm_num⟩
    have h₂₆ := h₀ 4 5 ⟨by norm_num, by norm_num⟩
    -- Normalize the numbers to simplify the expressions
    norm_num [h₁] at h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇ h₁₈ h₁₉ h₂₀ h₂₁ h₂₂ h₂₃ h₂₄ h₂₅ h₂₆
    -- Use the omega tactic to solve the resulting system of equations
    <;>
    (try omega) <;>
    (try
      {
        omega
      }) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        simp_all [Nat.sub_eq_zero_iff_le]
        <;> omega
      })
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        omega
      })
  exact h_main
