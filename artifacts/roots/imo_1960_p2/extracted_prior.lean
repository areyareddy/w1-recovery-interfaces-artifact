theorem imo_1960_p2 (x : ℝ) (h₀ : 0 ≤ 1 + 2 * x) (h₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0)
    (h₂ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9) : -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  have h_main₁ : -(1 / 2 : ℝ) ≤ x := by
    have h₃ : 0 ≤ 1 + 2 * x := h₀
    have h₄ : -(1 / 2 : ℝ) ≤ x := by
      -- Use the fact that the square root of a non-negative number is non-negative to derive the inequality.
      nlinarith [Real.sqrt_nonneg (1 + 2 * x)]
    exact h₄
  
  have h_main₂ : x < 45 / 8 := by
    have h₃ : 0 ≤ 1 + 2 * x := h₀
    have h₄ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0 := h₁
    have h₅ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 := h₂
    have h₆ : 0 ≤ Real.sqrt (1 + 2 * x) := Real.sqrt_nonneg _
    have h₇ : Real.sqrt (1 + 2 * x) ≥ 0 := by linarith
    have h₈ : 1 + 2 * x ≥ 0 := by nlinarith
    have h₉ : Real.sqrt (1 + 2 * x) ≠ 1 := by
      intro h
      have h₁₀ : Real.sqrt (1 + 2 * x) = 1 := h
      have h₁₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = 0 := by
        rw [h₁₀]
        norm_num
      contradiction
    have h₁₀ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 > 0 := by
      apply lt_of_le_of_ne
      · -- Prove that the square is non-negative
        nlinarith [Real.sq_sqrt (by nlinarith : 0 ≤ 1 + 2 * x)]
      · -- Prove that the square is not zero
        intro h
        apply h₄
        nlinarith
    -- Use the inequality to derive the desired result
    have h₁₁ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 := h₅
    have h₁₂ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 := h₅
    have h₁₃ : x < 45 / 8 := by
      by_contra h
      have h₁₄ : x ≥ 45 / 8 := by linarith
      have h₁₅ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≤ 0 := by
        have h₁₆ : Real.sqrt (1 + 2 * x) ≥ 7 / 2 := by
          apply Real.le_sqrt_of_sq_le
          nlinarith
        have h₁₇ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≤ 0 := by
          nlinarith [Real.sq_sqrt (by nlinarith : 0 ≤ 1 + 2 * x)]
        nlinarith
      have h₁₆ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 > 0 := by
        apply h₁₀
      nlinarith
    exact h₁₃
  
  exact ⟨h_main₁, h_main₂⟩
