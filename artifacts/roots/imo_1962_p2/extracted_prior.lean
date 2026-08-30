theorem imo_1962_p2 (x : ℝ) (h₀ : 0 ≤ 3 - x) (h₁ : 0 ≤ x + 1)
    (h₂ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)) : -1 ≤ x ∧ x < 1 - Real.sqrt 31 / 8 := by
  have h₃ : -1 ≤ x := by
    have h₃ : 0 ≤ x + 1 := h₁
    linarith
  
  have h₄ : x < 1 - Real.sqrt 31 / 8 := by
    have h₄ : 0 ≤ Real.sqrt 31 := Real.sqrt_nonneg _
    have h₅ : 0 ≤ Real.sqrt (3 - x) := Real.sqrt_nonneg _
    have h₆ : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg _
    have h₇ : Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 2 := by linarith
    have h₈ : Real.sqrt (3 - x) > Real.sqrt (x + 1) + 1 / 2 := by linarith
    have h₉ : 0 ≤ Real.sqrt (3 - x) * Real.sqrt (x + 1) := by positivity
    have h₁₀ : (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 > (1 / 2) ^ 2 := by
      have h₁₀ : Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 2 := by linarith
      have h₁₁ : (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 > (1 / 2) ^ 2 := by
        have h₁₂ : Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 2 := by linarith
        have h₁₃ : (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 > (1 / 2) ^ 2 := by
          nlinarith [sq_nonneg (Real.sqrt (3 - x) - Real.sqrt (x + 1) - 1 / 2)]
        exact h₁₃
      exact h₁₁
    have h₁₁ : (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 > (1 / 2) ^ 2 := by linarith
    have h₁₂ : (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 > 1 / 4 := by
      norm_num at h₁₁ ⊢
      <;> nlinarith
    have h₁₃ : (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 > 1 / 4 := by linarith
    have h₁₄ : 64 * x ^ 2 - 128 * x - 417 > 0 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 3 - x by linarith), Real.sq_sqrt (show 0 ≤ x + 1 by linarith),
        sq_nonneg (Real.sqrt (3 - x) - Real.sqrt (x + 1) - 1 / 2),
        sq_nonneg (Real.sqrt (3 - x) + Real.sqrt (x + 1) - 2),
        sq_nonneg (Real.sqrt (3 - x) - Real.sqrt (x + 1) + 1 / 2),
        sq_nonneg (Real.sqrt (3 - x) + Real.sqrt (x + 1) + 2)]
    have h₁₅ : x < 1 - Real.sqrt 31 / 8 := by
      nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num),
        sq_nonneg (x - (1 - Real.sqrt 31 / 8)),
        sq_nonneg (x + (1 - Real.sqrt 31 / 8)),
        Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num),
        sq_nonneg (x - (1 - Real.sqrt 31 / 8)),
        sq_nonneg (x + (1 - Real.sqrt 31 / 8))]
    exact h₁₅
  
  exact ⟨h₃, h₄⟩
