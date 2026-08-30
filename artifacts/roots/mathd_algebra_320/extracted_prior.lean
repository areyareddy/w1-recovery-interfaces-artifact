theorem mathd_algebra_320 (x : ℝ) (a b c : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 ≤ x)
    (h₁ : 2 * x ^ 2 = 4 * x + 9) (h₂ : x = (a + Real.sqrt b) / c) (h₃ : c = 2) : a + b + c = 26 := by
  have h₄ : a = 2 := by
    have h₄₁ : (a : ℝ) + Real.sqrt b = 2 + Real.sqrt 22 := by
      have h₄₂ : x = (a + Real.sqrt b : ℝ) / c := by simpa using h₂
      have h₄₃ : x = (2 + Real.sqrt 22 : ℝ) / 2 := by
        have h₄₄ : 2 * x ^ 2 = 4 * x + 9 := h₁
        have h₄₅ : x = (2 + Real.sqrt 22 : ℝ) / 2 ∨ x = (2 - Real.sqrt 22 : ℝ) / 2 := by
          apply or_iff_not_imp_left.mpr
          intro h
          apply mul_left_cancel₀ (sub_ne_zero_of_ne h)
          nlinarith [Real.sq_sqrt (show 0 ≤ 22 by norm_num), Real.sqrt_nonneg 22,
            sq_nonneg (x - (2 + Real.sqrt 22) / 2), sq_nonneg (x - (2 - Real.sqrt 22) / 2)]
        cases h₄₅ with
        | inl h₄₅ =>
          exact h₄₅
        | inr h₄₅ =>
          have h₄₆ : x ≥ 0 := h₀.2.2.2
          have h₄₇ : (2 - Real.sqrt 22 : ℝ) / 2 < 0 := by
            nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num)]
          linarith
      have h₄₈ : (a + Real.sqrt b : ℝ) / c = (2 + Real.sqrt 22 : ℝ) / 2 := by
        linarith
      have h₄₉ : c = 2 := h₃
      rw [h₄₉] at h₄₈
      ring_nf at h₄₈ ⊢
      linarith
    have h₄₁₀ : (a : ℝ) + Real.sqrt b = 2 + Real.sqrt 22 := h₄₁
    have h₄₁₁ : a = 2 := by
      have h₄₁₂ : 0 < a := h₀.1
      have h₄₁₃ : 0 < b := h₀.2.1
      have h₄₁₄ : 0 < c := h₀.2.2.1
      have h₄₁₅ : 0 ≤ x := h₀.2.2.2
      -- Use the fact that the square root of a natural number is irrational unless it's a perfect square
      have h₄₁₆ : Real.sqrt b ≥ 0 := Real.sqrt_nonneg b
      have h₄₁₇ : Real.sqrt 22 ≥ 0 := Real.sqrt_nonneg 22
      have h₄₁₈ : (a : ℝ) = 2 := by
        -- Use the fact that the square root of a natural number is irrational unless it's a perfect square
        have h₄₁₉ : Real.sqrt b = 2 + Real.sqrt 22 - (a : ℝ) := by linarith
        have h₄₂₀ : (Real.sqrt b : ℝ) ^ 2 = (2 + Real.sqrt 22 - (a : ℝ)) ^ 2 := by rw [h₄₁₉]
        have h₄₂₁ : (b : ℝ) = (2 + Real.sqrt 22 - (a : ℝ)) ^ 2 := by
          have h₄₂₂ : (Real.sqrt b : ℝ) ^ 2 = (b : ℝ) := by
            rw [Real.sq_sqrt (by positivity)]
          rw [h₄₂₂] at h₄₂₀
          exact h₄₂₀
        have h₄₂₃ : (b : ℝ) = (2 + Real.sqrt 22 - (a : ℝ)) ^ 2 := h₄₂₁
        have h₄₂₄ : (b : ℝ) = (2 + Real.sqrt 22 - (a : ℝ)) ^ 2 := h₄₂₃
        have h₄₂₅ : (a : ℝ) ≥ 1 := by
          exact_mod_cast Nat.succ_le_iff.mpr h₄₁₂
        have h₄₂₆ : (a : ℝ) ≤ 26 := by
          by_contra h
          have h₄₂₇ : (a : ℝ) > 26 := by linarith
          have h₄₂₈ : (b : ℝ) > 26 := by
            nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num),
              sq_nonneg ((a : ℝ) - 2), sq_nonneg ((a : ℝ) - 1)]
          have h₄₂₉ : (b : ℕ) > 26 := by
            exact_mod_cast h₄₂₈
          have h₄₃₀ : (b : ℕ) ≥ 27 := by linarith
          have h₄₃₁ : (b : ℝ) ≥ 27 := by exact_mod_cast h₄₃₀
          nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num),
            sq_nonneg ((a : ℝ) - 2), sq_nonneg ((a : ℝ) - 1)]
        have h₄₃₂ : (a : ℕ) ≤ 26 := by
          exact_mod_cast h₄₂₆
        interval_cases a <;> norm_num at h₄₂₄ ⊢ <;>
          (try norm_num at h₄₁₉ ⊢) <;>
          (try {
            nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num),
              Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ (b : ℝ) by positivity)]
          }) <;>
          (try {
            have h₄₃₃ : Real.sqrt b = 2 + Real.sqrt 22 - (2 : ℝ) := by linarith
            have h₄₃₄ : Real.sqrt b = Real.sqrt 22 := by linarith
            have h₄₃₅ : (b : ℝ) = 22 := by
              have h₄₃₆ : Real.sqrt b = Real.sqrt 22 := h₄₃₄
              have h₄₃₇ : (Real.sqrt b : ℝ) ^ 2 = (Real.sqrt 22 : ℝ) ^ 2 := by rw [h₄₃₆]
              have h₄₃₈ : (b : ℝ) = 22 := by
                nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ (b : ℝ) by positivity),
                  Real.sq_sqrt (show 0 ≤ (22 : ℝ) by norm_num)]
              exact h₄₃₈
            have h₄₃₉ : (b : ℕ) = 22 := by
              exact_mod_cast h₄₃₅
            simp_all
            <;> norm_num
            <;> linarith
          }) <;>
          (try {
            have h₄₃₃ : Real.sqrt b = 2 + Real.sqrt 22 - (1 : ℝ) := by linarith
            have h₄₃₄ : Real.sqrt b = 1 + Real.sqrt 22 := by linarith
            have h₄₃₅ : (b : ℝ) = (1 + Real.sqrt 22) ^ 2 := by
              have h₄₃₆ : Real.sqrt b = 1 + Real.sqrt 22 := h₄₃₄
              have h₄₃₇ : (Real.sqrt b : ℝ) ^ 2 = (1 + Real.sqrt 22 : ℝ) ^ 2 := by rw [h₄₃₆]
              have h₄₃₈ : (b : ℝ) = (1 + Real.sqrt 22 : ℝ) ^ 2 := by
                nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ (b : ℝ) by positivity),
                  Real.sq_sqrt (show 0 ≤ (22 : ℝ) by norm_num)]
              exact h₄₃₈
            have h₄₃₉ : (b : ℝ) = (1 + Real.sqrt 22) ^ 2 := h₄₃₅
            have h₄₄₀ : (b : ℕ) = 45 := by
              have h₄₄₁ : (b : ℝ) = (1 + Real.sqrt 22) ^ 2 := h₄₃₉
              have h₄₄₂ : (b : ℝ) = 1 + 2 * Real.sqrt 22 + 22 := by
                nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num)]
              have h₄₄₃ : (b : ℝ) = 23 + 2 * Real.sqrt 22 := by linarith
              have h₄₄₄ : (b : ℕ) = 45 := by
                norm_num at h₄₄₃ ⊢
                <;>
                (try norm_num) <;>
                (try
                  {
                    nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num)]
                  }) <;>
                (try
                  {
                    ring_nf at h₄₄₃ ⊢ <;>
                    nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num)]
                  })
              exact h₄₄₄
            simp_all
            <;> norm_num
            <;> linarith
          }) <;>
          (try {
            have h₄₃₃ : Real.sqrt b = 2 + Real.sqrt 22 - (3 : ℝ) := by linarith
            have h₄₃₄ : Real.sqrt b = -1 + Real.sqrt 22 := by linarith
            have h₄₃₅ : (b : ℝ) = (-1 + Real.sqrt 22) ^ 2 := by
              have h₄₃₆ : Real.sqrt b = -1 + Real.sqrt 22 := h₄₃₄
              have h₄₃₇ : (Real.sqrt b : ℝ) ^ 2 = (-1 + Real.sqrt 22 : ℝ) ^ 2 := by rw [h₄₃₆]
              have h₄₃₈ : (b : ℝ) = (-1 + Real.sqrt 22 : ℝ) ^ 2 := by
                nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ (b : ℝ) by positivity),
                  Real.sq_sqrt (show 0 ≤ (22 : ℝ) by norm_num)]
              exact h₄₃₈
            have h₄₃₉ : (b : ℝ) = (-1 + Real.sqrt 22) ^ 2 := h₄₃₅
            have h₄₄₀ : (b : ℕ) = 43 := by
              have h₄₄₁ : (b : ℝ) = (-1 + Real.sqrt 22) ^ 2 := h₄₃₉
              have h₄₄₂ : (b : ℝ) = 1 - 2 * Real.sqrt 22 + 22 := by
                nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num)]
              have h₄₄₃ : (b : ℝ) = 23 - 2 * Real.sqrt 22 := by linarith
              have h₄₄₄ : (b : ℕ) = 43 := by
                norm_num at h₄₄₃ ⊢
                <;>
                (try norm_num) <;>
                (try
                  {
                    nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num)]
                  }) <;>
                (try
                  {
                    ring_nf at h₄₄₃ ⊢ <;>
                    nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num)]
                  })
              exact h₄₄₄
            simp_all
            <;> norm_num
            <;> linarith
          }) <;>
          (try {
            nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num),
              Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ (b : ℝ) by positivity)]
          })
      have h₄₃₃ : (a : ℕ) = 2 := by
        norm_cast at h₄₁₈ ⊢
        <;> linarith
      exact h₄₃₃
    exact h₄₁₁
  
  have h₅ : b = 22 := by
    have h₅₁ : (a : ℝ) + Real.sqrt b = 2 + Real.sqrt 22 := by
      have h₅₂ : x = (a + Real.sqrt b : ℝ) / c := by simpa using h₂
      have h₅₃ : x = (2 + Real.sqrt 22 : ℝ) / 2 := by
        have h₅₄ : 2 * x ^ 2 = 4 * x + 9 := h₁
        have h₅₅ : x = (2 + Real.sqrt 22 : ℝ) / 2 ∨ x = (2 - Real.sqrt 22 : ℝ) / 2 := by
          apply or_iff_not_imp_left.mpr
          intro h
          apply mul_left_cancel₀ (sub_ne_zero_of_ne h)
          nlinarith [Real.sq_sqrt (show 0 ≤ 22 by norm_num), Real.sqrt_nonneg 22,
            sq_nonneg (x - (2 + Real.sqrt 22) / 2), sq_nonneg (x - (2 - Real.sqrt 22) / 2)]
        cases h₅₅ with
        | inl h₅₅ =>
          exact h₅₅
        | inr h₅₅ =>
          have h₅₆ : x ≥ 0 := h₀.2.2.2
          have h₅₇ : (2 - Real.sqrt 22 : ℝ) / 2 < 0 := by
            nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show 0 ≤ 22 by norm_num)]
          linarith
      have h₅₈ : (a + Real.sqrt b : ℝ) / c = (2 + Real.sqrt 22 : ℝ) / 2 := by
        linarith
      have h₅₉ : c = 2 := h₃
      rw [h₅₉] at h₅₈
      ring_nf at h₅₈ ⊢
      linarith
    have h₅₁₀ : (a : ℝ) + Real.sqrt b = 2 + Real.sqrt 22 := h₅₁
    have h₅₁₁ : a = 2 := h₄
    have h₅₁₂ : (a : ℝ) = 2 := by
      norm_num [h₅₁₁]
    have h₅₁₃ : Real.sqrt b = Real.sqrt 22 := by
      linarith
    have h₅₁₄ : (b : ℝ) = 22 := by
      have h₅₁₅ : Real.sqrt b = Real.sqrt 22 := h₅₁₃
      have h₅₁₆ : (Real.sqrt b : ℝ) ^ 2 = (Real.sqrt 22 : ℝ) ^ 2 := by rw [h₅₁₅]
      have h₅₁₇ : (b : ℝ) = 22 := by
        have h₅₁₈ : (Real.sqrt b : ℝ) ^ 2 = (b : ℝ) := by
          rw [Real.sq_sqrt (by positivity)]
        have h₅₁₉ : (Real.sqrt 22 : ℝ) ^ 2 = 22 := by
          rw [Real.sq_sqrt (by positivity)]
        nlinarith
      exact h₅₁₇
    have h₅₁₅ : (b : ℕ) = 22 := by
      norm_cast at h₅₁₄ ⊢
      <;> linarith
    exact h₅₁₅
  
  have h₆ : a + b + c = 26 := by
    have h₆₁ : a = 2 := h₄
    have h₆₂ : b = 22 := h₅
    have h₆₃ : c = 2 := h₃
    simp [h₆₁, h₆₂, h₆₃]
    <;> norm_num
  
  exact h₆
