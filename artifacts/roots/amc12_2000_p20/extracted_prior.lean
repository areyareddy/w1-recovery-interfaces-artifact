theorem amc12_2000_p20 (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x + 1 / y = 4)
    (h₂ : y + 1 / z = 1) (h₃ : z + 1 / x = 7 / 3) : x * y * z = 1 := by
  have h₄ : y = 1 / (4 - x) := by
    have h₄₁ : 0 < y := h₀.2.1
    have h₄₂ : 0 < x := h₀.1
    have h₄₃ : x + 1 / y = 4 := h₁
    have h₄₄ : 1 / y = 4 - x := by linarith
    have h₄₅ : y = 1 / (4 - x) := by
      have h₄₅₁ : 4 - x ≠ 0 := by
        by_contra h
        have h₄₅₂ : 4 - x = 0 := by linarith
        have h₄₅₃ : x = 4 := by linarith
        have h₄₅₄ : 1 / y = 0 := by
          rw [h₄₅₃] at h₄₄
          norm_num at h₄₄ ⊢
          <;> linarith
        have h₄₅₅ : y > 0 := h₄₁
        have h₄₅₆ : 1 / y > 0 := by positivity
        linarith
      have h₄₅₇ : y = 1 / (4 - x) := by
        field_simp at h₄₄ ⊢
        <;> nlinarith
      exact h₄₅₇
    exact h₄₅
  
  have h₅ : z = (4 - x) / (3 - x) := by
    have h₅₁ : 0 < y := h₀.2.1
    have h₅₂ : 0 < x := h₀.1
    have h₅₃ : 0 < z := h₀.2.2
    have h₅₄ : y + 1 / z = 1 := h₂
    have h₅₅ : y = 1 / (4 - x) := h₄
    have h₅₆ : 1 / z = 1 - y := by linarith
    have h₅₇ : 1 / z = 1 - 1 / (4 - x) := by rw [h₅₅] at h₅₆; exact h₅₆
    have h₅₈ : 1 / z = (3 - x) / (4 - x) := by
      have h₅₈₁ : 1 - 1 / (4 - x) = (3 - x) / (4 - x) := by
        have h₅₈₂ : 4 - x ≠ 0 := by
          by_contra h
          have h₅₈₃ : 4 - x = 0 := by linarith
          have h₅₈₄ : x = 4 := by linarith
          have h₅₈₅ : 1 / y = 0 := by
            rw [h₅₈₄] at h₅₅
            norm_num at h₅₅ ⊢
            <;> linarith
          have h₅₈₆ : y > 0 := h₅₁
          have h₅₈₇ : 1 / y > 0 := by positivity
          linarith
        field_simp at h₅₇ ⊢
        <;> ring_nf at h₅₇ ⊢ <;> nlinarith
      rw [h₅₈₁] at h₅₇
      exact h₅₇
    have h₅₉ : z = (4 - x) / (3 - x) := by
      have h₅₉₁ : 1 / z = (3 - x) / (4 - x) := h₅₈
      have h₅₉₂ : 3 - x ≠ 0 := by
        by_contra h
        have h₅₉₃ : 3 - x = 0 := by linarith
        have h₅₉₄ : x = 3 := by linarith
        have h₅₉₅ : 1 / z = 0 := by
          rw [h₅₉₄] at h₅₉₁
          norm_num at h₅₉₁ ⊢
          <;> linarith
        have h₅₉₆ : z > 0 := h₅₃
        have h₅₉₇ : 1 / z > 0 := by positivity
        linarith
      have h₅₉₈ : 4 - x ≠ 0 := by
        by_contra h
        have h₅₉₉ : 4 - x = 0 := by linarith
        have h₅₉₁₀ : x = 4 := by linarith
        have h₅₉₁₁ : 1 / y = 0 := by
          rw [h₅₉₁₀] at h₅₅
          norm_num at h₅₅ ⊢
          <;> linarith
        have h₅₉₁₂ : y > 0 := h₅₁
        have h₅₉₁₃ : 1 / y > 0 := by positivity
        linarith
      have h₅₉₁₄ : z = (4 - x) / (3 - x) := by
        have h₅₉₁₅ : 1 / z = (3 - x) / (4 - x) := h₅₉₁
        have h₅₉₁₆ : z = (4 - x) / (3 - x) := by
          have h₅₉₁₇ : z ≠ 0 := by linarith
          field_simp at h₅₉₁₅ ⊢
          <;> ring_nf at h₅₉₁₅ ⊢ <;> nlinarith
        exact h₅₉₁₆
      exact h₅₉₁₄
    exact h₅₉
  
  have h₆ : x * y * z = x / (3 - x) := by
    have h₆₁ : y = 1 / (4 - x) := h₄
    have h₆₂ : z = (4 - x) / (3 - x) := h₅
    rw [h₆₁, h₆₂]
    have h₆₃ : 3 - x ≠ 0 := by
      by_contra h
      have h₆₄ : 3 - x = 0 := by linarith
      have h₆₅ : x = 3 := by linarith
      have h₆₆ : 0 < x := h₀.1
      have h₆₇ : 0 < y := h₀.2.1
      have h₆₈ : 0 < z := h₀.2.2
      have h₆₉ : x + 1 / y = 4 := h₁
      have h₇₀ : y + 1 / z = 1 := h₂
      have h₇₁ : z + 1 / x = 7 / 3 := h₃
      rw [h₆₅] at h₆₉
      have h₇₂ : (3 : ℝ) + 1 / y = 4 := by simpa using h₆₉
      have h₇₃ : 1 / y = 1 := by linarith
      have h₇₄ : y = 1 := by
        have h₇₄₁ : y > 0 := h₆₇
        have h₇₄₂ : 1 / y = 1 := h₇₃
        field_simp at h₇₄₂ ⊢
        <;> nlinarith
      have h₇₅ : y = 1 := h₇₄
      rw [h₇₅] at h₇₀
      have h₇₆ : (1 : ℝ) + 1 / z = 1 := by simpa using h₇₀
      have h₇₇ : 1 / z = 0 := by linarith
      have h₇₈ : z > 0 := h₆₈
      have h₇₉ : 1 / z > 0 := by positivity
      linarith
    have h₆₄ : 4 - x ≠ 0 := by
      by_contra h
      have h₆₅ : 4 - x = 0 := by linarith
      have h₆₆ : x = 4 := by linarith
      have h₆₇ : 0 < x := h₀.1
      have h₆₈ : 0 < y := h₀.2.1
      have h₆₉ : 0 < z := h₀.2.2
      have h₇₀ : x + 1 / y = 4 := h₁
      have h₇₁ : y + 1 / z = 1 := h₂
      have h₇₂ : z + 1 / x = 7 / 3 := h₃
      rw [h₆₆] at h₇₀
      have h₇₃ : (4 : ℝ) + 1 / y = 4 := by simpa using h₇₀
      have h₇₄ : 1 / y = 0 := by linarith
      have h₇₅ : y > 0 := h₆₈
      have h₇₆ : 1 / y > 0 := by positivity
      linarith
    field_simp [h₆₃, h₆₄, sub_ne_zero]
    <;> ring_nf
    <;> field_simp [h₆₃, h₆₄, sub_ne_zero] at *
    <;> nlinarith
  
  have h₇ : z = 7 / 3 - 1 / x := by
    have h₇₁ : z + 1 / x = 7 / 3 := h₃
    have h₇₂ : z = 7 / 3 - 1 / x := by linarith
    exact h₇₂
  
  have h₈ : (4 : ℝ) * x ^ 2 - 12 * x + 9 = 0 := by
    have h₈₁ : z = 7 / 3 - 1 / x := h₇
    have h₈₂ : z = (4 - x) / (3 - x) := h₅
    have h₈₃ : (4 - x) / (3 - x) = 7 / 3 - 1 / x := by linarith
    have h₈₄ : 3 - x ≠ 0 := by
      by_contra h
      have h₈₅ : 3 - x = 0 := by linarith
      have h₈₆ : x = 3 := by linarith
      have h₈₇ : 0 < x := h₀.1
      have h₈₈ : 0 < y := h₀.2.1
      have h₈₉ : 0 < z := h₀.2.2
      have h₉₀ : x + 1 / y = 4 := h₁
      have h₉₁ : y + 1 / z = 1 := h₂
      have h₉₂ : z + 1 / x = 7 / 3 := h₃
      rw [h₈₆] at h₉₀
      have h₉₃ : (3 : ℝ) + 1 / y = 4 := by simpa using h₉₀
      have h₉₄ : 1 / y = 1 := by linarith
      have h₉₅ : y = 1 := by
        have h₉₅₁ : y > 0 := h₈₈
        have h₉₅₂ : 1 / y = 1 := h₉₄
        field_simp at h₉₅₂ ⊢
        <;> nlinarith
      have h₉₆ : y = 1 := h₉₅
      rw [h₉₆] at h₉₁
      have h₉₇ : (1 : ℝ) + 1 / z = 1 := by simpa using h₉₁
      have h₉₈ : 1 / z = 0 := by linarith
      have h₉₉ : z > 0 := h₈₉
      have h₁₀₀ : 1 / z > 0 := by positivity
      linarith
    have h₈₅ : x ≠ 0 := by linarith
    have h₈₆ : 3 - x ≠ 0 := h₈₄
    have h₈₇ : x ≠ 0 := h₈₅
    field_simp at h₈₃
    ring_nf at h₈₃ ⊢
    nlinarith [sq_nonneg (x - 3 / 2)]
  
  have h₉ : x = 3 / 2 := by
    have h₉₁ : (4 : ℝ) * x ^ 2 - 12 * x + 9 = 0 := h₈
    have h₉₂ : x = 3 / 2 := by
      have h₉₃ : (2 * x - 3) ^ 2 = 0 := by
        nlinarith
      have h₉₄ : 2 * x - 3 = 0 := by
        nlinarith
      nlinarith
    exact h₉₂
  
  have h₁₀ : x * y * z = 1 := by
    have h₁₀₁ : x * y * z = x / (3 - x) := h₆
    have h₁₀₂ : x = 3 / 2 := h₉
    rw [h₁₀₂] at h₁₀₁
    have h₁₀₃ : (3 : ℝ) - (3 / 2 : ℝ) ≠ 0 := by norm_num
    have h₁₀₄ : (3 / 2 : ℝ) / (3 - (3 / 2 : ℝ)) = 1 := by norm_num
    rw [h₁₀₁]
    <;> norm_num [h₁₀₄]
    <;> linarith
  
  exact h₁₀
