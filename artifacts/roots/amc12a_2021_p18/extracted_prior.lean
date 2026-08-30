theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f (25 /. 11) < 0 := by
  have h₂ : f 1 = 0 := by
    have h₂₁ : f (1 * 1 : ℚ) = f 1 + f 1 := by
      apply h₀
      · norm_num
      · norm_num
    have h₂₂ : f (1 * 1 : ℚ) = f 1 := by norm_num
    have h₂₃ : f 1 + f 1 = f 1 := by linarith
    have h₂₄ : f 1 = 0 := by linarith
    exact h₂₄
  
  have h₃ : ∀ (p : ℕ), Nat.Prime p → f (1 / (p : ℚ)) = - (p : ℝ) := by
    intro p hp
    have h₃₁ : f (p : ℚ) = (p : ℝ) := by
      have h₃₂ : f (p : ℚ) = (p : ℝ) := by
        have h₃₃ : f (p : ℚ) = (p : ℝ) := by
          have h₃₄ : f (p : ℚ) = (p : ℝ) := by
            simpa [Nat.cast_inj] using h₁ p hp
          exact h₃₄
        exact h₃₃
      exact h₃₂
    have h₃₂ : f ((p : ℚ) * (1 / (p : ℚ))) = f (p : ℚ) + f (1 / (p : ℚ)) := by
      apply h₀
      · exact by
          norm_num [hp.pos]
          <;>
          positivity
      · exact by
          norm_num [hp.pos]
          <;>
          positivity
    have h₃₃ : f ((p : ℚ) * (1 / (p : ℚ))) = f 1 := by
      have h₃₄ : (p : ℚ) * (1 / (p : ℚ)) = 1 := by
        field_simp [hp.ne_zero]
        <;>
        norm_num
      rw [h₃₄]
    have h₃₄ : f 1 = 0 := h₂
    have h₃₅ : f (p : ℚ) + f (1 / (p : ℚ)) = 0 := by
      linarith
    have h₃₆ : f (1 / (p : ℚ)) = - (p : ℝ) := by
      have h₃₇ : f (p : ℚ) = (p : ℝ) := h₃₁
      have h₃₈ : f (p : ℚ) + f (1 / (p : ℚ)) = 0 := h₃₅
      have h₃₉ : (p : ℝ) + f (1 / (p : ℚ)) = 0 := by
        rw [h₃₇] at h₃₈
        exact h₃₈
      have h₄₀ : f (1 / (p : ℚ)) = - (p : ℝ) := by
        linarith
      exact h₄₀
    exact h₃₆
  
  have h₄ : f (25 / 11 : ℚ) = -1 := by
    have h₄₁ : f (25 / 11 : ℚ) = f (25 * (1 / 11 : ℚ)) := by norm_num
    rw [h₄₁]
    have h₄₂ : f (25 * (1 / 11 : ℚ)) = f (25 : ℚ) + f (1 / 11 : ℚ) := by
      apply h₀
      · norm_num
      · norm_num
    rw [h₄₂]
    have h₄₃ : f (25 : ℚ) = (25 : ℝ) := by
      have h₄₄ : f (25 : ℚ) = (25 : ℝ) := by
        have h₄₅ : f (25 : ℚ) = (25 : ℝ) := by
          have h₄₆ : f (25 : ℚ) = f (5 * 5 : ℚ) := by norm_num
          rw [h₄₆]
          have h₄₇ : f (5 * 5 : ℚ) = f (5 : ℚ) + f (5 : ℚ) := by
            apply h₀
            · norm_num
            · norm_num
          rw [h₄₇]
          have h₄₈ : f (5 : ℚ) = (5 : ℝ) := by
            have h₄₉ : f (5 : ℚ) = (5 : ℝ) := by
              have h₅₀ : Nat.Prime 5 := by decide
              have h₅₁ : f (5 : ℚ) = (5 : ℝ) := by
                simpa [Nat.cast_inj] using h₁ 5 h₅₀
              exact h₅₁
            exact h₄₉
          rw [h₄₈]
          <;> norm_num
        exact h₄₅
      exact h₄₄
    have h₄₄ : f (1 / 11 : ℚ) = (-11 : ℝ) := by
      have h₄₅ : f (1 / 11 : ℚ) = (-11 : ℝ) := by
        have h₄₆ : Nat.Prime 11 := by decide
        have h₄₇ : f (1 / (11 : ℚ)) = (- (11 : ℝ)) := by
          apply h₃
          <;> decide
        simpa [Nat.cast_inj] using h₄₇
      exact h₄₅
    rw [h₄₃, h₄₄]
    <;> norm_num
    <;> linarith
  
  have h₅ : f (25 /. 11 : ℚ) < 0 := by
    rw [h₄]
    <;> norm_num
    <;> linarith
  
  exact h₅
