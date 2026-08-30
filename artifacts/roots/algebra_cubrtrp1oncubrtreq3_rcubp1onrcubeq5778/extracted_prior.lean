theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 (r : ℝ)
    (h₀ : r ^ ((1 : ℝ) / 3) + 1 / r ^ ((1 : ℝ) / 3) = 3) : r ^ 3 + 1 / r ^ 3 = 5778 := by
  have h_main : r ^ 3 + 1 / r ^ 3 = 5778 := by
    have h₁ : r ≠ 0 := by
      by_contra h
      rw [h] at h₀
      norm_num at h₀ ⊢
      <;>
      (try simp_all [Real.rpow_def_of_pos]) <;>
      (try ring_nf at * <;> nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1) 3]) <;>
      (try field_simp at * <;> nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1) 3])
      <;>
      (try
        {
          simp_all [Real.rpow_def_of_pos]
          <;>
          ring_nf at * <;>
          nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1) 3]
        })
    -- Use the given condition to find the value of r^3 + 1 / r^3
    have h₂ : r ^ ((1 : ℝ) / 3) + 1 / r ^ ((1 : ℝ) / 3) = 3 := h₀
    have h₃ : (r ^ ((1 : ℝ) / 3)) ^ 3 = r := by
      rw [← Real.rpow_nat_cast]
      rw [← Real.rpow_mul] <;> ring_nf <;>
      norm_num <;>
      linarith
    have h₄ : (r ^ ((1 : ℝ) / 3)) ^ 3 = r := by
      rw [← Real.rpow_nat_cast]
      rw [← Real.rpow_mul] <;> ring_nf <;>
      norm_num <;>
      linarith
    have h₅ : r ^ 3 + 1 / r ^ 3 = 5778 := by
      have h₆ : r ^ ((1 : ℝ) / 3) + 1 / r ^ ((1 : ℝ) / 3) = 3 := h₂
      have h₇ : (r ^ ((1 : ℝ) / 3)) ^ 3 = r := by
        rw [← Real.rpow_nat_cast]
        rw [← Real.rpow_mul] <;> ring_nf <;>
        norm_num <;>
        linarith
      have h₈ : (r ^ ((1 : ℝ) / 3)) ^ 3 = r := by
        rw [← Real.rpow_nat_cast]
        rw [← Real.rpow_mul] <;> ring_nf <;>
        norm_num <;>
        linarith
      -- Use the given condition to find the value of r^3 + 1 / r^3
      field_simp [h₁] at h₆ ⊢
      ring_nf at h₆ ⊢
      nlinarith [sq_nonneg (r ^ ((1 : ℝ) / 3) - 1),
        sq_nonneg (r ^ ((1 : ℝ) / 3) + 1),
        sq_nonneg (r ^ ((1 : ℝ) / 3) - 2),
        sq_nonneg (r ^ ((1 : ℝ) / 3) + 2),
        Real.sq_sqrt (show 0 ≤ 5 by norm_num),
        Real.sq_sqrt (show 0 ≤ 3 by norm_num),
        Real.sq_sqrt (show 0 ≤ 1 by norm_num)]
    exact h₅
  exact h_main
