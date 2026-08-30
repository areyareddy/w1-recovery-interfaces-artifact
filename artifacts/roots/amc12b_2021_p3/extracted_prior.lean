theorem amc12b_2021_p3 (x : ℝ) (h₀ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53) : x = 3 / 4 := by
  have h₁ : x = 3 / 4 := by
    have h₂ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53 := h₀
    have h₃ : 3 + x ≠ 0 := by
      by_contra h
      rw [h] at h₂
      norm_num at h₂
      <;> simp_all [div_eq_mul_inv]
      <;> ring_nf at *
      <;> field_simp at *
      <;> nlinarith
    have h₄ : 2 + 2 / (3 + x) ≠ 0 := by
      by_contra h
      have h₅ : 2 + 2 / (3 + x) = 0 := by simpa using h
      have h₆ : 2 / (3 + x) = -2 := by linarith
      have h₇ : 3 + x ≠ 0 := by
        intro h₈
        simp_all
        <;> norm_num at *
        <;> linarith
      field_simp at h₆
      <;> nlinarith
    have h₅ : 1 + 1 / (2 + 2 / (3 + x)) ≠ 0 := by
      by_contra h
      have h₆ : 1 + 1 / (2 + 2 / (3 + x)) = 0 := by simpa using h
      have h₇ : 1 / (2 + 2 / (3 + x)) = -1 := by linarith
      have h₈ : 2 + 2 / (3 + x) ≠ 0 := by
        intro h₉
        simp_all
        <;> norm_num at *
        <;> linarith
      field_simp at h₇
      <;> nlinarith
    have h₆ : 1 + 1 / (2 + 2 / (3 + x)) ≠ 0 := by
      by_contra h
      have h₇ : 1 + 1 / (2 + 2 / (3 + x)) = 0 := by simpa using h
      have h₈ : 1 / (2 + 2 / (3 + x)) = -1 := by linarith
      have h₉ : 2 + 2 / (3 + x) ≠ 0 := by
        intro h₁₀
        simp_all
        <;> norm_num at *
        <;> linarith
      field_simp at h₈
      <;> nlinarith
    field_simp at h₂
    ring_nf at h₂
    apply Eq.symm
    ring_nf at h₂ ⊢
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h₃), sq_pos_of_ne_zero (sub_ne_zero.mpr h₄),
      sq_pos_of_ne_zero (sub_ne_zero.mpr h₅), sq_pos_of_ne_zero (sub_ne_zero.mpr h₆)]
  exact h₁
