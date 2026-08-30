theorem amc12b_2021_p13 (S : Finset ℝ)
    (h₀ :
      ∀ x : ℝ, x ∈ S ↔ 0 < x ∧ x ≤ 2 * Real.pi ∧ 1 - 3 * Real.sin x + 5 * Real.cos (3 * x) = 0) :
    S.card = 6 := by
  have h₁ : S.card = 6 := by
    have h₂ : S = {Real.pi / 6, 5 * Real.pi / 6, Real.pi / 2, 7 * Real.pi / 6, 3 * Real.pi / 2, 11 * Real.pi / 6} := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
      constructor
      · intro h
        have h₃ : 0 < x := h.1
        have h₄ : x ≤ 2 * Real.pi := h.2.1
        have h₅ : 1 - 3 * Real.sin x + 5 * Real.cos (3 * x) = 0 := h.2.2
        have h₆ : x = Real.pi / 6 ∨ x = 5 * Real.pi / 6 ∨ x = Real.pi / 2 ∨ x = 7 * Real.pi / 6 ∨ x = 3 * Real.pi / 2 ∨ x = 11 * Real.pi / 6 := by
          -- Prove that x must be one of the six values
          have h₇ : x = Real.pi / 6 ∨ x = 5 * Real.pi / 6 ∨ x = Real.pi / 2 ∨ x = 7 * Real.pi / 6 ∨ x = 3 * Real.pi / 2 ∨ x = 11 * Real.pi / 6 := by
            -- Use the fact that the equation has six solutions in (0, 2π]
            have h₈ : x = Real.pi / 6 ∨ x = 5 * Real.pi / 6 ∨ x = Real.pi / 2 ∨ x = 7 * Real.pi / 6 ∨ x = 3 * Real.pi / 2 ∨ x = 11 * Real.pi / 6 := by
              -- Prove that x must be one of the six values
              have h₉ : 0 < x := h₃
              have h₁₀ : x ≤ 2 * Real.pi := h₄
              have h₁₁ : 1 - 3 * Real.sin x + 5 * Real.cos (3 * x) = 0 := h₅
              have h₁₂ : x = Real.pi / 6 ∨ x = 5 * Real.pi / 6 ∨ x = Real.pi / 2 ∨ x = 7 * Real.pi / 6 ∨ x = 3 * Real.pi / 2 ∨ x = 11 * Real.pi / 6 := by
                -- Prove that x must be one of the six values
                have h₁₃ : x = Real.pi / 6 ∨ x = 5 * Real.pi / 6 ∨ x = Real.pi / 2 ∨ x = 7 * Real.pi / 6 ∨ x = 3 * Real.pi / 2 ∨ x = 11 * Real.pi / 6 := by
                  -- Prove that x must be one of the six values
                  apply or_iff_not_imp_left.mpr
                  intro h₁₄
                  apply or_iff_not_imp_left.mpr
                  intro h₁₅
                  apply or_iff_not_imp_left.mpr
                  intro h₁₆
                  apply or_iff_not_imp_left.mpr
                  intro h₁₇
                  apply or_iff_not_imp_left.mpr
                  intro h₁₈
                  -- Use the fact that the equation has six solutions in (0, 2π]
                  apply eq_of_sub_eq_zero
                  apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₄)
                  apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₅)
                  apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₆)
                  apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₇)
                  apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₈)
                  -- Use the fact that the equation has six solutions in (0, 2π]
                  nlinarith [Real.pi_pos, Real.pi_le_four, Real.sin_le_one x, Real.cos_le_one x, Real.sin_le_one (3 * x), Real.cos_le_one (3 * x),
                    Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq (3 * x), Real.sin_le_one (Real.pi / 6), Real.sin_le_one (5 * Real.pi / 6),
                    Real.sin_le_one (Real.pi / 2), Real.sin_le_one (7 * Real.pi / 6), Real.sin_le_one (3 * Real.pi / 2), Real.sin_le_one (11 * Real.pi / 6),
                    Real.cos_le_one (Real.pi / 6), Real.cos_le_one (5 * Real.pi / 6), Real.cos_le_one (Real.pi / 2), Real.cos_le_one (7 * Real.pi / 6),
                    Real.cos_le_one (3 * Real.pi / 2), Real.cos_le_one (11 * Real.pi / 6)]
                exact h₁₃
              exact h₁₂
            exact h₈
          exact h₇
        -- Prove that x must be one of the six values
        aesop
      · intro h
        have h₃ : x = Real.pi / 6 ∨ x = 5 * Real.pi / 6 ∨ x = Real.pi / 2 ∨ x = 7 * Real.pi / 6 ∨ x = 3 * Real.pi / 2 ∨ x = 11 * Real.pi / 6 := h
        have h₄ : 0 < x ∧ x ≤ 2 * Real.pi ∧ 1 - 3 * Real.sin x + 5 * Real.cos (3 * x) = 0 := by
          -- Prove that x must satisfy the conditions
          have h₅ : x = Real.pi / 6 ∨ x = 5 * Real.pi / 6 ∨ x = Real.pi / 2 ∨ x = 7 * Real.pi / 6 ∨ x = 3 * Real.pi / 2 ∨ x = 11 * Real.pi / 6 := h₃
          have h₆ : 0 < x := by
            -- Prove that 0 < x
            rcases h₅ with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
            (try norm_num) <;>
            (try linarith [Real.pi_pos, Real.pi_gt_three]) <;>
            (try ring_nf) <;>
            (try norm_num) <;>
            (try linarith [Real.pi_pos, Real.pi_gt_three])
          have h₇ : x ≤ 2 * Real.pi := by
            -- Prove that x ≤ 2 * Real.pi
            rcases h₅ with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
            (try norm_num) <;>
            (try linarith [Real.pi_pos, Real.pi_gt_three]) <;>
            (try ring_nf) <;>
            (try norm_num) <;>
            (try linarith [Real.pi_pos, Real.pi_gt_three])
          have h₈ : 1 - 3 * Real.sin x + 5 * Real.cos (3 * x) = 0 := by
            -- Prove that 1 - 3 * Real.sin x + 5 * Real.cos (3 * x) = 0
            rcases h₅ with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
            (try norm_num) <;>
            (try ring_nf) <;>
            (try field_simp [Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.sin_two_mul, Real.cos_two_mul, Real.sin_three_mul, Real.cos_three_mul]) <;>
            (try ring_nf at *) <;>
            (try norm_num at *) <;>
            (try linarith [Real.pi_pos, Real.pi_gt_three]) <;>
            (try nlinarith [Real.sin_le_one (Real.pi / 6), Real.sin_le_one (5 * Real.pi / 6), Real.sin_le_one (Real.pi / 2), Real.sin_le_one (7 * Real.pi / 6), Real.sin_le_one (3 * Real.pi / 2), Real.sin_le_one (11 * Real.pi / 6), Real.cos_le_one (Real.pi / 6), Real.cos_le_one (5 * Real.pi / 6), Real.cos_le_one (Real.pi / 2), Real.cos_le_one (7 * Real.pi / 6), Real.cos_le_one (3 * Real.pi / 2), Real.cos_le_one (11 * Real.pi / 6), Real.sin_le_one (3 * (Real.pi / 6)), Real.sin_le_one (3 * (5 * Real.pi / 6)), Real.sin_le_one (3 * (Real.pi / 2)), Real.sin_le_one (3 * (7 * Real.pi / 6)), Real.sin_le_one (3 * (3 * Real.pi / 2)), Real.sin_le_one (3 * (11 * Real.pi / 6)), Real.cos_le_one (3 * (Real.pi / 6)), Real.cos_le_one (3 * (5 * Real.pi / 6)), Real.cos_le_one (3 * (Real.pi / 2)), Real.cos_le_one (3 * (7 * Real.pi / 6)), Real.cos_le_one (3 * (3 * Real.pi / 2)), Real.cos_le_one (3 * (11 * Real.pi / 6))])
          exact ⟨h₆, h₇, h₈⟩
        exact h₄
    rw [h₂]
    norm_num [Finset.card_insert_of_not_mem, Finset.mem_singleton]
    <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try linarith [Real.pi_pos, Real.pi_gt_three]) <;>
    (try nlinarith [Real.sin_le_one (Real.pi / 6), Real.sin_le_one (5 * Real.pi / 6), Real.sin_le_one (Real.pi / 2), Real.sin_le_one (7 * Real.pi / 6), Real.sin_le_one (3 * Real.pi / 2), Real.sin_le_one (11 * Real.pi / 6), Real.cos_le_one (Real.pi / 6), Real.cos_le_one (5 * Real.pi / 6), Real.cos_le_one (Real.pi / 2), Real.cos_le_one (7 * Real.pi / 6), Real.cos_le_one (3 * Real.pi / 2), Real.cos_le_one (11 * Real.pi / 6), Real.sin_le_one (3 * (Real.pi / 6)), Real.sin_le_one (3 * (5 * Real.pi / 6)), Real.sin_le_one (3 * (Real.pi / 2)), Real.sin_le_one (3 * (7 * Real.pi / 6)), Real.sin_le_one (3 * (3 * Real.pi / 2)), Real.sin_le_one (3 * (11 * Real.pi / 6)), Real.cos_le_one (3 * (Real.pi / 6)), Real.cos_le_one (3 * (5 * Real.pi / 6)), Real.cos_le_one (3 * (Real.pi / 2)), Real.cos_le_one (3 * (7 * Real.pi / 6)), Real.cos_le_one (3 * (3 * Real.pi / 2)), Real.cos_le_one (3 * (11 * Real.pi / 6))])
  exact h₁
