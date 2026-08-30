theorem mathd_algebra_184 (a b : NNReal) (h₀ : 0 < a ∧ 0 < b) (h₁ : a ^ 2 = 6 * b)
    (h₂ : a ^ 2 = 54 / b) : a = 3 * NNReal.sqrt 2 := by
  have h_b_pos : 0 < b := by
    exact h₀.2
  
  have h_b_val : b = 3 := by
    have h₃ : (a ^ 2 : NNReal) = 6 * b := by simpa using h₁
    have h₄ : (a ^ 2 : NNReal) = 54 / b := by simpa using h₂
    have h₅ : (6 * b : NNReal) = 54 / b := by
      calc
        (6 * b : NNReal) = a ^ 2 := by
          rw [h₃]
          <;> simp [mul_comm]
        _ = 54 / b := by rw [h₄]
    have h₆ : (b : ℝ) > 0 := by exact_mod_cast h_b_pos
    have h₇ : (6 * b : ℝ) = 54 / b := by
      exact_mod_cast h₅
    have h₈ : (b : ℝ) ^ 2 = 9 := by
      field_simp at h₇
      nlinarith
    have h₉ : (b : ℝ) = 3 := by
      nlinarith
    have h₁₀ : b = 3 := by
      exact_mod_cast h₉
    exact h₁₀
  
  have h_a_sq : a ^ 2 = 18 := by
    have h₃ : a ^ 2 = 6 * b := h₁
    rw [h_b_val] at h₃
    norm_num at h₃ ⊢
    <;>
    (try simp_all [mul_comm]) <;>
    (try ring_nf at * <;> simp_all [mul_comm]) <;>
    (try field_simp at * <;> ring_nf at * <;> nlinarith) <;>
    (try norm_cast at * <;> nlinarith)
    <;>
    simp_all [mul_comm]
    <;>
    ring_nf at * <;>
    nlinarith
  
  have h_a_val : a = 3 * NNReal.sqrt 2 := by
    have h₃ : a ^ 2 = 18 := h_a_sq
    have h₄ : a = 3 * NNReal.sqrt 2 := by
      have h₅ : (a : ℝ) ^ 2 = 18 := by
        norm_cast at h₃ ⊢
        <;> simp_all [sq]
        <;> ring_nf at * <;> nlinarith
      have h₆ : (a : ℝ) = 3 * Real.sqrt 2 := by
        have h₇ : 0 ≤ (a : ℝ) := by exact_mod_cast (by positivity)
        have h₈ : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h₉ : 0 ≤ (a : ℝ) * Real.sqrt 2 := by positivity
        -- Use the fact that the square of a is 18 to find the value of a
        have h₁₀ : (a : ℝ) ^ 2 = 18 := by exact_mod_cast h₅
        have h₁₁ : (a : ℝ) = 3 * Real.sqrt 2 := by
          -- Use the quadratic equation to find a
          have h₁₂ : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
          have h₁₃ : (a : ℝ) = 3 * Real.sqrt 2 := by
            -- Use the quadratic equation to find a
            nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num), Real.sqrt_nonneg 2,
              sq_nonneg ((a : ℝ) - 3 * Real.sqrt 2)]
          exact h₁₃
        exact h₁₁
      have h₇ : a = 3 * NNReal.sqrt 2 := by
        -- Convert the result back to NNReal
        have h₈ : (a : ℝ) = 3 * Real.sqrt 2 := by exact_mod_cast h₆
        have h₉ : a = 3 * NNReal.sqrt 2 := by
          apply Eq.symm
          apply Eq.symm
          rw [← NNReal.coe_inj] at *
          simp_all [NNReal.coe_mul, NNReal.coe_sqrt, NNReal.coe_ofNat]
          <;>
          ring_nf at * <;>
          norm_num at * <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
        exact h₉
      exact h₇
    exact h₄
  
  rw [h_a_val]
  <;>
  simp_all
  <;>
  norm_num
  <;>
  ring_nf
  <;>
  norm_num
  <;>
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
