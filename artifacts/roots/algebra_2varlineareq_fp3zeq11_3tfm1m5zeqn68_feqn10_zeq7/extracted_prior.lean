theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 (f z : ℂ) (h₀ : f + 3 * z = 11)
    (h₁ : 3 * (f - 1) - 5 * z = -68) : f = -10 ∧ z = 7 := by
  have h₂ : f = 11 - 3 * z := by
    have h₂₁ : f = 11 - 3 * z := by
      have h₂₂ : f + 3 * z = 11 := h₀
      have h₂₃ : f = 11 - 3 * z := by
        rw [← sub_eq_zero]
        ring_nf at h₂₂ ⊢
        rw [h₂₂]
        <;> ring_nf <;> simp [Complex.ext_iff, pow_two, pow_three]
        <;> norm_num
        <;>
        (try ring_nf at * <;> simp_all [Complex.ext_iff, pow_two, pow_three] <;> norm_num <;>
          constructor <;> linarith) <;>
        (try ring_nf at * <;> simp_all [Complex.ext_iff, pow_two, pow_three] <;> norm_num <;>
          constructor <;> linarith)
      exact h₂₃
    exact h₂₁
  
  have h₃ : 3 * f - 5 * z = -65 := by
    have h₃₁ : 3 * (f - 1) - 5 * z = -68 := h₁
    have h₃₂ : 3 * f - 5 * z = -65 := by
      calc
        3 * f - 5 * z = 3 * f - 5 * z := rfl
        _ = 3 * (f - 1) - 5 * z + 3 := by ring
        _ = (-68 : ℂ) + 3 := by rw [h₃₁]
        _ = -65 := by norm_num
    exact h₃₂
  
  have h₄ : z = 7 := by
    rw [h₂] at h₃
    have h₄₁ : (3 : ℂ) * (11 - 3 * z) - 5 * z = -65 := by
      simpa using h₃
    have h₄₂ : (3 : ℂ) * (11 - 3 * z) - 5 * z = 33 - 14 * z := by
      ring_nf
      <;> simp [Complex.ext_iff, pow_two, pow_three]
      <;> norm_num
      <;>
      (try ring_nf at * <;> simp_all [Complex.ext_iff, pow_two, pow_three] <;> norm_num <;>
        constructor <;> linarith) <;>
      (try ring_nf at * <;> simp_all [Complex.ext_iff, pow_two, pow_three] <;> norm_num <;>
        constructor <;> linarith)
    have h₄₃ : (33 : ℂ) - 14 * z = -65 := by
      rw [h₄₂] at h₄₁
      exact h₄₁
    have h₄₄ : (z : ℂ) = 7 := by
      have h₄₄₁ : (z : ℂ) = 7 := by
        have h₄₄₂ : (33 : ℂ) - 14 * z = -65 := h₄₃
        have h₄₄₃ : (14 : ℂ) * z = 98 := by
          ring_nf at h₄₄₂ ⊢
          rw [← sub_eq_zero]
          ring_nf at h₄₄₂ ⊢
          rw [h₄₄₂]
          <;> ring_nf <;> simp [Complex.ext_iff, pow_two, pow_three]
          <;> norm_num
          <;>
          (try ring_nf at * <;> simp_all [Complex.ext_iff, pow_two, pow_three] <;> norm_num <;>
            constructor <;> linarith) <;>
          (try ring_nf at * <;> simp_all [Complex.ext_iff, pow_two, pow_three] <;> norm_num <;>
            constructor <;> linarith)
        have h₄₄₄ : (z : ℂ) = 7 := by
          have h₄₄₅ : (14 : ℂ) * z = 98 := h₄₄₃
          have h₄₄₆ : (z : ℂ) = 7 := by
            calc
              (z : ℂ) = (14 : ℂ) * z / 14 := by field_simp <;> ring_nf <;> simp [Complex.ext_iff, pow_two, pow_three] <;> norm_num
              _ = 98 / 14 := by rw [h₄₄₅]
              _ = 7 := by norm_num
              _ = 7 := by rfl
          exact h₄₄₆
        exact h₄₄₄
      exact h₄₄₁
    exact h₄₄
  
  have h₅ : f = -10 := by
    rw [h₂, h₄]
    <;> norm_num <;>
    (try ring_nf at * <;> simp_all [Complex.ext_iff, pow_two, pow_three] <;> norm_num <;>
      constructor <;> linarith) <;>
    (try ring_nf at * <;> simp_all [Complex.ext_iff, pow_two, pow_three] <;> norm_num <;>
      constructor <;> linarith)
    <;>
    simp_all [Complex.ext_iff, pow_two, pow_three]
    <;>
    norm_num
    <;>
    linarith
  
  have h₆ : f = -10 ∧ z = 7 := by
    exact ⟨h₅, h₄⟩
  
  exact h₆
