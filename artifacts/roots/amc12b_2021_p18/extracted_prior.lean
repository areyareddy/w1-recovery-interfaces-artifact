theorem amc12b_2021_p18 (z : ℂ)
    (h₀ : 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z ^ 2 + 1) + 31) :
    z + 6 / z = -2 := by
  have h_main : z + 6 / z = -2 := by
    have h₁ := h₀
    simp [Complex.normSq, Complex.ext_iff, pow_two, pow_three, Complex.ext_iff, mul_add, add_mul,
      mul_comm, mul_left_comm] at h₁ ⊢
    ring_nf at h₁ ⊢
    <;>
    (try norm_num at h₁ ⊢) <;>
    (try
      {
        nlinarith [sq_nonneg (z.re - 1), sq_nonneg (z.im), sq_nonneg (z.re + 1), sq_nonneg (z.im - 1),
          sq_nonneg (z.re - 2), sq_nonneg (z.im - 2), sq_nonneg (z.re + 2), sq_nonneg (z.im + 2)]
      }) <;>
    (try
      {
        field_simp [Complex.ext_iff, pow_two, pow_three, Complex.ext_iff, mul_add, add_mul,
          mul_comm, mul_left_comm] at h₁ ⊢
        <;>
        ring_nf at h₁ ⊢ <;>
        norm_num at h₁ ⊢ <;>
        nlinarith [sq_nonneg (z.re - 1), sq_nonneg (z.im), sq_nonneg (z.re + 1), sq_nonneg (z.im - 1),
          sq_nonneg (z.re - 2), sq_nonneg (z.im - 2), sq_nonneg (z.re + 2), sq_nonneg (z.im + 2)]
      }) <;>
    (try
      {
        simp_all [Complex.ext_iff, pow_two, pow_three, Complex.ext_iff, mul_add, add_mul,
          mul_comm, mul_left_comm]
        <;>
        ring_nf at *
        <;>
        norm_num at *
        <;>
        nlinarith [sq_nonneg (z.re - 1), sq_nonneg (z.im), sq_nonneg (z.re + 1), sq_nonneg (z.im - 1),
          sq_nonneg (z.re - 2), sq_nonneg (z.im - 2), sq_nonneg (z.re + 2), sq_nonneg (z.im + 2)]
      }) <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        nlinarith [sq_nonneg (z.re - 1), sq_nonneg (z.im), sq_nonneg (z.re + 1), sq_nonneg (z.im - 1),
          sq_nonneg (z.re - 2), sq_nonneg (z.im - 2), sq_nonneg (z.re + 2), sq_nonneg (z.im + 2)]
      })
    <;>
    (try
      {
        simp_all [Complex.ext_iff, pow_two, pow_three, Complex.ext_iff, mul_add, add_mul,
          mul_comm, mul_left_comm]
        <;>
        ring_nf at *
        <;>
        norm_num at *
        <;>
        nlinarith [sq_nonneg (z.re - 1), sq_nonneg (z.im), sq_nonneg (z.re + 1), sq_nonneg (z.im - 1),
          sq_nonneg (z.re - 2), sq_nonneg (z.im - 2), sq_nonneg (z.re + 2), sq_nonneg (z.im + 2)]
      })
  exact h_main
