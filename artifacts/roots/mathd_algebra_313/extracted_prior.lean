theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by
  have h_contradiction : False := by
    have h₃ : v = i * z := h₀
    have h₄ : v = 1 + Complex.I := h₁
    have h₅ : z = 2 - Complex.I := h₂
    have h₆ : i * z = 1 + Complex.I := by
      rw [h₃] at h₄
      exact h₄
    rw [h₅] at h₆
    have h₇ : i * (2 - Complex.I) = 1 + Complex.I := h₆
    have h₈ : i * (2 - Complex.I) = 2 * i - i * Complex.I := by
      ring_nf
      <;> simp [Complex.ext_iff, Complex.I_mul_I]
      <;> norm_num
      <;> ring_nf
      <;> simp [Complex.ext_iff, Complex.I_mul_I]
      <;> norm_num
      <;> ring_nf
      <;> simp [Complex.ext_iff, Complex.I_mul_I]
      <;> norm_num
    rw [h₈] at h₇
    have h₉ := h₇
    simp [Complex.ext_iff, Complex.I_mul_I] at h₇ h₉
    <;> norm_num at h₇ h₉ <;>
    (try ring_nf at h₇ h₉) <;>
    (try norm_num at h₇ h₉) <;>
    (try
      {
        simp_all [Complex.ext_iff, Complex.I_mul_I]
        <;> nlinarith
      }) <;>
    (try
      {
        nlinarith
      }) <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        simp_all [Complex.ext_iff, Complex.I_mul_I]
        <;> nlinarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        aesop
      })
  
  have h_main : i = 1 / 5 + 3 / 5 * Complex.I := by
    exfalso
    exact h_contradiction
  
  exact h_main
