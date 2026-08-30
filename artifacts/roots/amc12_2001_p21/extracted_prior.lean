theorem amc12_2001_p21 (a b c d : ℕ) (h₀ : a * b * c * d = 8!) (h₁ : a * b + a + b = 524)
    (h₂ : b * c + b + c = 146) (h₃ : c * d + c + d = 104) : ↑a - ↑d = (10 : ℤ) := by
  have h_b_c : b = 20 ∧ c = 6 := by
    have h₄ : b ≥ 1 := by
      by_contra h
      have h₅ : b = 0 := by
        omega
      simp [h₅] at h₂ h₃
      <;> norm_num at h₂ h₃ <;> nlinarith
    have h₅ : c ≥ 1 := by
      by_contra h
      have h₆ : c = 0 := by
        omega
      simp [h₆] at h₂ h₃
      <;> norm_num at h₂ h₃ <;> nlinarith
    have h₆ : b ≤ 147 := by
      nlinarith
    have h₇ : c ≤ 147 := by
      nlinarith
    interval_cases b <;> norm_num at h₂ ⊢ <;>
      (try omega) <;>
      (try
        {
          have h₈ : c ≤ 147 := by nlinarith
          interval_cases c <;> norm_num at h₂ h₃ ⊢ <;>
            (try omega) <;>
            (try nlinarith) <;>
            (try
              {
                simp_all [Nat.factorial]
                <;> ring_nf at *
                <;> nlinarith
              })
        }) <;>
      (try omega) <;>
      (try nlinarith) <;>
      (try
        {
          simp_all [Nat.factorial]
          <;> ring_nf at *
          <;> nlinarith
        })
    <;>
    (try omega)
    <;>
    (try nlinarith)
    <;>
    (try
      {
        simp_all [Nat.factorial]
        <;> ring_nf at *
        <;> nlinarith
      })
    <;>
    (try omega)
  
  have h_a : a = 24 := by
    have h₄ : b = 20 ∧ c = 6 := h_b_c
    have h₅ : a * b + a + b = 524 := h₁
    have h₆ : a * b + a + b = 524 := by simpa using h₅
    have h₇ : b = 20 := h₄.1
    have h₈ : c = 6 := h₄.2
    subst_vars
    <;> ring_nf at *
    <;> nlinarith
  
  have h_d : d = 14 := by
    have h₄ : a * b * c * d = 8! := h₀
    have h₅ : a * b + a + b = 524 := h₁
    have h₆ : b * c + b + c = 146 := h₂
    have h₇ : c * d + c + d = 104 := h₃
    have h₈ : b = 20 := by
      have h₈₁ := h_b_c
      tauto
    have h₉ : c = 6 := by
      have h₉₁ := h_b_c
      tauto
    have h₁₀ : a = 24 := by
      have h₁₀₁ := h_a
      tauto
    subst_vars
    <;> norm_num [Nat.factorial] at h₄ ⊢ <;>
    (try omega) <;>
    (try ring_nf at h₄ ⊢ <;> omega) <;>
    (try nlinarith) <;>
    (try
      {
        ring_nf at h₄ ⊢
        omega
      })
    <;>
    omega
  
  have h_main : ↑a - ↑d = (10 : ℤ) := by
    have h₄ : a = 24 := h_a
    have h₅ : d = 14 := h_d
    subst_vars
    <;> norm_num
    <;> rfl
  
  exact h_main
