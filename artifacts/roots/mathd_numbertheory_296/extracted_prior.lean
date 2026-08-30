theorem mathd_numbertheory_296 (n : ℕ) (h₀ : 2 ≤ n) (h₁ : ∃ x, x ^ 3 = n) (h₂ : ∃ t, t ^ 4 = n) :
    4096 ≤ n := by
  have h_main : 4096 ≤ n := by
    rcases h₁ with ⟨x, hx⟩
    rcases h₂ with ⟨t, ht⟩
    have h₃ : x ^ 3 = n := hx
    have h₄ : t ^ 4 = n := ht
    have h₅ : x ^ 3 = t ^ 4 := by linarith
    have h₆ : x ≥ 2 := by
      by_contra h
      have h₇ : x ≤ 1 := by linarith
      have h₈ : x = 0 ∨ x = 1 := by
        omega
      rcases h₈ with (h₈ | h₈) <;> simp [h₈, pow_succ, pow_zero, mul_assoc] at h₅ <;>
        (try omega) <;>
        (try {
          have h₉ : t ≤ 1 := by
            nlinarith [sq_nonneg (t ^ 2), sq_nonneg (t ^ 2 - 1), sq_nonneg (t - 1)]
          have h₁₀ : t = 0 ∨ t = 1 := by omega
          rcases h₁₀ with (h₁₀ | h₁₀) <;> simp [h₁₀, pow_succ, pow_zero, mul_assoc] at h₅ <;>
            (try omega) <;>
            (try nlinarith)
        }) <;>
        nlinarith
    have h₇ : t ≥ 2 := by
      by_contra h
      have h₈ : t ≤ 1 := by linarith
      have h₉ : t = 0 ∨ t = 1 := by omega
      rcases h₉ with (h₉ | h₉) <;> simp [h₉, pow_succ, pow_zero, mul_assoc] at h₅ <;>
        (try omega) <;>
        (try {
          have h₁₀ : x ≤ 1 := by
            nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1)]
          have h₁₁ : x = 0 ∨ x = 1 := by omega
          rcases h₁₁ with (h₁₁ | h₁₁) <;> simp [h₁₁, pow_succ, pow_zero, mul_assoc] at h₅ <;>
            (try omega) <;>
            (try nlinarith)
        }) <;>
        nlinarith
    have h₈ : x ^ 3 ≥ 2 ^ 3 := by
      have h₉ : x ≥ 2 := h₆
      have h₁₀ : x ^ 3 ≥ 2 ^ 3 := by
        exact Nat.pow_le_pow_of_le_left h₉ 3
      exact h₁₀
    have h₉ : t ^ 4 ≥ 2 ^ 4 := by
      have h₁₀ : t ≥ 2 := h₇
      have h₁₁ : t ^ 4 ≥ 2 ^ 4 := by
        exact Nat.pow_le_pow_of_le_left h₁₀ 4
      exact h₁₁
    have h₁₀ : x ^ 3 = t ^ 4 := by linarith
    have h₁₁ : x ≥ 2 := h₆
    have h₁₂ : t ≥ 2 := h₇
    have h₁₃ : x ^ 3 ≥ 2 ^ 3 := by
      exact h₈
    have h₁₄ : t ^ 4 ≥ 2 ^ 4 := by
      exact h₉
    have h₁₅ : x ≤ 16 := by
      by_contra! h
      have h₁₆ : x ≥ 17 := by linarith
      have h₁₇ : x ^ 3 ≥ 17 ^ 3 := by
        exact Nat.pow_le_pow_of_le_left h₁₆ 3
      have h₁₈ : t ^ 4 ≥ 17 ^ 4 := by
        have h₁₉ : t ≥ 17 := by
          by_contra! h₂₀
          have h₂₁ : t ≤ 16 := by linarith
          interval_cases t <;> norm_num at h₁₀ ⊢ <;>
            (try omega) <;>
            (try {
              have h₂₂ : x ≤ 256 := by
                nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1)]
              interval_cases x <;> norm_num at h₁₀ ⊢ <;>
                (try omega) <;>
                (try nlinarith)
            }) <;>
            (try omega)
        exact Nat.pow_le_pow_of_le_left h₁₉ 4
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (t ^ 2), sq_nonneg (x - t)]
    have h₁₆ : t ≤ 16 := by
      by_contra! h
      have h₁₇ : t ≥ 17 := by linarith
      have h₁₈ : t ^ 4 ≥ 17 ^ 4 := by
        exact Nat.pow_le_pow_of_le_left h₁₇ 4
      have h₁₉ : x ^ 3 ≥ 17 ^ 3 := by
        have h₂₀ : x ≥ 17 := by
          by_contra! h₂₁
          have h₂₂ : x ≤ 16 := by linarith
          interval_cases x <;> norm_num at h₁₀ ⊢ <;>
            (try omega) <;>
            (try {
              have h₂₃ : t ≤ 256 := by
                nlinarith [sq_nonneg (t ^ 2), sq_nonneg (t ^ 2 - 1), sq_nonneg (t - 1)]
              interval_cases t <;> norm_num at h₁₀ ⊢ <;>
                (try omega) <;>
                (try nlinarith)
            }) <;>
            (try omega)
        exact Nat.pow_le_pow_of_le_left h₂₀ 3
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (t ^ 2), sq_nonneg (x - t)]
    interval_cases x <;> interval_cases t <;> norm_num at h₁₀ ⊢ <;>
      (try omega) <;>
      (try {
        omega
      }) <;>
      (try {
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (t ^ 2), sq_nonneg (x - t)]
      })
    <;>
    (try {
      nlinarith
    })
    <;>
    (try {
      ring_nf at *
      <;>
      nlinarith
    })
  exact h_main
