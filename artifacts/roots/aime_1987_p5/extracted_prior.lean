theorem aime_1987_p5 (x y : ℤ) (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    3 * (x ^ 2 * y ^ 2) = 588 := by
  have h_main : 3 * (x ^ 2 * y ^ 2) = 588 := by
    have h₁ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517 := h₀
    have h₂ : y ^ 2 * (1 + 3 * x ^ 2) = 30 * x ^ 2 + 517 := by
      ring_nf at h₁ ⊢
      <;> nlinarith
    have h₃ : x ≤ 10 := by
      nlinarith [sq_nonneg (x ^ 2 - 4), sq_nonneg (y ^ 2 - 49), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1)]
    have h₄ : x ≥ -10 := by
      nlinarith [sq_nonneg (x ^ 2 - 4), sq_nonneg (y ^ 2 - 49), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1)]
    interval_cases x <;> norm_num at h₂ ⊢ <;>
    (try omega) <;>
    (try {
      have h₅ : y ≤ 24 := by nlinarith
      have h₆ : y ≥ -24 := by nlinarith
      interval_cases y <;> norm_num at h₂ ⊢ <;> omega
    }) <;>
    (try {
      have h₅ : y ≤ 24 := by nlinarith
      have h₆ : y ≥ -24 := by nlinarith
      interval_cases y <;> norm_num at h₂ ⊢ <;> omega
    }) <;>
    (try {
      have h₅ : y ≤ 24 := by nlinarith
      have h₆ : y ≥ -24 := by nlinarith
      interval_cases y <;> norm_num at h₂ ⊢ <;> omega
    }) <;>
    (try {
      have h₅ : y ≤ 24 := by nlinarith
      have h₆ : y ≥ -24 := by nlinarith
      interval_cases y <;> norm_num at h₂ ⊢ <;> omega
    }) <;>
    (try {
      omega
    }) <;>
    (try {
      nlinarith
    })
    <;>
    (try {
      omega
    })
    <;>
    (try {
      nlinarith
    })
    <;>
    (try {
      omega
    })
    <;>
    (try {
      nlinarith
    })
    <;>
    (try {
      omega
    })
    <;>
    (try {
      nlinarith
    })
    <;>
    (try {
      omega
    })
    <;>
    (try {
      nlinarith
    })
    <;>
    (try {
      omega
    })
    <;>
    (try {
      nlinarith
    })
  exact h_main
