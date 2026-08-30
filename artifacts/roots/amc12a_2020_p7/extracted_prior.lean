theorem amc12a_2020_p7 (a : ℕ → ℕ) (h₀ : a 0 ^ 3 = 1) (h₁ : a 1 ^ 3 = 8) (h₂ : a 2 ^ 3 = 27)
    (h₃ : a 3 ^ 3 = 64) (h₄ : a 4 ^ 3 = 125) (h₅ : a 5 ^ 3 = 216) (h₆ : a 6 ^ 3 = 343) :
    ↑(∑ k in Finset.range 7, 6 * (a (k ^ 2))) - ↑(2 * ∑ k in Finset.range 6, (a (k ^ 2))) = (658 : ℤ) := by
  have h₇ : a 0 = 1 := by
    have h₇₁ : a 0 ^ 3 = 1 := h₀
    have h₇₂ : a 0 = 1 := by
      have h₇₃ : a 0 ≤ 1 := by
        nlinarith [pow_two_nonneg (a 0), pow_two_nonneg (a 0 - 1)]
      interval_cases a 0 <;> norm_num at h₇₁ ⊢ <;> nlinarith
    exact h₇₂
  
  have h₈ : a 1 = 2 := by
    have h₈₁ : a 1 ^ 3 = 8 := h₁
    have h₈₂ : a 1 = 2 := by
      have h₈₃ : a 1 ≤ 2 := by
        nlinarith [pow_two_nonneg (a 1), pow_two_nonneg (a 1 - 1)]
      interval_cases a 1 <;> norm_num at h₈₁ ⊢ <;> nlinarith
    exact h₈₂
  
  have h₉ : a 4 = 5 := by
    have h₉₁ : a 4 ^ 3 = 125 := h₄
    have h₉₂ : a 4 = 5 := by
      have h₉₃ : a 4 ≤ 5 := by
        nlinarith [pow_two_nonneg (a 4), pow_two_nonneg (a 4 - 1)]
      interval_cases a 4 <;> norm_num at h₉₁ ⊢ <;> nlinarith
    exact h₉₂
  
  have h₁₀ : a 9 = 9 := by
    have h₁₀₁ : a 9 ^ 3 = 729 := by
      have h₁₀₂ : a 9 ^ 3 = 729 := by
        -- Use the given value of a(9) to compute a(9)^3
        norm_num [h₇, h₈, h₉] at *
        <;>
        (try omega) <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 9), pow_two_nonneg (a 9 - 1)]
          }) <;>
        (try
          {
            ring_nf at *
            <;> nlinarith
          })
        <;>
        (try
          {
            aesop
          })
        <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 9), pow_two_nonneg (a 9 - 1)]
          })
        <;>
        (try
          {
            omega
          })
        <;>
        (try
          {
            aesop
          })
        <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 9), pow_two_nonneg (a 9 - 1)]
          })
        <;>
        (try
          {
            omega
          })
        <;>
        (try
          {
            aesop
          })
      exact h₁₀₂
    have h₁₀₃ : a 9 = 9 := by
      have h₁₀₄ : a 9 ≤ 9 := by
        nlinarith [pow_two_nonneg (a 9), pow_two_nonneg (a 9 - 1)]
      interval_cases a 9 <;> norm_num at h₁₀₁ ⊢ <;> nlinarith
    exact h₁₀₃
  
  have h₁₁ : a 16 = 16 := by
    have h₁₁₁ : a 16 ^ 3 = 4096 := by
      have h₁₁₂ : a 16 ^ 3 = 4096 := by
        -- Use the given value of a(16) to compute a(16)^3
        norm_num [h₇, h₈, h₉, h₁₀] at *
        <;>
        (try omega) <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 16), pow_two_nonneg (a 16 - 1)]
          }) <;>
        (try
          {
            ring_nf at *
            <;> nlinarith
          })
        <;>
        (try
          {
            aesop
          })
        <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 16), pow_two_nonneg (a 16 - 1)]
          })
        <;>
        (try
          {
            omega
          })
        <;>
        (try
          {
            aesop
          })
        <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 16), pow_two_nonneg (a 16 - 1)]
          })
        <;>
        (try
          {
            omega
          })
        <;>
        (try
          {
            aesop
          })
      exact h₁₁₂
    have h₁₁₂ : a 16 = 16 := by
      have h₁₁₃ : a 16 ≤ 16 := by
        nlinarith [pow_two_nonneg (a 16), pow_two_nonneg (a 16 - 1)]
      interval_cases a 16 <;> norm_num at h₁₁₁ ⊢ <;> nlinarith
    exact h₁₁₂
  
  have h₁₂ : a 25 = 25 := by
    have h₁₂₁ : a 25 ^ 3 = 15625 := by
      have h₁₂₂ : a 25 ^ 3 = 15625 := by
        -- Use the given value of a(25) to compute a(25)^3
        norm_num [h₇, h₈, h₉, h₁₀, h₁₁] at *
        <;>
        (try omega) <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 25), pow_two_nonneg (a 25 - 1)]
          }) <;>
        (try
          {
            ring_nf at *
            <;> nlinarith
          })
        <;>
        (try
          {
            aesop
          })
        <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 25), pow_two_nonneg (a 25 - 1)]
          })
        <;>
        (try
          {
            omega
          })
        <;>
        (try
          {
            aesop
          })
        <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 25), pow_two_nonneg (a 25 - 1)]
          })
        <;>
        (try
          {
            omega
          })
        <;>
        (try
          {
            aesop
          })
      exact h₁₂₂
    have h₁₂₂ : a 25 = 25 := by
      have h₁₂₃ : a 25 ≤ 25 := by
        nlinarith [pow_two_nonneg (a 25), pow_two_nonneg (a 25 - 1)]
      interval_cases a 25 <;> norm_num at h₁₂₁ ⊢ <;> nlinarith
    exact h₁₂₂
  
  have h₁₃ : a 36 = 36 := by
    have h₁₃₁ : a 36 ^ 3 = 46656 := by
      have h₁₃₂ : a 36 ^ 3 = 46656 := by
        -- Use the given value of a(36) to compute a(36)^3
        norm_num [h₇, h₈, h₉, h₁₀, h₁₁, h₁₂] at *
        <;>
        (try omega) <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 36), pow_two_nonneg (a 36 - 1)]
          }) <;>
        (try
          {
            ring_nf at *
            <;> nlinarith
          })
        <;>
        (try
          {
            aesop
          })
        <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 36), pow_two_nonneg (a 36 - 1)]
          })
        <;>
        (try
          {
            omega
          })
        <;>
        (try
          {
            aesop
          })
        <;>
        (try
          {
            nlinarith [pow_two_nonneg (a 36), pow_two_nonneg (a 36 - 1)]
          })
        <;>
        (try
          {
            omega
          })
        <;>
        (try
          {
            aesop
          })
      exact h₁₃₂
    have h₁₃₂ : a 36 = 36 := by
      have h₁₃₃ : a 36 ≤ 36 := by
        nlinarith [pow_two_nonneg (a 36), pow_two_nonneg (a 36 - 1)]
      interval_cases a 36 <;> norm_num at h₁₃₁ ⊢ <;> nlinarith
    exact h₁₃₂
  
  have h₁₄ : ↑(∑ k in Finset.range 7, 6 * (a (k ^ 2))) - ↑(2 * ∑ k in Finset.range 6, (a (k ^ 2))) = (658 : ℤ) := by
    simp [Finset.sum_range_succ, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃]
    <;> norm_num
    <;> rfl
  
  exact h₁₄
