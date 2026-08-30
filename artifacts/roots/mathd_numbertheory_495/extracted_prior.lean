theorem mathd_numbertheory_495 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a % 10 = 2) (h₂ : b % 10 = 4)
    (h₃ : Nat.gcd a b = 6) : 108 ≤ Nat.lcm a b := by
  have h₄ : 6 ∣ a := by
    have h₄₁ : 6 ∣ Nat.gcd a b := by
      rw [h₃]
      <;> norm_num
    have h₄₂ : 6 ∣ a := by
      have h₄₃ : 6 ∣ Nat.gcd a b := h₄₁
      have h₄₄ : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
      exact dvd_trans h₄₃ h₄₄
    exact h₄₂
  
  have h₅ : 6 ∣ b := by
    have h₅₁ : 6 ∣ Nat.gcd a b := by
      rw [h₃]
      <;> norm_num
    have h₅₂ : 6 ∣ b := by
      have h₅₃ : 6 ∣ Nat.gcd a b := h₅₁
      have h₅₄ : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
      exact dvd_trans h₅₃ h₅₄
    exact h₅₂
  
  have h₆ : a ≥ 12 := by
    by_contra h
    -- Assume for contradiction that a < 12
    have h₆₁ : a ≤ 11 := by linarith
    -- Since a > 0 and a < 12, a must be one of 1, 2, ..., 11
    have h₆₂ : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 := by
      omega
    -- Check each possible value of a to see if it satisfies the conditions
    rcases h₆₂ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    <;> norm_num at h₁ h₃ h₄ h₅ ⊢ <;>
      (try omega) <;>
      (try
        {
          have h₆₃ : b % 10 = 4 := h₂
          have h₆₄ : 6 ∣ b := h₅
          have h₆₅ : Nat.gcd 6 b = 6 := by simpa [h₃] using h₃
          have h₆₆ : b ≥ 6 := by
            by_contra h₆₆
            have h₆₇ : b ≤ 5 := by omega
            interval_cases b <;> norm_num at h₆₃ h₆₄ h₆₅ ⊢ <;> omega
          omega
        }) <;>
      (try
        {
          have h₆₃ : b % 10 = 4 := h₂
          have h₆₄ : 6 ∣ b := h₅
          have h₆₅ : Nat.gcd 2 b = 2 := by simpa [h₃] using h₃
          have h₆₆ : b ≥ 2 := by
            by_contra h₆₆
            have h₆₇ : b ≤ 1 := by omega
            interval_cases b <;> norm_num at h₆₃ h₆₄ h₆₅ ⊢ <;> omega
          omega
        }) <;>
      (try
        {
          have h₆₃ : b % 10 = 4 := h₂
          have h₆₄ : 6 ∣ b := h₅
          have h₆₅ : Nat.gcd 3 b = 3 := by simpa [h₃] using h₃
          have h₆₆ : b ≥ 3 := by
            by_contra h₆₆
            have h₆₇ : b ≤ 2 := by omega
            interval_cases b <;> norm_num at h₆₃ h₆₄ h₆₅ ⊢ <;> omega
          omega
        }) <;>
      (try
        {
          have h₆₃ : b % 10 = 4 := h₂
          have h₆₄ : 6 ∣ b := h₅
          have h₆₅ : Nat.gcd 4 b = 2 := by simpa [h₃] using h₃
          have h₆₆ : b ≥ 4 := by
            by_contra h₆₆
            have h₆₇ : b ≤ 3 := by omega
            interval_cases b <;> norm_num at h₆₃ h₆₄ h₆₅ ⊢ <;> omega
          omega
        }) <;>
      (try
        {
          have h₆₃ : b % 10 = 4 := h₂
          have h₆₄ : 6 ∣ b := h₅
          have h₆₅ : Nat.gcd 5 b = 1 := by simpa [h₃] using h₃
          have h₆₆ : b ≥ 5 := by
            by_contra h₆₆
            have h₆₇ : b ≤ 4 := by omega
            interval_cases b <;> norm_num at h₆₃ h₆₄ h₆₅ ⊢ <;> omega
          omega
        }) <;>
      (try
        {
          have h₆₃ : b % 10 = 4 := h₂
          have h₆₄ : 6 ∣ b := h₅
          have h₆₅ : Nat.gcd 6 b = 6 := by simpa [h₃] using h₃
          have h₆₆ : b ≥ 6 := by
            by_contra h₆₆
            have h₆₇ : b ≤ 5 := by omega
            interval_cases b <;> norm_num at h₆₃ h₆₄ h₆₅ ⊢ <;> omega
          omega
        }) <;>
      (try
        {
          have h₆₃ : b % 10 = 4 := h₂
          have h₆₄ : 6 ∣ b := h₅
          have h₆₅ : Nat.gcd 7 b = 1 := by simpa [h₃] using h₃
          have h₆₆ : b ≥ 7 := by
            by_contra h₆₆
            have h₆₇ : b ≤ 6 := by omega
            interval_cases b <;> norm_num at h₆₃ h₆₄ h₆₅ ⊢ <;> omega
          omega
        }) <;>
      (try
        {
          have h₆₃ : b % 10 = 4 := h₂
          have h₆₄ : 6 ∣ b := h₅
          have h₆₅ : Nat.gcd 8 b = 2 := by simpa [h₃] using h₃
          have h₆₆ : b ≥ 8 := by
            by_contra h₆₆
            have h₆₇ : b ≤ 7 := by omega
            interval_cases b <;> norm_num at h₆₃ h₆₄ h₆₅ ⊢ <;> omega
          omega
        }) <;>
      (try
        {
          have h₆₃ : b % 10 = 4 := h₂
          have h₆₄ : 6 ∣ b := h₅
          have h₆₅ : Nat.gcd 9 b = 3 := by simpa [h₃] using h₃
          have h₆₆ : b ≥ 9 := by
            by_contra h₆₆
            have h₆₇ : b ≤ 8 := by omega
            interval_cases b <;> norm_num at h₆₃ h₆₄ h₆₅ ⊢ <;> omega
          omega
        }) <;>
      (try
        {
          have h₆₃ : b % 10 = 4 := h₂
          have h₆₄ : 6 ∣ b := h₅
          have h₆₅ : Nat.gcd 10 b = 2 := by simpa [h₃] using h₃
          have h₆₆ : b ≥ 10 := by
            by_contra h₆₆
            have h₆₇ : b ≤ 9 := by omega
            interval_cases b <;> norm_num at h₆₃ h₆₄ h₆₅ ⊢ <;> omega
          omega
        })
    <;> omega
  
  have h₇ : b ≥ 24 := by
    by_contra h
    have h₇₁ : b ≤ 23 := by linarith
    have h₇₂ : 6 ∣ b := h₅
    have h₇₃ : b % 10 = 4 := h₂
    have h₇₄ : Nat.gcd a b = 6 := h₃
    have h₇₅ : 6 ∣ a := h₄
    have h₇₆ : a % 10 = 2 := h₁
    have h₇₇ : a ≥ 12 := h₆
    -- We will check all possible values of b from 6 to 23 that are multiples of 6 and satisfy b % 10 = 4
    have h₇₈ : b = 6 ∨ b = 12 ∨ b = 18 ∨ b = 24 := by
      interval_cases b <;> norm_num at h₇₂ h₇₃ ⊢ <;> omega
    rcases h₇₈ with (rfl | rfl | rfl | rfl) <;> norm_num at h₇₂ h₇₃ h₇₄ h₇₅ h₇₆ h₇₇ ⊢ <;>
      (try omega) <;>
      (try {
        have h₇₉ : a ≥ 12 := h₆
        have h₇₁₀ : a % 10 = 2 := h₁
        have h₇₁₁ : 6 ∣ a := h₄
        have h₇₁₂ : Nat.gcd a 6 = 6 := by simpa [h₃] using h₃
        have h₇₁₃ : a ≥ 6 := by
          by_contra h₇₁₃
          have h₇₁₄ : a ≤ 5 := by omega
          interval_cases a <;> norm_num at h₇₁₀ h₇₁₁ h₇₁₂ ⊢ <;> omega
        omega
      }) <;>
      (try {
        have h₇₉ : a ≥ 12 := h₆
        have h₇₁₀ : a % 10 = 2 := h₁
        have h₇₁₁ : 6 ∣ a := h₄
        have h₇₁₂ : Nat.gcd a 12 = 6 := by simpa [h₃] using h₃
        have h₇₁₃ : a ≥ 12 := by
          by_contra h₇₁₃
          have h₇₁₄ : a ≤ 11 := by omega
          interval_cases a <;> norm_num at h₇₁₀ h₇₁₁ h₇₁₂ ⊢ <;> omega
        omega
      }) <;>
      (try {
        have h₇₉ : a ≥ 12 := h₆
        have h₇₁₀ : a % 10 = 2 := h₁
        have h₇₁₁ : 6 ∣ a := h₄
        have h₇₁₂ : Nat.gcd a 18 = 6 := by simpa [h₃] using h₃
        have h₇₁₃ : a ≥ 18 := by
          by_contra h₇₁₃
          have h₇₁₄ : a ≤ 17 := by omega
          interval_cases a <;> norm_num at h₇₁₀ h₇₁₁ h₇₁₂ ⊢ <;> omega
        omega
      }) <;>
      (try {
        have h₇₉ : a ≥ 12 := h₆
        have h₇₁₀ : a % 10 = 2 := h₁
        have h₇₁₁ : 6 ∣ a := h₄
        have h₇₁₂ : Nat.gcd a 24 = 6 := by simpa [h₃] using h₃
        have h₇₁₃ : a ≥ 24 := by
          by_contra h₇₁₃
          have h₇₁₄ : a ≤ 23 := by omega
          interval_cases a <;> norm_num at h₇₁₀ h₇₁₁ h₇₁₂ ⊢ <;> omega
        omega
      })
    <;> omega
  
  have h₈ : a * b ≥ 648 := by
    have h₈₁ : a ≥ 12 := h₆
    have h₈₂ : b ≥ 24 := h₇
    have h₈₃ : a * b ≥ 12 * 24 := by
      nlinarith
    nlinarith
  
  have h₉ : Nat.lcm a b ≥ 108 := by
    have h₉₁ : Nat.lcm a b = a * b / Nat.gcd a b := by
      rw [Nat.lcm]
      <;> simp [Nat.gcd_mul_lcm]
      <;> ring
      <;> omega
    rw [h₉₁]
    have h₉₂ : Nat.gcd a b = 6 := h₃
    rw [h₉₂]
    have h₉₃ : a * b ≥ 648 := h₈
    have h₉₄ : a * b / 6 ≥ 108 := by
      omega
    omega
  
  linarith
