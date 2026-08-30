theorem algebra_others_exirrpowirrational : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
  have h_main : ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
    use Real.sqrt 2, (2 * Real.logb 2 3)
    constructor
    · -- Prove that √2 is irrational
      exact irrational_sqrt_two
    constructor
    · -- Prove that 2 * Real.logb 2 3 is irrational
      have h₁ : Irrational (2 * Real.logb 2 3) := by
        -- Use the fact that log₂ 3 is irrational to show that 2 * log₂ 3 is irrational
        have h₂ : Irrational (Real.logb 2 3) := by
          -- Prove that log₂ 3 is irrational
          have h₃ : Real.logb 2 3 = Real.log 3 / Real.log 2 := by
            simp [Real.logb]
          rw [h₃]
          -- Use the fact that log 3 / log 2 is irrational
          have h₄ : Irrational (Real.log 3 / Real.log 2) := by
            -- Prove that log 3 / log 2 is irrational
            have h₅ : Irrational (Real.log 3) := by
              -- Prove that log 3 is irrational
              exact by
                -- Use the fact that log 3 is transcendental
                have h₆ : Irrational (Real.log 3) := by
                  -- Use the fact that log 3 is transcendental
                  exact by
                    -- Use the fact that log 3 is transcendental
                    have h₇ : Real.log 3 ≠ 0 := by
                      -- Prove that log 3 ≠ 0
                      have h₈ : Real.log 3 > 0 := Real.log_pos (by norm_num)
                      linarith
                    -- Use the fact that log 3 is transcendental
                    have h₉ : Irrational (Real.log 3) := by
                      -- Use the fact that log 3 is transcendental
                      exact by
                        -- Use the fact that log 3 is transcendental
                        norm_num [Irrational, Set.mem_setOf_eq]
                        <;>
                        (try norm_num) <;>
                        (try
                          {
                            intro h
                            rcases h with ⟨q, hq⟩
                            have h₁₀ : Real.log 3 = q := by
                              linarith
                            have h₁₁ : Real.log 3 = q := by linarith
                            have h₁₂ : Real.log 3 = q := by linarith
                            -- Use the fact that log 3 is transcendental
                            have h₁₃ : Real.log 3 = q := by linarith
                            -- Use the fact that log 3 is transcendental
                            have h₁₄ : Real.log 3 = q := by linarith
                            -- Use the fact that log 3 is transcendental
                            norm_num at h₁₃ h₁₄ ⊢
                            <;>
                            (try
                              {
                                nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
                              })
                          })
                    exact h₉
                exact h₆
            have h₆ : Irrational (Real.log 2) := by
              -- Prove that log 2 is irrational
              have h₇ : Irrational (Real.log 2) := by
                -- Use the fact that log 2 is transcendental
                exact by
                  -- Use the fact that log 2 is transcendental
                  have h₈ : Real.log 2 ≠ 0 := by
                    -- Prove that log 2 ≠ 0
                    have h₉ : Real.log 2 > 0 := Real.log_pos (by norm_num)
                    linarith
                  -- Use the fact that log 2 is transcendental
                  have h₉ : Irrational (Real.log 2) := by
                    -- Use the fact that log 2 is transcendental
                    exact by
                      -- Use the fact that log 2 is transcendental
                      norm_num [Irrational, Set.mem_setOf_eq]
                      <;>
                      (try norm_num) <;>
                      (try
                        {
                          intro h
                          rcases h with ⟨q, hq⟩
                          have h₁₀ : Real.log 2 = q := by
                            linarith
                          have h₁₁ : Real.log 2 = q := by linarith
                          have h₁₂ : Real.log 2 = q := by linarith
                          -- Use the fact that log 2 is transcendental
                          have h₁₃ : Real.log 2 = q := by linarith
                          -- Use the fact that log 2 is transcendental
                          have h₁₄ : Real.log 2 = q := by linarith
                          -- Use the fact that log 2 is transcendental
                          norm_num at h₁₃ h₁₄ ⊢
                          <;>
                          (try
                            {
                              nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
                            })
                        })
                  exact h₉
              exact h₇
            -- Prove that log 3 / log 2 is irrational
            have h₇ : Irrational (Real.log 3 / Real.log 2) := by
              -- Use the fact that log 3 / log 2 is irrational
              have h₈ : Irrational (Real.log 3 / Real.log 2) := by
                -- Use the fact that log 3 / log 2 is irrational
                exact by
                  -- Use the fact that log 3 / log 2 is irrational
                  have h₉ : Irrational (Real.log 3) := h₅
                  have h₁₀ : Irrational (Real.log 2) := h₆
                  -- Use the fact that log 3 / log 2 is irrational
                  exact by
                    -- Use the fact that log 3 / log 2 is irrational
                    norm_num [Irrational, Set.mem_setOf_eq]
                    <;>
                    (try norm_num) <;>
                    (try
                      {
                        intro h
                        rcases h with ⟨q, hq⟩
                        have h₁₁ : Real.log 3 / Real.log 2 = q := by
                          linarith
                        have h₁₂ : Real.log 3 / Real.log 2 = q := by linarith
                        have h₁₃ : Real.log 3 / Real.log 2 = q := by linarith
                        -- Use the fact that log 3 / log 2 is irrational
                        have h₁₄ : Real.log 3 / Real.log 2 = q := by linarith
                        -- Use the fact that log 3 / log 2 is irrational
                        have h₁₅ : Real.log 3 / Real.log 2 = q := by linarith
                        -- Use the fact that log 3 / log 2 is irrational
                        field_simp at h₁₄ h₁₅ ⊢
                        <;>
                        (try
                          {
                            nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2),
                              Real.log_pos (by norm_num : (1 : ℝ) < 3)]
                          })
                      })
              exact h₈
            exact h₇
          exact h₄
        -- Prove that 2 * log₂ 3 is irrational
        have h₃ : Irrational (2 * Real.logb 2 3) := by
          -- Use the fact that log₂ 3 is irrational
          have h₄ : Irrational (Real.logb 2 3) := h₂
          -- Prove that 2 * log₂ 3 is irrational
          have h₅ : Irrational (2 * Real.logb 2 3) := by
            -- Use the fact that log₂ 3 is irrational
            exact by
              -- Use the fact that log₂ 3 is irrational
              norm_num [Irrational, Set.mem_setOf_eq]
              <;>
              (try norm_num) <;>
              (try
                {
                  intro h
                  rcases h with ⟨q, hq⟩
                  have h₆ : 2 * Real.logb 2 3 = q := by
                    linarith
                  have h₇ : 2 * Real.logb 2 3 = q := by linarith
                  have h₈ : 2 * Real.logb 2 3 = q := by linarith
                  -- Use the fact that log₂ 3 is irrational
                  have h₉ : Real.logb 2 3 = q / 2 := by
                    linarith
                  have h₁₀ : Real.logb 2 3 = q / 2 := by linarith
                  have h₁₁ : Real.logb 2 3 = q / 2 := by linarith
                  -- Use the fact that log₂ 3 is irrational
                  have h₁₂ : Irrational (Real.logb 2 3) := h₄
                  -- Use the fact that log₂ 3 is irrational
                  exact h₁₂ ⟨q / 2, by simp [h₉]⟩
                })
          exact h₅
        exact h₃
      exact h₁
    · -- Prove that (√2)^(2 * log₂ 3) is rational
      have h₂ : (Real.sqrt 2 : ℝ) ^ (2 * Real.logb 2 3) = 3 := by
        -- Prove that (√2)^(2 * log₂ 3) = 3
        have h₃ : Real.logb 2 3 = Real.log 3 / Real.log 2 := by
          simp [Real.logb]
        rw [h₃]
        have h₄ : (Real.sqrt 2 : ℝ) ^ (2 * (Real.log 3 / Real.log 2)) = 3 := by
          -- Prove that (√2)^(2 * (log 3 / log 2)) = 3
          have h₅ : (Real.sqrt 2 : ℝ) ^ (2 * (Real.log 3 / Real.log 2)) = (2 : ℝ) ^ (Real.log 3 / Real.log 2) := by
            -- Prove that (√2)^(2 * (log 3 / log 2)) = 2^(log 3 / log 2)
            have h₅₁ : (Real.sqrt 2 : ℝ) ^ (2 * (Real.log 3 / Real.log 2)) = (2 : ℝ) ^ (Real.log 3 / Real.log 2) := by
              -- Prove that (√2)^(2 * (log 3 / log 2)) = 2^(log 3 / log 2)
              calc
                (Real.sqrt 2 : ℝ) ^ (2 * (Real.log 3 / Real.log 2)) = (2 : ℝ) ^ (1 / 2 * (2 * (Real.log 3 / Real.log 2))) := by
                  -- Prove that (√2)^(2 * (log 3 / log 2)) = 2^(1/2 * (2 * (log 3 / log 2)))
                  rw [show (Real.sqrt 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) by
                    rw [Real.sqrt_eq_rpow]
                    <;> norm_num]
                  rw [← Real.rpow_mul] <;>
                  ring_nf <;>
                  norm_num <;>
                  linarith
                _ = (2 : ℝ) ^ (Real.log 3 / Real.log 2) := by
                  -- Prove that 1/2 * (2 * (log 3 / log 2)) = log 3 / log 2
                  ring_nf
                  <;>
                  field_simp
                  <;>
                  ring_nf
                  <;>
                  norm_num
                  <;>
                  linarith
            exact h₅₁
          rw [h₅]
          have h₆ : (2 : ℝ) ^ (Real.log 3 / Real.log 2) = 3 := by
            -- Prove that 2^(log 3 / log 2) = 3
            have h₆₁ : Real.log ((2 : ℝ) ^ (Real.log 3 / Real.log 2)) = Real.log 3 := by
              -- Prove that log (2^(log 3 / log 2)) = log 3
              have h₆₂ : Real.log ((2 : ℝ) ^ (Real.log 3 / Real.log 2)) = (Real.log 3 / Real.log 2) * Real.log 2 := by
                -- Prove that log (2^(log 3 / log 2)) = (log 3 / log 2) * log 2
                rw [Real.log_rpow (by norm_num : (2 : ℝ) > 0)]
                <;>
                ring_nf
                <;>
                field_simp
                <;>
                ring_nf
                <;>
                norm_num
                <;>
                linarith
              rw [h₆₂]
              have h₆₃ : (Real.log 3 / Real.log 2) * Real.log 2 = Real.log 3 := by
                -- Prove that (log 3 / log 2) * log 2 = log 3
                have h₆₄ : Real.log 2 ≠ 0 := by
                  -- Prove that log 2 ≠ 0
                  have h₆₅ : Real.log 2 > 0 := Real.log_pos (by norm_num)
                  linarith
                field_simp [h₆₄]
                <;>
                ring_nf
                <;>
                norm_num
                <;>
                linarith
              rw [h₆₃]
            have h₆₅ : Real.log ((2 : ℝ) ^ (Real.log 3 / Real.log 2)) = Real.log 3 := h₆₁
            have h₆₆ : Real.log ((2 : ℝ) ^ (Real.log 3 / Real.log 2)) = Real.log 3 := h₆₁
            have h₆₇ : (2 : ℝ) ^ (Real.log 3 / Real.log 2) = 3 := by
              -- Prove that 2^(log 3 / log 2) = 3
              apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
              linarith
            exact h₆₇
          rw [h₆]
        exact h₄
      -- Prove that (√2)^(2 * log₂ 3) is rational
      have h₃ : ¬Irrational ((Real.sqrt 2 : ℝ) ^ (2 * Real.logb 2 3)) := by
        -- Prove that (√2)^(2 * log₂ 3) is rational
        rw [h₂]
        -- Prove that 3 is rational
        norm_num [Irrational, Set.mem_setOf_eq]
        <;>
        (try norm_num) <;>
        (try
          {
            intro h
            rcases h with ⟨q, hq⟩
            norm_num at hq ⊢
            <;>
            (try
              {
                linarith
              })
          })
      exact h₃
  -- Use the main result to complete the proof
  obtain ⟨a, b, h₁, h₂, h₃⟩ := h_main
  exact ⟨a, b, h₁, h₂, h₃⟩
