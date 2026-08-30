theorem amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) : Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  have h₄ : Even (d 2021) := by
    rw [even_iff_two_dvd]
    -- We need to show that 2 divides d 2021.
    -- We will use the fact that the sequence d(n) modulo 2 is periodic with period 7.
    -- Specifically, we will show that d(n) ≡ 0 mod 2 when n ≡ 5 mod 7.
    -- Since 2021 ≡ 5 mod 7, we have d(2021) ≡ 0 mod 2.
    have h₄₁ : d 2021 % 2 = 0 := by
      -- Use the recurrence relation to compute d(n) modulo 2.
      -- We will use the fact that the sequence d(n) modulo 2 is periodic with period 7.
      -- Specifically, we will show that d(n) ≡ 0 mod 2 when n ≡ 5 mod 7.
      -- Since 2021 ≡ 5 mod 7, we have d(2021) ≡ 0 mod 2.
      norm_num [h₀, h₁, h₂, h₃, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
      <;> rfl
    -- Since d(2021) % 2 = 0, we have 2 divides d(2021).
    omega
  
  have h₅ : Odd (d 2022) := by
    rw [Nat.odd_iff_not_even]
    rw [even_iff_two_dvd]
    -- We need to show that 2 does not divide d 2022.
    -- We will use the fact that the sequence d(n) modulo 2 is periodic with period 7.
    -- Specifically, we will show that d(n) ≡ 1 mod 2 when n ≡ 6 mod 7.
    -- Since 2022 ≡ 6 mod 7, we have d(2022) ≡ 1 mod 2.
    have h₅₁ : d 2022 % 2 = 1 := by
      -- Use the recurrence relation to compute d(n) modulo 2.
      -- We will use the fact that the sequence d(n) modulo 2 is periodic with period 7.
      -- Specifically, we will show that d(n) ≡ 1 mod 2 when n ≡ 6 mod 7.
      -- Since 2022 ≡ 6 mod 7, we have d(2022) ≡ 1 mod 2.
      norm_num [h₀, h₁, h₂, h₃, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
      <;> rfl
    -- Since d(2022) % 2 = 1, we have 2 does not divide d(2022).
    omega
  
  have h₆ : Even (d 2023) := by
    rw [even_iff_two_dvd]
    -- We need to show that 2 divides d 2023.
    -- We will use the fact that the sequence d(n) modulo 2 is periodic with period 7.
    -- Specifically, we will show that d(n) ≡ 0 mod 2 when n ≡ 0 mod 7.
    -- Since 2023 ≡ 0 mod 7, we have d(2023) ≡ 0 mod 2.
    have h₆₁ : d 2023 % 2 = 0 := by
      -- Use the recurrence relation to compute d(n) modulo 2.
      -- We will use the fact that the sequence d(n) modulo 2 is periodic with period 7.
      -- Specifically, we will show that d(n) ≡ 0 mod 2 when n ≡ 0 mod 7.
      -- Since 2023 ≡ 0 mod 7, we have d(2023) ≡ 0 mod 2.
      norm_num [h₀, h₁, h₂, h₃, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
      <;> rfl
    -- Since d(2023) % 2 = 0, we have 2 divides d(2023).
    omega
  
  exact ⟨h₄, h₅, h₆⟩
