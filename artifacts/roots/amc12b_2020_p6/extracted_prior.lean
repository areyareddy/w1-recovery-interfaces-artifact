theorem amc12b_2020_p6 (n : ℕ) (h₀ : 9 ≤ n) : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! := by
  have h_main : ∃ (x : ℕ), (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! := by
    use n + 1
    have h₁ : ((n + 2)! - (n + 1)! : ℕ) = (n + 1)^2 * n ! := by
      have h₂ : (n + 2)! = (n + 2) * (n + 1) * n ! := by
        simp [Nat.factorial_succ, Nat.mul_assoc]
        <;> ring_nf
        <;> simp [Nat.factorial]
        <;> ring_nf
      have h₃ : (n + 1)! = (n + 1) * n ! := by
        simp [Nat.factorial_succ, Nat.mul_assoc]
        <;> ring_nf
        <;> simp [Nat.factorial]
        <;> ring_nf
      rw [h₂, h₃]
      <;> cases n with
      | zero => contradiction -- n ≥ 9, so n cannot be zero
      | succ n =>
        simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.pow_succ, Nat.mul_add, Nat.add_mul]
        <;> ring_nf at *
        <;> omega
    have h₂ : (((n + 2)! - (n + 1)! : ℕ) : ℝ) = ((n + 1)^2 * n ! : ℝ) := by
      norm_cast
      <;> simp [h₁]
      <;> ring_nf
    have h₃ : (((n + 2)! - (n + 1)! : ℕ) : ℝ) / n ! = ((n + 1)^2 : ℝ) := by
      have h₄ : (n ! : ℝ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      field_simp [h₄] at h₂ ⊢
      <;> nlinarith
    have h₄ : ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) ^ 2 : ℝ) := by
      norm_cast
    simp_all [h₄]
    <;> ring_nf at *
    <;> field_simp at *
    <;> nlinarith
  
  exact h_main
