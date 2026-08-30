theorem mathd_numbertheory_135 (n A B C : ℕ) (h₀ : n = 3 ^ 17 + 3 ^ 10) (h₁ : 11 ∣ n + 1)
    (h₂ : [A, B, C].Pairwise (· ≠ ·)) (h₃ : {A, B, C} ⊂ Finset.Icc 0 9) (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬3 ∣ B) (h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]) :
    100 * A + 10 * B + C = 129 := by
  have h_contradiction : False := by
    have h₇ : n = 129157512 := by
      rw [h₀]
      <;> norm_num
      <;> rfl
    have h₈ : Nat.digits 10 n = [1, 2, 9, 1, 5, 7, 5, 1, 2] := by
      rw [h₇]
      <;> norm_num [Nat.digits_zero, Nat.div_eq_of_lt]
      <;> rfl
    rw [h₈] at h₆
    have h₉ := h₆
    simp [List.cons, List.nil] at h₉
    <;>
    (try contradiction) <;>
    (try omega) <;>
    (try
      {
        have h₁₀ := h₂
        simp [List.Pairwise, List.cons, List.nil] at h₁₀
        <;>
        (try omega) <;>
        (try contradiction) <;>
        (try aesop)
      }) <;>
    (try
      {
        have h₁₁ := h₃
        simp [Finset.subset_iff, Finset.mem_insert, Finset.mem_singleton] at h₁₁
        <;>
        (try omega) <;>
        (try aesop)
      }) <;>
    (try
      {
        have h₁₂ := h₄
        simp [Nat.odd_iff_not_even, Nat.even_iff] at h₁₂
        <;>
        (try omega) <;>
        (try aesop)
      }) <;>
    (try
      {
        aesop
      })
    <;>
    omega
  
  have h_main : 100 * A + 10 * B + C = 129 := by
    exfalso
    exact h_contradiction
  
  exact h_main
