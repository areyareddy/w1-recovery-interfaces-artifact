theorem amc12a_2003_p5 (A M C : ℕ) (h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
    (h₁ : Nat.ofDigits 10 [0, 1, C, M, A] + Nat.ofDigits 10 [2, 1, C, M, A] = 123422) :
    A + M + C = 14 := by
  have h₂ : False := by
    have h₃ := h₁
    simp [Nat.ofDigits, List.sum_cons, List.sum_nil, List.map, List.range_succ, Nat.mul_add, Nat.add_mul] at h₃
    <;> ring_nf at h₃ ⊢
    <;> norm_num at h₃ ⊢
    <;>
    (try omega) <;>
    (try
      {
        have h₄ : A ≤ 9 := h₀.1
        have h₅ : M ≤ 9 := h₀.2.1
        have h₆ : C ≤ 9 := h₀.2.2
        interval_cases A <;> interval_cases M <;> interval_cases C <;> norm_num at h₃ ⊢ <;> omega
      }) <;>
    omega
  
  have h₃ : A + M + C = 14 := by
    exfalso
    exact h₂
  
  exact h₃
