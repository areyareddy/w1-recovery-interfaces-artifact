theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  have h_main : (∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k) → False := by
    intro h
    have h₁ : (∃ i j, (2 : ℤ) = 2 * i ∧ (0 : ℤ) = 2 * j) := by
      refine' ⟨1, 0, by norm_num, by norm_num⟩
    have h₂ : (∃ k : ℤ, (2 : ℤ) ^ 2 + (0 : ℤ) ^ 2 = 8 * k) ↔ False := by
      constructor
      · intro h₃
        rcases h₃ with ⟨k, h₃⟩
        have h₄ : (2 : ℤ) ^ 2 + (0 : ℤ) ^ 2 = 8 * k := h₃
        have h₅ : (4 : ℤ) = 8 * k := by norm_num at h₄ ⊢; linarith
        have h₆ : (k : ℤ) = 0 ∨ (k : ℤ) = 1 ∨ (k : ℤ) = -1 := by
          omega
        rcases h₆ with (h₆ | h₆ | h₆) <;> norm_num [h₆] at h₅ <;> omega
      · intro h₃
        exfalso
        exact h₃
    have h₃ := h (2 : ℤ) (0 : ℤ)
    have h₄ : (∃ i j, (2 : ℤ) = 2 * i ∧ (0 : ℤ) = 2 * j) ↔ ∃ k, (2 : ℤ) ^ 2 + (0 : ℤ) ^ 2 = 8 * k := by
      exact h₃
    have h₅ : (∃ i j, (2 : ℤ) = 2 * i ∧ (0 : ℤ) = 2 * j) := h₁
    have h₆ : (∃ k, (2 : ℤ) ^ 2 + (0 : ℤ) ^ 2 = 8 * k) := by
      tauto
    tauto
  
  intro h₁
  have h₂ : False := h_main h₁
  exact h₂
