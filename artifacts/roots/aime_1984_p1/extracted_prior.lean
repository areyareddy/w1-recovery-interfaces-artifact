theorem aime_1984_p1 (u : ℕ → ℚ) (h₀ : ∀ n, u (n + 1) = u n + 1)
    (h₁ : (∑ k in Finset.range 98, u k.succ) = 137) :
    (∑ k in Finset.range 49, u (2 * k.succ)) = 93 := by
  have h_main : (∑ k in Finset.range 49, u (2 * k.succ)) = 93 := by
    have h₂ : ∀ n, u n = u 0 + n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h₃ := h₀ n
        simp [ih] at h₃ ⊢
        <;> linarith
    have h₃ : (∑ k in Finset.range 98, u k.succ) = 137 := h₁
    have h₄ : (∑ k in Finset.range 49, u (2 * k.succ)) = 93 := by
      simp [h₂, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h₃ ⊢
      <;> ring_nf at h₃ ⊢ <;> norm_num at h₃ ⊢ <;> linarith
    exact h₄
  exact h_main
