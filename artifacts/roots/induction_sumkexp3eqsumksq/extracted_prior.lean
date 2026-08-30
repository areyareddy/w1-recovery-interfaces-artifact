theorem induction_sumkexp3eqsumksq (n : ℕ) :
    (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
  have h_main : (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
    have h₁ : ∀ n : ℕ, (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        cases n with
        | zero =>
          simp [Finset.sum_range_succ]
        | succ n =>
          simp_all [Finset.sum_range_succ, pow_two, pow_three, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
          <;> ring_nf at *
          <;>
            (try omega)
          <;>
            (try
              {
                nlinarith [sq_nonneg (n + 1), sq_nonneg (n + 2), sq_nonneg (n + 3), sq_nonneg (n + 4)]
              })
          <;>
            (try
              {
                simp_all [Finset.sum_range_succ, pow_two, pow_three, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
                <;> ring_nf at *
                <;> omega
              })
          <;>
            (try
              {
                ring_nf at *
                <;> omega
              })
          <;>
            (try
              {
                nlinarith [sq_nonneg (n + 1), sq_nonneg (n + 2), sq_nonneg (n + 3), sq_nonneg (n + 4)]
              })
    exact h₁ n
  exact h_main
