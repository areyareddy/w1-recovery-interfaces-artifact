theorem mathd_numbertheory_343 : (∏ k in Finset.range 6, 2 * k + 1) % 10 = 5 := by
  have h_main : (∏ k in Finset.range 6, 2 * k + 1) % 10 = 5 := by
    norm_num [Finset.prod_range_succ, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_zero]
    <;> rfl
  exact h_main
