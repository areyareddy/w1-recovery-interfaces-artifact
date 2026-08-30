theorem mathd_numbertheory_235 : (29 * 79 + 31 * 81) % 10 = 2 := by
  have h1 : (29 * 79) % 10 = 1 := by
    norm_num [Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt]
    <;> rfl
  
  have h2 : (31 * 81) % 10 = 1 := by
    norm_num [Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt]
    <;> rfl
  
  have h3 : (29 * 79 + 31 * 81) % 10 = 2 := by
    have h4 : (29 * 79 + 31 * 81) % 10 = ((29 * 79) % 10 + (31 * 81) % 10) % 10 := by
      norm_num [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_eq_of_lt]
      <;> rfl
    rw [h4]
    rw [h1, h2]
    <;> norm_num
    <;> rfl
  
  apply h3
