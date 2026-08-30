theorem amc12a_2020_p4 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
    S.card = 100 := by
  have h₁ : S = Finset.filter (fun n => 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) (Finset.Icc 1000 9999) := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_filter, Finset.mem_Icc, h₀]
    <;>
    aesop
  
  have h₂ : S.card = 100 := by
    rw [h₁]
    -- We need to count the number of 4-digit numbers with all even digits and divisible by 5.
    -- The numbers are of the form n = 1000a + 100b + 10c where a ∈ {2, 4, 6, 8}, b, c ∈ {0, 2, 4, 6, 8}, and d = 0.
    -- There are 4 choices for a, 5 choices for b, and 5 choices for c, giving 4 * 5 * 5 = 100 numbers.
    rfl
    <;>
    decide
  
  apply h₂
