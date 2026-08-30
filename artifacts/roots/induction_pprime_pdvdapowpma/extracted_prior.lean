theorem induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) : p ∣ a ^ p - a := by
  have h_main : p ∣ a ^ p - a := by
    haveI := Fact.mk h₁
    simp [← ZMod.natCast_zmod_eq_zero_iff_dvd, ← ZMod.eq_iff_modEq_nat]
    <;>
    (try cases p <;> simp_all [Nat.Prime, Nat.succ_le_iff])
    <;>
    (try simp_all [Nat.Prime, Nat.succ_le_iff, Nat.pow_succ, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod])
    <;>
    (try omega)
    <;>
    (try
      {
        induction a with
        | zero => simp_all [Nat.Prime]
        | succ a ih =>
          cases a with
          | zero => simp_all [Nat.Prime]
          | succ a =>
            simp_all [Nat.Prime, Nat.succ_le_iff, Nat.pow_succ, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
            <;>
            ring_nf at *
            <;>
            omega
      })
    <;>
    (try
      {
        cases p with
        | zero => contradiction
        | succ p =>
          cases p with
          | zero => contradiction
          | succ p =>
            simp_all [Nat.Prime, Nat.succ_le_iff, Nat.pow_succ, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
            <;>
            ring_nf at *
            <;>
            omega
      })
    <;>
    (try
      {
        simp_all [Nat.Prime, Nat.succ_le_iff, Nat.pow_succ, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
        <;>
        ring_nf at *
        <;>
        omega
      })
    <;>
    (try
      {
        simp_all [Nat.Prime, Nat.succ_le_iff, Nat.pow_succ, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
        <;>
        ring_nf at *
        <;>
        omega
      })
  exact h_main
