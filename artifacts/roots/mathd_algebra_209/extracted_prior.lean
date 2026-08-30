theorem mathd_algebra_209 (σ : Equiv ℝ ℝ) (h₀ : σ.2 2 = 10) (h₁ : σ.2 10 = 1) (h₂ : σ.2 1 = 2) :
    σ.1 (σ.1 10) = 1 := by
  have h_main : σ.1 (σ.1 10) = 1 := by
    have h₃ := σ.symm_apply_apply 10
    have h₄ := σ.symm_apply_apply 1
    have h₅ := σ.symm_apply_apply 2
    have h₆ := σ.symm_apply_apply (σ.1 10)
    have h₇ := σ.symm_apply_apply (σ.1 1)
    have h₈ := σ.symm_apply_apply (σ.1 2)
    simp_all [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    <;>
    (try ring_nf at * <;> nlinarith) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        simp_all [Equiv.symm_apply_apply]
        <;>
        aesop
      })
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        simp_all [Equiv.symm_apply_apply]
        <;>
        aesop
      })
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        simp_all [Equiv.symm_apply_apply]
        <;>
        aesop
      })
    <;>
    (try
      {
        aesop
      })
  exact h_main
