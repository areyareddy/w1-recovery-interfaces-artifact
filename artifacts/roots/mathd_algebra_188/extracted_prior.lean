theorem mathd_algebra_188 (σ : Equiv ℝ ℝ) (h : σ.1 2 = σ.2 2) : σ.1 (σ.1 2) = 2 := by
  have h₁ : σ.1 (σ.2 2) = 2 := by
    apply Equiv.apply_inv
    <;> simp_all [Equiv.inv_apply_apply]
    <;> aesop
  
  have h₂ : σ.1 (σ.1 2) = σ.1 (σ.2 2) := by
    rw [h]
    <;> simp [h₁]
    <;> aesop
  
  have h₃ : σ.1 (σ.1 2) = 2 := by
    rw [h₂]
    rw [h₁]
    <;> simp_all
    <;> aesop
  
  apply h₃
