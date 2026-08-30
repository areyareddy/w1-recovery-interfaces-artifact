theorem imo_2019_p1 (f : ℤ → ℤ) :
    (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔ ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  have h_imp : (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) → (∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c) := by
    intro hf
    have h1 : (∀ a, f (2 * a) = 2 * f a - f 0) := by
      intro a
      have h2 := hf a 0
      have h3 := hf 0 a
      have h4 := hf a a
      have h5 := hf 0 0
      have h6 := hf a (-a)
      have h7 := hf (-a) a
      have h8 := hf a 1
      have h9 := hf 1 a
      have h10 := hf a (-1)
      have h11 := hf (-1) a
      have h12 := hf a 2
      have h13 := hf 2 a
      have h14 := hf a (-2)
      have h15 := hf (-2) a
      ring_nf at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 ⊢
      <;> linarith
    have h2 : f 0 = 0 := by
      have h3 := hf 0 0
      have h4 := hf 0 1
      have h5 := hf 1 0
      have h6 := hf 1 1
      have h7 := hf (-1) 0
      have h8 := hf 0 (-1)
      have h9 := hf (-1) (-1)
      have h10 := hf 2 0
      have h11 := hf 0 2
      have h12 := hf 1 (-1)
      have h13 := hf (-1) 1
      have h14 := hf 2 1
      have h15 := hf 1 2
      have h16 := hf 2 (-1)
      have h17 := hf (-1) 2
      have h18 := hf 3 0
      have h19 := hf 0 3
      have h20 := hf 3 1
      have h21 := hf 1 3
      have h22 := hf 3 (-1)
      have h23 := hf (-1) 3
      have h24 := hf 3 2
      have h25 := hf 2 3
      have h26 := hf 3 (-2)
      have h27 := hf (-2) 3
      have h28 := hf 4 0
      have h29 := hf 0 4
      have h30 := hf 4 1
      have h31 := hf 1 4
      have h32 := hf 4 (-1)
      have h33 := hf (-1) 4
      have h34 := hf 4 2
      have h35 := hf 2 4
      have h36 := hf 4 (-2)
      have h37 := hf (-2) 4
      have h38 := hf 4 3
      have h39 := hf 3 4
      have h40 := hf 4 (-3)
      have h41 := hf (-3) 4
      norm_num at h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 ⊢
      <;> linarith
    have h3 : (∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c) := by
      intro z
      by_cases h : f z = 0
      · exact Or.inl h
      · -- If f(z) ≠ 0, then f must be of the form f(z) = 2z + c
        have h4 : ∃ c, ∀ z, f z = 2 * z + c := by
          use f 1 - 2 * 1
          intro z
          have h5 := h1 0
          have h6 := h1 1
          have h7 := h1 (-1)
          have h8 := h1 2
          have h9 := h1 (-2)
          have h10 := hf 0 0
          have h11 := hf 0 1
          have h12 := hf 1 0
          have h13 := hf 1 1
          have h14 := hf (-1) 0
          have h15 := hf 0 (-1)
          have h16 := hf (-1) (-1)
          have h17 := hf 2 0
          have h18 := hf 0 2
          have h19 := hf 1 (-1)
          have h20 := hf (-1) 1
          have h21 := hf 2 1
          have h22 := hf 1 2
          have h23 := hf 2 (-1)
          have h24 := hf (-1) 2
          have h25 := hf 3 0
          have h26 := hf 0 3
          have h27 := hf 3 1
          have h28 := hf 1 3
          have h29 := hf 3 (-1)
          have h30 := hf (-1) 3
          have h31 := hf 3 2
          have h32 := hf 2 3
          have h33 := hf 3 (-2)
          have h34 := hf (-2) 3
          have h35 := hf 4 0
          have h36 := hf 0 4
          have h37 := hf 4 1
          have h38 := hf 1 4
          have h39 := hf 4 (-1)
          have h40 := hf (-1) 4
          have h41 := hf 4 2
          have h42 := hf 2 4
          have h43 := hf 4 (-2)
          have h44 := hf (-2) 4
          have h45 := hf 4 3
          have h46 := hf 3 4
          have h47 := hf 4 (-3)
          have h48 := hf (-3) 4
          norm_num at h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 ⊢
          <;>
          (try omega) <;>
          (try ring_nf at * <;> omega) <;>
          (try
            {
              have h49 := h1 z
              have h50 := h1 (-z)
              have h51 := hf z 0
              have h52 := hf 0 z
              have h53 := hf z 1
              have h54 := hf 1 z
              have h55 := hf z (-1)
              have h56 := hf (-1) z
              have h57 := hf z 2
              have h58 := hf 2 z
              have h59 := hf z (-2)
              have h60 := hf (-2) z
              have h61 := hf z 3
              have h62 := hf 3 z
              have h63 := hf z (-3)
              have h64 := hf (-3) z
              have h65 := hf z 4
              have h66 := hf 4 z
              have h67 := hf z (-4)
              have h68 := hf (-4) z
              ring_nf at h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 ⊢
              <;> omega
            })
          <;>
          (try
            {
              have h49 := h1 z
              have h50 := h1 (-z)
              have h51 := hf z 0
              have h52 := hf 0 z
              have h53 := hf z 1
              have h54 := hf 1 z
              have h55 := hf z (-1)
              have h56 := hf (-1) z
              have h57 := hf z 2
              have h58 := hf 2 z
              have h59 := hf z (-2)
              have h60 := hf (-2) z
              have h61 := hf z 3
              have h62 := hf 3 z
              have h63 := hf z (-3)
              have h64 := hf (-3) z
              have h65 := hf z 4
              have h66 := hf 4 z
              have h67 := hf z (-4)
              have h68 := hf (-4) z
              ring_nf at h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 ⊢
              <;> omega
            })
          <;>
          (try omega)
        exact Or.inr h4
    exact h3
  have h_conv : (∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c) → (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) := by
    intro hf
    have h1 : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
      intro a b
      have h2 := hf 0
      have h3 := hf 1
      have h4 := hf (-1)
      have h5 := hf 2
      have h6 := hf (-2)
      have h7 := hf 3
      have h8 := hf (-3)
      have h9 := hf 4
      have h10 := hf (-4)
      cases' h2 with h2 h2 <;> cases' h3 with h3 h3 <;> cases' h4 with h4 h4 <;> cases' h5 with h5 h5 <;> cases' h6 with h6 h6 <;> cases' h7 with h7 h7 <;> cases' h8 with h8 h8 <;> cases' h9 with h9 h9 <;> cases' h10 with h10 h10 <;>
        (try omega) <;>
        (try
          {
            simp_all [h2, h3, h4, h5, h6, h7, h8, h9, h10]
            <;>
            ring_nf at *
            <;>
            omega
          }) <;>
        (try
          {
            simp_all [h2, h3, h4, h5, h6, h7, h8, h9, h10]
            <;>
            ring_nf at *
            <;>
            omega
          }) <;>
        (try
          {
            simp_all [h2, h3, h4, h5, h6, h7, h8, h9, h10]
            <;>
            ring_nf at *
            <;>
            omega
          })
    exact h1
  have h_main : (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔ ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
    constructor
    · -- Prove the forward direction
      intro h
      exact h_imp h
    · -- Prove the backward direction
      intro h
      exact h_conv h
  exact h_main
