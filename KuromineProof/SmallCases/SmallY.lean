import KuromineProof.SmallCases.Residues

namespace KuromineProof

/-- The case `y = 0` has no solutions once `x ≥ 2`. -/
theorem no_solution_y0_x_ge_2 {x z : ℕ} (hx : 2 ≤ x) (h : Solves x 0 z) : False := by
  unfold Solves at h
  have hmod : (2 ^ x + 3 ^ 0 + 5) % 4 = (z ^ 3) % 4 :=
    congrArg (fun n : ℕ => n % 4) h
  have hleft : (2 ^ x + 3 ^ 0 + 5) % 4 = 2 := by
    calc
      (2 ^ x + 3 ^ 0 + 5) % 4 = (2 ^ x + 6) % 4 := by norm_num
      _ = (2 ^ x % 4 + 6 % 4) % 4 := Nat.add_mod _ _ _
      _ = 2 := by simp [pow_two_mod4_zero hx]
  rw [hleft] at hmod
  exact cube_mod4_ne_two z hmod.symm

/-- The case `y = 1` has no solutions. -/
theorem no_solution_y1 {x z : ℕ} (h : Solves x 1 z) : False := by
  unfold Solves at h
  have hmod : (2 ^ x + 3 ^ 1 + 5) % 7 = (z ^ 3) % 7 :=
    congrArg (fun n : ℕ => n % 7) h
  have hleft : (2 ^ x + 3 ^ 1 + 5) % 7 = (2 ^ x % 7 + 1) % 7 := by
    calc
      (2 ^ x + 3 ^ 1 + 5) % 7 = (2 ^ x + 8) % 7 := by norm_num
      _ = (2 ^ x % 7 + 8 % 7) % 7 := Nat.add_mod _ _ _
      _ = (2 ^ x % 7 + 1) % 7 := by norm_num
  rw [hleft] at hmod
  rcases pow_two_mod7 x with h2 | h2 | h2 <;> rw [h2] at hmod <;>
    rcases cube_mod7_cases z with h3 | h3 | h3 <;> omega

/-- The case `y = 2` has no solutions once `x ≥ 3`. -/
theorem no_solution_y2_x_ge_3 {x z : ℕ} (hx : 3 ≤ x) (h : Solves x 2 z) : False := by
  unfold Solves at h
  have hmod : (2 ^ x + 3 ^ 2 + 5) % 8 = (z ^ 3) % 8 :=
    congrArg (fun n : ℕ => n % 8) h
  have hleft : (2 ^ x + 3 ^ 2 + 5) % 8 = 6 := by
    calc
      (2 ^ x + 3 ^ 2 + 5) % 8 = (2 ^ x + 14) % 8 := by norm_num
      _ = (2 ^ x % 8 + 14 % 8) % 8 := Nat.add_mod _ _ _
      _ = 6 := by simp [pow_two_mod8_zero hx]
  rw [hleft] at hmod
  exact cube_mod8_ne_six z hmod.symm

end KuromineProof
