import KuromineProof.NaturalClassification

namespace KuromineProof

/-- The Kuromine equation with integer exponents, interpreted in `ℚ`. -/
def SolvesInteger (x y z : ℤ) : Prop :=
  (2 : ℚ) ^ x + (3 : ℚ) ^ y + 5 = (z : ℚ) ^ (3 : ℕ)

private theorem no_both_exponents_negative
    (a b : ℕ) (z : ℤ)
    (h : SolvesInteger (Int.negSucc a) (Int.negSucc b) z) :
    False := by
  unfold SolvesInteger at h
  simp at h
  field_simp at h
  have hZ :
      (3 : ℤ) ^ (b + 1) + (2 : ℤ) ^ (a + 1) +
          (2 : ℤ) ^ (a + 1) * (3 : ℤ) ^ (b + 1) * 5 =
        (2 : ℤ) ^ (a + 1) * (3 : ℤ) ^ (b + 1) * z ^ 3 := by
    exact_mod_cast h
  have hmod := congrArg (fun n : ℤ => (n : ZMod 2)) hZ
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hthree : (3 : ZMod 2) = 1 := by decide
  simp [pow_succ, htwo, hthree] at hmod

private theorem no_negative_y
    (x b : ℕ) (z : ℤ)
    (h : SolvesInteger (Int.ofNat x) (Int.negSucc b) z) :
    False := by
  unfold SolvesInteger at h
  simp at h
  field_simp at h
  have hZ :
      (2 : ℤ) ^ x * (3 : ℤ) ^ (b + 1) + 1 +
          (3 : ℤ) ^ (b + 1) * 5 =
        (3 : ℤ) ^ (b + 1) * z ^ 3 := by
    exact_mod_cast h
  have hmod := congrArg (fun n : ℤ => (n : ZMod 3)) hZ
  have hthree : (3 : ZMod 3) = 0 := by decide
  simp [pow_succ, hthree] at hmod

private theorem no_negative_x
    (a y : ℕ) (z : ℤ)
    (h : SolvesInteger (Int.negSucc a) (Int.ofNat y) z) :
    False := by
  unfold SolvesInteger at h
  simp at h
  field_simp at h
  have hZ :
      1 + (2 : ℤ) ^ (a + 1) * (3 : ℤ) ^ y +
          (2 : ℤ) ^ (a + 1) * 5 =
        (2 : ℤ) ^ (a + 1) * z ^ 3 := by
    exact_mod_cast h
  have hmod := congrArg (fun n : ℤ => (n : ZMod 2)) hZ
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [pow_succ, htwo] at hmod

private theorem integer_exponents_nonnegative
    {x y z : ℤ}
    (h : SolvesInteger x y z) :
    0 ≤ x ∧ 0 ≤ y := by
  cases x with
  | negSucc a =>
      cases y with
      | negSucc b => exact (no_both_exponents_negative a b z h).elim
      | ofNat ny => exact (no_negative_x a ny z h).elim
  | ofNat nx =>
      cases y with
      | negSucc b => exact (no_negative_y nx b z h).elim
      | ofNat ny => exact ⟨by simp, by simp⟩

private theorem integer_z_positive
    {x y z : ℤ}
    (h : SolvesInteger x y z)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    0 < z := by
  cases x with
  | negSucc a => omega
  | ofNat nx =>
      cases y with
      | negSucc b => omega
      | ofNat ny =>
          have hQ :
              (2 : ℚ) ^ nx + (3 : ℚ) ^ ny + 5 = (z : ℚ) ^ 3 := by
            simpa [SolvesInteger] using h
          have hz3pos : 0 < (z : ℚ) ^ 3 := by
            rw [← hQ]
            positivity
          have hzQpos : 0 < (z : ℚ) := by
            by_contra hz
            have hznonpos : (z : ℚ) ≤ 0 := le_of_not_gt hz
            have hzsq : 0 ≤ (z : ℚ) ^ 2 := sq_nonneg _
            have hcube_nonpos : (z : ℚ) ^ 3 ≤ 0 := by
              calc
                (z : ℚ) ^ 3 = (z : ℚ) * (z : ℚ) ^ 2 := by ring
                _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hznonpos hzsq
            linarith
          exact_mod_cast hzQpos

/-- Every integer solution has nonnegative exponents and positive `z`. -/
theorem integer_solution_signs
    {x y z : ℤ}
    (h : SolvesInteger x y z) :
    0 ≤ x ∧ 0 ≤ y ∧ 0 < z := by
  obtain ⟨hx, hy⟩ := integer_exponents_nonnegative h
  exact ⟨hx, hy, integer_z_positive h hx hy⟩

/-- An integer solution reduces to a solution over natural numbers. -/
theorem integer_solution_reduces
    {x y z : ℤ}
    (h : SolvesInteger x y z) :
    ∃ nx ny nz : ℕ,
      x = nx ∧ y = ny ∧ z = nz ∧ Solves nx ny nz := by
  have hs := integer_solution_signs h
  cases x with
  | negSucc a => omega
  | ofNat nx =>
      cases y with
      | negSucc b => omega
      | ofNat ny =>
          cases z with
          | negSucc c => omega
          | ofNat nz =>
              refine ⟨nx, ny, nz, rfl, rfl, rfl, ?_⟩
              have hQ :
                  (2 : ℚ) ^ nx + (3 : ℚ) ^ ny + 5 = (nz : ℚ) ^ 3 := by
                simpa [SolvesInteger] using h
              unfold Solves
              exact_mod_cast hQ

/-- Complete classification for integer exponents and integer `z`. -/
theorem classify_integer_solutions
    {x y z : ℤ}
    (h : SolvesInteger x y z) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨
    (x = 5 ∧ y = 3 ∧ z = 4) := by
  rcases integer_solution_reduces h with
    ⟨nx, ny, nz, rfl, rfl, rfl, hnat⟩
  rcases classify_natural_solutions hnat with h1 | h2
  · left
    rcases h1 with ⟨rfl, rfl, rfl⟩
    norm_num
  · right
    rcases h2 with ⟨rfl, rfl, rfl⟩
    norm_num

end KuromineProof
