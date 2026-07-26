import KuromineProof.SmallCases.Residues

namespace KuromineProof

theorem no_solution_x_eq_zero {y z : ℕ} (h : Solves 0 y z) : False := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 7 := by omega
    have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
    interval_cases z <;> omega
  · by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 9 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
      interval_cases z <;> omega
    · by_cases hy2 : y = 2
      · subst y
        have hz : z ^ 3 = 15 := by omega
        have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
        interval_cases z <;> omega
      · have hy3 : 3 ≤ y := by omega
        have hmod : (2 ^ 0 + 3 ^ y + 5) % 27 = (z ^ 3) % 27 :=
          congrArg (fun n : ℕ => n % 27) h
        have hleft : (2 ^ 0 + 3 ^ y + 5) % 27 = 6 := by
          calc
            (2 ^ 0 + 3 ^ y + 5) % 27 = (3 ^ y + 6) % 27 := by
              apply congrArg (fun n : ℕ => n % 27); omega
            _ = (3 ^ y % 27 + 6 % 27) % 27 := Nat.add_mod _ _ _
            _ = 6 := by simp [pow_three_mod27_zero hy3]
        rw [hleft] at hmod
        exact cube_mod27_ne_six z hmod.symm

theorem classify_solution_x_eq_one {y z : ℕ} (h : Solves 1 y z) : y = 0 ∧ z = 2 := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 8 := by omega
    have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
    interval_cases z <;> omega
  · exfalso
    by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 10 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
      interval_cases z <;> omega
    · have hy2 : 2 ≤ y := by omega
      have hmod : (2 ^ 1 + 3 ^ y + 5) % 9 = (z ^ 3) % 9 :=
        congrArg (fun n : ℕ => n % 9) h
      have hleft : (2 ^ 1 + 3 ^ y + 5) % 9 = 7 := by
        calc
          (2 ^ 1 + 3 ^ y + 5) % 9 = (3 ^ y + 7) % 9 := by
            apply congrArg (fun n : ℕ => n % 9); omega
          _ = (3 ^ y % 9 + 7 % 9) % 9 := Nat.add_mod _ _ _
          _ = 7 := by simp [pow_three_mod9_zero hy2]
      rw [hleft] at hmod
      exact cube_mod9_ne_seven z hmod.symm

theorem no_solution_x_eq_two {y z : ℕ} (h : Solves 2 y z) : False := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 10 := by omega
    have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
    interval_cases z <;> omega
  · by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 12 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
      interval_cases z <;> omega
    · by_cases hy2 : y = 2
      · subst y
        have hmod : (2 ^ 2 + 3 ^ 2 + 5) % 27 = (z ^ 3) % 27 :=
          congrArg (fun n : ℕ => n % 27) h
        norm_num at hmod
        exact cube_mod27_ne_eighteen z hmod.symm
      · have hy3 : 3 ≤ y := by omega
        have hmod : (2 ^ 2 + 3 ^ y + 5) % 27 = (z ^ 3) % 27 :=
          congrArg (fun n : ℕ => n % 27) h
        have hleft : (2 ^ 2 + 3 ^ y + 5) % 27 = 9 := by
          calc
            (2 ^ 2 + 3 ^ y + 5) % 27 = (3 ^ y + 9) % 27 := by
              apply congrArg (fun n : ℕ => n % 27); omega
            _ = (3 ^ y % 27 + 9 % 27) % 27 := Nat.add_mod _ _ _
            _ = 9 := by simp [pow_three_mod27_zero hy3]
        rw [hleft] at hmod
        exact cube_mod27_ne_nine z hmod.symm

theorem no_solution_x_eq_three {y z : ℕ} (h : Solves 3 y z) : False := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 14 := by omega
    have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
    interval_cases z <;> omega
  · by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 16 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
      interval_cases z <;> omega
    · have hy2 : 2 ≤ y := by omega
      have hmod : (2 ^ 3 + 3 ^ y + 5) % 9 = (z ^ 3) % 9 :=
        congrArg (fun n : ℕ => n % 9) h
      have hleft : (2 ^ 3 + 3 ^ y + 5) % 9 = 4 := by
        calc
          (2 ^ 3 + 3 ^ y + 5) % 9 = (3 ^ y + 13) % 9 := by
            apply congrArg (fun n : ℕ => n % 9); omega
          _ = (3 ^ y % 9 + 13 % 9) % 9 := Nat.add_mod _ _ _
          _ = 4 := by simp [pow_three_mod9_zero hy2]
      rw [hleft] at hmod
      exact cube_mod9_ne_four z hmod.symm

theorem no_solution_x_eq_four {y z : ℕ} (h : Solves 4 y z) : False := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 22 := by omega
    have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
    interval_cases z <;> omega
  · by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 24 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 (by omega)
      interval_cases z <;> omega
    · have hy2 : 2 ≤ y := by omega
      have hmod : (2 ^ 4 + 3 ^ y + 5) % 9 = (z ^ 3) % 9 :=
        congrArg (fun n : ℕ => n % 9) h
      have hleft : (2 ^ 4 + 3 ^ y + 5) % 9 = 3 := by
        calc
          (2 ^ 4 + 3 ^ y + 5) % 9 = (3 ^ y + 21) % 9 := by
            apply congrArg (fun n : ℕ => n % 9); omega
          _ = (3 ^ y % 9 + 21 % 9) % 9 := Nat.add_mod _ _ _
          _ = 3 := by simp [pow_three_mod9_zero hy2]
      rw [hleft] at hmod
      exact cube_mod9_ne_three z hmod.symm

end KuromineProof
