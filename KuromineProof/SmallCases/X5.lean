import KuromineProof.SmallCases.Residues

namespace KuromineProof

private theorem y_mod_six_eq_three_of_solution_x_eq_five
    {y z : ℕ}
    (h : Solves 5 y z) :
    y % 6 = 3 := by
  unfold Solves at h
  have hmod8 : (2 ^ 5 + 3 ^ y + 5) % 8 = (z ^ 3) % 8 :=
    congrArg (fun n : ℕ => n % 8) h
  have hy_odd : y % 2 = 1 := by
    have hy_mod_lt : y % 2 < 2 := Nat.mod_lt y (by norm_num)
    by_contra hne
    have hy_even : y % 2 = 0 := by omega
    have hleft : (2 ^ 5 + 3 ^ y + 5) % 8 = 6 := by
      calc
        (2 ^ 5 + 3 ^ y + 5) % 8 = (3 ^ y + 37) % 8 := by
          apply congrArg (fun n : ℕ => n % 8)
          omega
        _ = (3 ^ y % 8 + 37 % 8) % 8 := Nat.add_mod _ _ _
        _ = 6 := by simp [pow_three_mod8_of_even hy_even]
    rw [hleft] at hmod8
    exact cube_mod8_ne_six z hmod8.symm
  have hy6_ne1 : y % 6 ≠ 1 := by
    intro hy6
    have hmod7 : (2 ^ 5 + 3 ^ y + 5) % 7 = (z ^ 3) % 7 :=
      congrArg (fun n : ℕ => n % 7) h
    have hleft : (2 ^ 5 + 3 ^ y + 5) % 7 = 5 := by
      calc
        (2 ^ 5 + 3 ^ y + 5) % 7 = (3 ^ y + 37) % 7 := by
          apply congrArg (fun n : ℕ => n % 7)
          omega
        _ = (3 ^ y % 7 + 37 % 7) % 7 := Nat.add_mod _ _ _
        _ = 5 := by simp [pow_three_mod7_of_mod6_eq_one hy6]
    rw [hleft] at hmod7
    rcases cube_mod7_cases z with hz0 | hz1 | hz6 <;> omega
  have hy6_ne5 : y % 6 ≠ 5 := by
    intro hy6
    have hmod13 : (2 ^ 5 + 3 ^ y + 5) % 13 = (z ^ 3) % 13 :=
      congrArg (fun n : ℕ => n % 13) h
    have hleft : (2 ^ 5 + 3 ^ y + 5) % 13 = 7 := by
      calc
        (2 ^ 5 + 3 ^ y + 5) % 13 = (3 ^ y + 37) % 13 := by
          apply congrArg (fun n : ℕ => n % 13)
          omega
        _ = (3 ^ y % 13 + 37 % 13) % 13 := Nat.add_mod _ _ _
        _ = 7 := by simp [pow_three_mod13_of_mod6_eq_five hy6]
    rw [hleft] at hmod13
    exact cube_mod13_ne_seven z hmod13.symm
  have hy6_lt : y % 6 < 6 := Nat.mod_lt y (by norm_num)
  have hy6_odd : (y % 6) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd y (by norm_num : 2 ∣ 6)]
    exact hy_odd
  omega

/-- The only solution with `x = 5` is `(y,z) = (3,4)`. -/
theorem classify_solution_x_eq_five
    {y z : ℕ}
    (h : Solves 5 y z) :
    y = 3 ∧ z = 4 := by
  have hy6_eq3 : y % 6 = 3 :=
    y_mod_six_eq_three_of_solution_x_eq_five h
  have hy_div3 : 3 ∣ y := by
    apply Nat.dvd_of_mod_eq_zero
    calc
      y % 3 = (y % 6) % 3 :=
        (Nat.mod_mod_of_dvd y (by norm_num : 3 ∣ 6)).symm
      _ = 0 := by norm_num [hy6_eq3]
  obtain ⟨η, rfl⟩ := hy_div3
  unfold Solves at h
  let t : ℕ := 3 ^ η
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_cube : t ^ 3 = 3 ^ (3 * η) := by
    dsimp [t]
    rw [← Nat.pow_mul, mul_comm]
  have hsum : 37 + t ^ 3 = z ^ 3 := by
    rw [ht_cube]
    omega
  have ht_lt_z : t < z := by
    apply lt_of_pow_lt_pow_left' 3
    omega
  let d : ℕ := z - t
  let q : ℕ := z ^ 2 + z * t + t ^ 2
  have hd_pos : 0 < d := by
    dsimp [d]
    omega
  have hz_eq : z = d + t := by
    dsimp [d]
    omega
  have hfactor : d * q + t ^ 3 = z ^ 3 := by
    calc
      d * q + t ^ 3 =
          d * ((d + t) ^ 2 + (d + t) * t + t ^ 2) + t ^ 3 := by
            simp [q, hz_eq]
      _ = (d + t) ^ 3 := by ring
      _ = z ^ 3 := by rw [← hz_eq]
  have hprod : d * q = 37 := by omega
  have hcases : d = 1 ∨ d = 37 :=
    (Nat.dvd_prime (by norm_num)).mp ⟨q, hprod.symm⟩
  rcases hcases with h_one | h_37
  · have hz_eq_t1 : z = t + 1 := by omega
    have hq37 : q = 37 := by simpa [h_one] using hprod
    have hprod12 : t * (t + 1) = 12 := by
      have halgebra : 3 * (t * (t + 1)) + 1 = 37 := by
        calc
          3 * (t * (t + 1)) + 1 =
              (t + 1) ^ 2 + (t + 1) * t + t ^ 2 := by ring
          _ = q := by simp [q, hz_eq_t1]
          _ = 37 := hq37
      omega
    have ht_lt_four : t < 4 := by
      nlinarith [hprod12]
    have ht_eq_three : t = 3 := by
      interval_cases t <;> norm_num at hprod12 <;> omega
    have hη1 : η = 1 := by
      by_cases hη0 : η = 0
      · subst η
        norm_num [t] at ht_eq_three
      by_cases hη1 : η = 1
      · exact hη1
      · have hη2 : 2 ≤ η := by omega
        obtain ⟨k, hk⟩ : ∃ k, η = k + 2 := ⟨η - 2, by omega⟩
        have hkpow_pos : 0 < 3 ^ k := by positivity
        dsimp [t] at ht_eq_three
        rw [hk, pow_add] at ht_eq_three
        norm_num at ht_eq_three
        omega
    omega
  · have hprod37 : 37 * q = 37 := by
      calc
        37 * q = d * q := by rw [h_37]
        _ = 37 := hprod
    have hq1 : q = 1 := by
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 37)
      simpa using hprod37
    have hz2 : 2 ≤ z := by omega
    have hzsq : 4 ≤ z ^ 2 := by
      calc
        4 = 2 * 2 := by norm_num
        _ ≤ z * z := Nat.mul_le_mul hz2 hz2
        _ = z ^ 2 := by ring
    have hzsq_le_q : z ^ 2 ≤ q := by
      dsimp [q]
      calc
        z ^ 2 ≤ z ^ 2 + z * t := Nat.le_add_right _ _
        _ ≤ z ^ 2 + z * t + t ^ 2 := Nat.le_add_right _ _
    omega

end KuromineProof
