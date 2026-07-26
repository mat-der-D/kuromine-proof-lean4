import KuromineProof.Basic

namespace KuromineProof

private theorem cube_mod4_ne_two (z : ℕ) : (z ^ 3) % 4 ≠ 2 := by
  rw [Nat.pow_mod z 3 4]
  have hr : z % 4 < 4 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 4 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem cube_mod8_ne_six (z : ℕ) : (z ^ 3) % 8 ≠ 6 := by
  rw [Nat.pow_mod z 3 8]
  have hr : z % 8 < 8 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 8 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem cube_mod9_ne_three (z : ℕ) : (z ^ 3) % 9 ≠ 3 := by
  rw [Nat.pow_mod z 3 9]
  have hr : z % 9 < 9 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 9 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem cube_mod9_ne_four (z : ℕ) : (z ^ 3) % 9 ≠ 4 := by
  rw [Nat.pow_mod z 3 9]
  have hr : z % 9 < 9 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 9 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem cube_mod9_ne_seven (z : ℕ) : (z ^ 3) % 9 ≠ 7 := by
  rw [Nat.pow_mod z 3 9]
  have hr : z % 9 < 9 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 9 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem cube_mod27_ne_six (z : ℕ) : (z ^ 3) % 27 ≠ 6 := by
  rw [Nat.pow_mod z 3 27]
  have hr : z % 27 < 27 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 27 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem cube_mod27_ne_nine (z : ℕ) : (z ^ 3) % 27 ≠ 9 := by
  rw [Nat.pow_mod z 3 27]
  have hr : z % 27 < 27 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 27 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem cube_mod27_ne_eighteen (z : ℕ) : (z ^ 3) % 27 ≠ 18 := by
  rw [Nat.pow_mod z 3 27]
  have hr : z % 27 < 27 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 27 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem cube_mod13_ne_seven (z : ℕ) : (z ^ 3) % 13 ≠ 7 := by
  rw [Nat.pow_mod z 3 13]
  have hr : z % 13 < 13 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 13 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem pow_two_mod7 (x : ℕ) :
    2 ^ x % 7 = 1 ∨ 2 ^ x % 7 = 2 ∨ 2 ^ x % 7 = 4 := by
  induction x with
  | zero => left; rfl
  | succ x ih =>
      rcases ih with h1 | h2 | h4
      · right; left
        calc
          2 ^ (x + 1) % 7 = (2 ^ x * 2) % 7 := by rfl
          _ = (2 ^ x % 7 * 2) % 7 := Nat.mul_mod _ _ _
          _ = 2 := by simp [h1]
      · right; right
        calc
          2 ^ (x + 1) % 7 = (2 ^ x * 2) % 7 := by rfl
          _ = (2 ^ x % 7 * 2) % 7 := Nat.mul_mod _ _ _
          _ = 4 := by simp [h2]
      · left
        calc
          2 ^ (x + 1) % 7 = (2 ^ x * 2) % 7 := by rfl
          _ = (2 ^ x % 7 * 2) % 7 := Nat.mul_mod _ _ _
          _ = 1 := by simp [h4]

private theorem cube_mod7_cases (z : ℕ) :
    (z ^ 3) % 7 = 0 ∨ (z ^ 3) % 7 = 1 ∨ (z ^ 3) % 7 = 6 := by
  rw [Nat.pow_mod z 3 7]
  have hr : z % 7 < 7 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 7 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem pow_three_mod8_of_even {y : ℕ} (hy : y % 2 = 0) :
    3 ^ y % 8 = 1 := by
  have hdiv : y = 2 * (y / 2) := by
    have h := (Nat.div_add_mod y 2).symm
    omega
  have hp := congrArg (fun n : ℕ => 3 ^ n % 8) hdiv
  calc
    3 ^ y % 8 = 3 ^ (2 * (y / 2)) % 8 := hp
    _ = (3 ^ 2) ^ (y / 2) % 8 := by rw [pow_mul]
    _ = ((3 ^ 2 % 8) ^ (y / 2)) % 8 := Nat.pow_mod _ _ _
    _ = 1 := by norm_num

private theorem pow_three_mod7_of_mod6_eq_one {y : ℕ} (hy : y % 6 = 1) :
    3 ^ y % 7 = 3 := by
  have hdiv : y = 6 * (y / 6) + 1 := by
    have h := (Nat.div_add_mod y 6).symm
    omega
  have hp := congrArg (fun n : ℕ => 3 ^ n % 7) hdiv
  calc
    3 ^ y % 7 = 3 ^ (6 * (y / 6) + 1) % 7 := hp
    _ = ((3 ^ 6) ^ (y / 6) * 3) % 7 := by rw [pow_add, pow_mul]; norm_num
    _ = (((3 ^ 6) ^ (y / 6) % 7) * (3 % 7)) % 7 := Nat.mul_mod _ _ _
    _ = 3 := by
      rw [Nat.pow_mod]
      norm_num

private theorem pow_three_mod13_of_mod6_eq_five {y : ℕ} (hy : y % 6 = 5) :
    3 ^ y % 13 = 9 := by
  have hdiv : y = 6 * (y / 6) + 5 := by
    have h := (Nat.div_add_mod y 6).symm
    omega
  have hp := congrArg (fun n : ℕ => 3 ^ n % 13) hdiv
  calc
    3 ^ y % 13 = 3 ^ (6 * (y / 6) + 5) % 13 := hp
    _ = ((3 ^ 6) ^ (y / 6) * 3 ^ 5) % 13 := by rw [pow_add, pow_mul]
    _ = (((3 ^ 6) ^ (y / 6) % 13) * (3 ^ 5 % 13)) % 13 := Nat.mul_mod _ _ _
    _ = 9 := by
      rw [Nat.pow_mod]
      norm_num

/-- The case `y = 0` has no solutions once `x ≥ 2`. -/
theorem no_solution_y0_x_ge_2 {x z : ℕ} (hx : 2 ≤ x) (h : Solves x 0 z) : False := by
  unfold Solves at h
  have h2x : 2 ^ x % 4 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, x = k + 2 := ⟨x - 2, by omega⟩
    calc
      2 ^ (k + 2) % 4 = (2 ^ k * 4) % 4 := by rw [pow_add]; norm_num
      _ = 0 := Nat.mul_mod_left (2 ^ k) 4
  have hmod := congrArg (fun n : ℕ => n % 4) h
  have hleft : (2 ^ x + 3 ^ 0 + 5) % 4 = 2 := by
    calc
      (2 ^ x + 3 ^ 0 + 5) % 4 = (2 ^ x + 6) % 4 := by norm_num
      _ = (2 ^ x % 4 + 6 % 4) % 4 := Nat.add_mod _ _ _
      _ = 2 := by simp [h2x]
  rw [hleft] at hmod
  exact cube_mod4_ne_two z hmod.symm

/-- The case `y = 1` has no solutions. -/
theorem no_solution_y1 {x z : ℕ} (h : Solves x 1 z) : False := by
  unfold Solves at h
  have hmod := congrArg (fun n : ℕ => n % 7) h
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
  have h2x : 2 ^ x % 8 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, x = k + 3 := ⟨x - 3, by omega⟩
    calc
      2 ^ (k + 3) % 8 = (2 ^ k * 8) % 8 := by rw [pow_add]; norm_num
      _ = 0 := Nat.mul_mod_left (2 ^ k) 8
  have hmod := congrArg (fun n : ℕ => n % 8) h
  have hleft : (2 ^ x + 3 ^ 2 + 5) % 8 = 6 := by
    calc
      (2 ^ x + 3 ^ 2 + 5) % 8 = (2 ^ x + 14) % 8 := by norm_num
      _ = (2 ^ x % 8 + 14 % 8) % 8 := Nat.add_mod _ _ _
      _ = 6 := by simp [h2x]
  rw [hleft] at hmod
  exact cube_mod8_ne_six z hmod.symm

private theorem solution_x_eq_zero {y z : ℕ} (h : Solves 0 y z) : False := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 7 := by omega
    have hcube : z ^ 3 < 3 ^ 3 := by omega
    have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
    interval_cases z <;> omega
  · by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 9 := by omega
      have hcube : z ^ 3 < 3 ^ 3 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
      interval_cases z <;> omega
    · by_cases hy2 : y = 2
      · subst y
        have hz : z ^ 3 = 15 := by omega
        have hcube : z ^ 3 < 3 ^ 3 := by omega
        have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
        interval_cases z <;> omega
      · have hy3 : 3 ≤ y := by omega
        have h3y : 3 ^ y % 27 = 0 := by
          obtain ⟨k, rfl⟩ : ∃ k, y = k + 3 := ⟨y - 3, by omega⟩
          calc
            3 ^ (k + 3) % 27 = (3 ^ k * 27) % 27 := by rw [pow_add]; norm_num
            _ = 0 := Nat.mul_mod_left (3 ^ k) 27
        have hmod := congrArg (fun n : ℕ => n % 27) h
        have hleft : (2 ^ 0 + 3 ^ y + 5) % 27 = 6 := by
          calc
            (2 ^ 0 + 3 ^ y + 5) % 27 = (3 ^ y + 6) % 27 := by
              apply congrArg (fun n : ℕ => n % 27); omega
            _ = (3 ^ y % 27 + 6 % 27) % 27 := Nat.add_mod _ _ _
            _ = 6 := by simp [h3y]
        rw [hleft] at hmod
        exact cube_mod27_ne_six z hmod.symm

private theorem solution_x_eq_one {y z : ℕ} (h : Solves 1 y z) : y = 0 ∧ z = 2 := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 8 := by omega
    have hz2 : z = 2 := by
      have hcube : z ^ 3 < 3 ^ 3 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
      interval_cases z <;> omega
    exact ⟨rfl, hz2⟩
  · exfalso
    by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 10 := by omega
      have hcube : z ^ 3 < 3 ^ 3 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
      interval_cases z <;> omega
    · have hy2 : 2 ≤ y := by omega
      have h3y : 3 ^ y % 9 = 0 := by
        obtain ⟨k, rfl⟩ : ∃ k, y = k + 2 := ⟨y - 2, by omega⟩
        calc
          3 ^ (k + 2) % 9 = (3 ^ k * 9) % 9 := by rw [pow_add]; norm_num
          _ = 0 := Nat.mul_mod_left (3 ^ k) 9
      have hmod := congrArg (fun n : ℕ => n % 9) h
      have hleft : (2 ^ 1 + 3 ^ y + 5) % 9 = 7 := by
        calc
          (2 ^ 1 + 3 ^ y + 5) % 9 = (3 ^ y + 7) % 9 := by
            apply congrArg (fun n : ℕ => n % 9); omega
          _ = (3 ^ y % 9 + 7 % 9) % 9 := Nat.add_mod _ _ _
          _ = 7 := by simp [h3y]
      rw [hleft] at hmod
      exact cube_mod9_ne_seven z hmod.symm

private theorem solution_x_eq_two {y z : ℕ} (h : Solves 2 y z) : False := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 10 := by omega
    have hcube : z ^ 3 < 3 ^ 3 := by omega
    have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
    interval_cases z <;> omega
  · by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 12 := by omega
      have hcube : z ^ 3 < 3 ^ 3 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
      interval_cases z <;> omega
    · by_cases hy2 : y = 2
      · subst y
        have hmod := congrArg (fun n : ℕ => n % 27) h
        norm_num at hmod
        exact cube_mod27_ne_eighteen z hmod.symm
      · have hy3 : 3 ≤ y := by omega
        have h3y : 3 ^ y % 27 = 0 := by
          obtain ⟨k, rfl⟩ : ∃ k, y = k + 3 := ⟨y - 3, by omega⟩
          calc
            3 ^ (k + 3) % 27 = (3 ^ k * 27) % 27 := by rw [pow_add]; norm_num
            _ = 0 := Nat.mul_mod_left (3 ^ k) 27
        have hmod := congrArg (fun n : ℕ => n % 27) h
        have hleft : (2 ^ 2 + 3 ^ y + 5) % 27 = 9 := by
          calc
            (2 ^ 2 + 3 ^ y + 5) % 27 = (3 ^ y + 9) % 27 := by
              apply congrArg (fun n : ℕ => n % 27); omega
            _ = (3 ^ y % 27 + 9 % 27) % 27 := Nat.add_mod _ _ _
            _ = 9 := by simp [h3y]
        rw [hleft] at hmod
        exact cube_mod27_ne_nine z hmod.symm

private theorem solution_x_eq_three {y z : ℕ} (h : Solves 3 y z) : False := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 14 := by omega
    have hcube : z ^ 3 < 3 ^ 3 := by omega
    have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
    interval_cases z <;> omega
  · by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 16 := by omega
      have hcube : z ^ 3 < 3 ^ 3 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
      interval_cases z <;> omega
    · have hy2 : 2 ≤ y := by omega
      have h3y : 3 ^ y % 9 = 0 := by
        obtain ⟨k, rfl⟩ : ∃ k, y = k + 2 := ⟨y - 2, by omega⟩
        calc
          3 ^ (k + 2) % 9 = (3 ^ k * 9) % 9 := by rw [pow_add]; norm_num
          _ = 0 := Nat.mul_mod_left (3 ^ k) 9
      have hmod := congrArg (fun n : ℕ => n % 9) h
      have hleft : (2 ^ 3 + 3 ^ y + 5) % 9 = 4 := by
        calc
          (2 ^ 3 + 3 ^ y + 5) % 9 = (3 ^ y + 13) % 9 := by
            apply congrArg (fun n : ℕ => n % 9); omega
          _ = (3 ^ y % 9 + 13 % 9) % 9 := Nat.add_mod _ _ _
          _ = 4 := by simp [h3y]
      rw [hleft] at hmod
      exact cube_mod9_ne_four z hmod.symm

private theorem solution_x_eq_four {y z : ℕ} (h : Solves 4 y z) : False := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 22 := by omega
    have hcube : z ^ 3 < 3 ^ 3 := by omega
    have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
    interval_cases z <;> omega
  · by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 24 := by omega
      have hcube : z ^ 3 < 3 ^ 3 := by omega
      have hz_bound : z < 3 := lt_of_pow_lt_pow_left' 3 hcube
      interval_cases z <;> omega
    · have hy2 : 2 ≤ y := by omega
      have h3y : 3 ^ y % 9 = 0 := by
        obtain ⟨k, rfl⟩ : ∃ k, y = k + 2 := ⟨y - 2, by omega⟩
        calc
          3 ^ (k + 2) % 9 = (3 ^ k * 9) % 9 := by rw [pow_add]; norm_num
          _ = 0 := Nat.mul_mod_left (3 ^ k) 9
      have hmod := congrArg (fun n : ℕ => n % 9) h
      have hleft : (2 ^ 4 + 3 ^ y + 5) % 9 = 3 := by
        calc
          (2 ^ 4 + 3 ^ y + 5) % 9 = (3 ^ y + 21) % 9 := by
            apply congrArg (fun n : ℕ => n % 9); omega
          _ = (3 ^ y % 9 + 21 % 9) % 9 := Nat.add_mod _ _ _
          _ = 3 := by simp [h3y]
      rw [hleft] at hmod
      exact cube_mod9_ne_three z hmod.symm

private theorem solution_x_eq_five {y z : ℕ} (h : Solves 5 y z) : y = 3 ∧ z = 4 := by
  unfold Solves at h
  by_cases hy0 : y = 0
  · subst y
    have hz : z ^ 3 = 38 := by omega
    have hcube : z ^ 3 < 4 ^ 3 := by omega
    have hz_bound : z < 4 := lt_of_pow_lt_pow_left' 3 hcube
    interval_cases z <;> omega
  · by_cases hy1 : y = 1
    · subst y
      have hz : z ^ 3 = 40 := by omega
      have hcube : z ^ 3 < 4 ^ 3 := by omega
      have hz_bound : z < 4 := lt_of_pow_lt_pow_left' 3 hcube
      interval_cases z <;> omega
    · by_cases hy2 : y = 2
      · subst y
        have hz : z ^ 3 = 46 := by omega
        have hcube : z ^ 3 < 4 ^ 3 := by omega
        have hz_bound : z < 4 := lt_of_pow_lt_pow_left' 3 hcube
        interval_cases z <;> omega
      · by_cases hy3 : y = 3
        · subst y
          have hz : z ^ 3 = 64 := by omega
          have hz4 : z = 4 := by
            have hcube : z ^ 3 < 5 ^ 3 := by omega
            have hz_bound : z < 5 := lt_of_pow_lt_pow_left' 3 hcube
            interval_cases z <;> omega
          exact ⟨rfl, hz4⟩
        · exfalso
          have hmod8 := congrArg (fun n : ℕ => n % 8) h
          have hy_odd : y % 2 = 1 := by
            have hy_mod_lt : y % 2 < 2 := Nat.mod_lt y (by norm_num)
            by_contra hne
            have hy_even : y % 2 = 0 := by omega
            have h3y8 : 3 ^ y % 8 = 1 := pow_three_mod8_of_even hy_even
            have hleft8 : (2 ^ 5 + 3 ^ y + 5) % 8 = 6 := by
              calc
                (2 ^ 5 + 3 ^ y + 5) % 8 = (3 ^ y + 37) % 8 := by
                  apply congrArg (fun n : ℕ => n % 8); omega
                _ = (3 ^ y % 8 + 37 % 8) % 8 := Nat.add_mod _ _ _
                _ = 6 := by simp [h3y8]
            rw [hleft8] at hmod8
            exact cube_mod8_ne_six z hmod8.symm
          have hy6_ne1 : y % 6 ≠ 1 := by
            intro hy6_eq1
            have h3y7 : 3 ^ y % 7 = 3 := pow_three_mod7_of_mod6_eq_one hy6_eq1
            have hmod7 := congrArg (fun n : ℕ => n % 7) h
            have hleft7 : (2 ^ 5 + 3 ^ y + 5) % 7 = 5 := by
              calc
                (2 ^ 5 + 3 ^ y + 5) % 7 = (3 ^ y + 37) % 7 := by
                  apply congrArg (fun n : ℕ => n % 7); omega
                _ = (3 ^ y % 7 + 37 % 7) % 7 := Nat.add_mod _ _ _
                _ = 5 := by simp [h3y7]
            rw [hleft7] at hmod7
            rcases cube_mod7_cases z with hz0 | hz1 | hz6 <;> omega
          have hy6_ne5 : y % 6 ≠ 5 := by
            intro hy6_eq5
            have h3y13 : 3 ^ y % 13 = 9 := pow_three_mod13_of_mod6_eq_five hy6_eq5
            have hmod13 := congrArg (fun n : ℕ => n % 13) h
            have hleft13 : (2 ^ 5 + 3 ^ y + 5) % 13 = 7 := by
              calc
                (2 ^ 5 + 3 ^ y + 5) % 13 = (3 ^ y + 37) % 13 := by
                  apply congrArg (fun n : ℕ => n % 13); omega
                _ = (3 ^ y % 13 + 37 % 13) % 13 := Nat.add_mod _ _ _
                _ = 7 := by simp [h3y13]
            rw [hleft13] at hmod13
            exact cube_mod13_ne_seven z hmod13.symm
          have hy6_eq3 : y % 6 = 3 := by
            have hy6_lt : y % 6 < 6 := Nat.mod_lt y (by norm_num)
            have hy6_odd : (y % 6) % 2 = 1 := by
              rw [Nat.mod_mod_of_dvd y (by norm_num : 2 ∣ 6)]
              exact hy_odd
            omega
          have hy_mod3 : 3 ∣ y := by
            apply Nat.dvd_of_mod_eq_zero
            calc
              y % 3 = (y % 6) % 3 :=
                (Nat.mod_mod_of_dvd y (by norm_num : 3 ∣ 6)).symm
              _ = 0 := by norm_num [hy6_eq3]
          obtain ⟨η, rfl⟩ := hy_mod3
          let t : ℕ := 3 ^ η
          have ht_cube : t ^ 3 = 3 ^ (3 * η) := by
            dsimp [t]
            rw [← Nat.pow_mul, mul_comm]
          have hsum : 37 + t ^ 3 = z ^ 3 := by rw [ht_cube]; omega
          have ht_lt_z : t < z := by
            apply lt_of_pow_lt_pow_left' 3
            omega
          let d : ℕ := z - t
          let q : ℕ := z ^ 2 + z * t + t ^ 2
          have hd_pos : 0 < d := by dsimp [d]; omega
          have hz_eq : z = d + t := by dsimp [d]; omega
          have hfactor : d * q + t ^ 3 = z ^ 3 := by
            calc
              d * q + t ^ 3 =
                  d * ((d + t) ^ 2 + (d + t) * t + t ^ 2) + t ^ 3 := by
                    simp [q, hz_eq]
              _ = (d + t) ^ 3 := by ring
              _ = z ^ 3 := by rw [← hz_eq]
          have hprod : d * q = 37 := by omega
          have hdvd : d ∣ 37 := ⟨q, hprod.symm⟩
          have hcases : d = 1 ∨ d = 37 := (Nat.dvd_prime (by norm_num)).mp hdvd
          rcases hcases with h_one | h_37
          · have hz_eq_t1 : z = t + 1 := by omega
            have hq37 : q = 37 := by simpa [h_one] using hprod
            have halgebra : 3 * (t * (t + 1)) + 1 = 37 := by
              calc
                3 * (t * (t + 1)) + 1 =
                    (t + 1) ^ 2 + (t + 1) * t + t ^ 2 := by ring
                _ = q := by simp [q, hz_eq_t1]
                _ = 37 := hq37
            have heta : t * (t + 1) = 12 := by omega
            have heta_lt2 : η < 2 := by
              by_contra hη
              have heta_ge2 : 2 ≤ η := by omega
              obtain ⟨k, hk⟩ : ∃ k, η = k + 2 := ⟨η - 2, by omega⟩
              have ht_ge9 : 9 ≤ t := by
                calc
                  9 = 1 * 9 := by norm_num
                  _ ≤ 3 ^ k * 9 := Nat.mul_le_mul_right 9 (by positivity)
                  _ = 3 ^ (k + 2) := by rw [pow_add]; norm_num
                  _ = t := by simp [t, hk]
              have hprod_ge90 : 90 ≤ t * (t + 1) :=
                Nat.mul_le_mul ht_ge9 (by omega)
              omega
            interval_cases η <;> omega
          · have hq1 : q = 1 := by rw [h_37] at hprod; omega
            have hz2 : 2 ≤ z := by omega
            have hzsq : 4 ≤ z ^ 2 := by nlinarith [Nat.mul_le_mul hz2 hz2]
            dsimp [q] at hq1
            omega

/-- The only solutions with `x < 6` are the two known solutions. -/
theorem classify_x_lt_six
    {x y z : ℕ}
    (hx : x < 6)
    (h : Solves x y z) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨
    (x = 5 ∧ y = 3 ∧ z = 4) := by
  interval_cases x
  · exact (solution_x_eq_zero h).elim
  · left; exact ⟨rfl, solution_x_eq_one h⟩
  · exact (solution_x_eq_two h).elim
  · exact (solution_x_eq_three h).elim
  · exact (solution_x_eq_four h).elim
  · right; exact ⟨rfl, solution_x_eq_five h⟩

end KuromineProof
