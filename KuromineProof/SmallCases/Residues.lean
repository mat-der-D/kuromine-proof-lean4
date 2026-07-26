import KuromineProof.Basic

namespace KuromineProof

theorem cube_mod4_ne_two (z : ℕ) : (z ^ 3) % 4 ≠ 2 := by
  rw [Nat.pow_mod z 3 4]
  have hr : z % 4 < 4 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 4 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod8_ne_six (z : ℕ) : (z ^ 3) % 8 ≠ 6 := by
  rw [Nat.pow_mod z 3 8]
  have hr : z % 8 < 8 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 8 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod9_ne_three (z : ℕ) : (z ^ 3) % 9 ≠ 3 := by
  rw [Nat.pow_mod z 3 9]
  have hr : z % 9 < 9 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 9 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod9_ne_four (z : ℕ) : (z ^ 3) % 9 ≠ 4 := by
  rw [Nat.pow_mod z 3 9]
  have hr : z % 9 < 9 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 9 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod9_ne_seven (z : ℕ) : (z ^ 3) % 9 ≠ 7 := by
  rw [Nat.pow_mod z 3 9]
  have hr : z % 9 < 9 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 9 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod27_ne_six (z : ℕ) : (z ^ 3) % 27 ≠ 6 := by
  rw [Nat.pow_mod z 3 27]
  have hr : z % 27 < 27 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 27 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod27_ne_nine (z : ℕ) : (z ^ 3) % 27 ≠ 9 := by
  rw [Nat.pow_mod z 3 27]
  have hr : z % 27 < 27 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 27 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod27_ne_eighteen (z : ℕ) : (z ^ 3) % 27 ≠ 18 := by
  rw [Nat.pow_mod z 3 27]
  have hr : z % 27 < 27 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 27 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod13_ne_seven (z : ℕ) : (z ^ 3) % 13 ≠ 7 := by
  rw [Nat.pow_mod z 3 13]
  have hr : z % 13 < 13 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 13 = r at hr ⊢
  interval_cases r <;> norm_num

theorem pow_two_mod4_zero {x : ℕ} (hx : 2 ≤ x) : 2 ^ x % 4 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = k + 2 := ⟨x - 2, by omega⟩
  calc
    2 ^ (k + 2) % 4 = (2 ^ k * 4) % 4 := by rw [pow_add]; norm_num
    _ = 0 := Nat.mul_mod_left (2 ^ k) 4

theorem pow_two_mod8_zero {x : ℕ} (hx : 3 ≤ x) : 2 ^ x % 8 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = k + 3 := ⟨x - 3, by omega⟩
  calc
    2 ^ (k + 3) % 8 = (2 ^ k * 8) % 8 := by rw [pow_add]; norm_num
    _ = 0 := Nat.mul_mod_left (2 ^ k) 8

theorem pow_three_mod9_zero {y : ℕ} (hy : 2 ≤ y) : 3 ^ y % 9 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, y = k + 2 := ⟨y - 2, by omega⟩
  calc
    3 ^ (k + 2) % 9 = (3 ^ k * 9) % 9 := by rw [pow_add]; norm_num
    _ = 0 := Nat.mul_mod_left (3 ^ k) 9

theorem pow_three_mod27_zero {y : ℕ} (hy : 3 ≤ y) : 3 ^ y % 27 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, y = k + 3 := ⟨y - 3, by omega⟩
  calc
    3 ^ (k + 3) % 27 = (3 ^ k * 27) % 27 := by rw [pow_add]; norm_num
    _ = 0 := Nat.mul_mod_left (3 ^ k) 27

theorem pow_two_mod7 (x : ℕ) :
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

theorem cube_mod7_cases (z : ℕ) :
    (z ^ 3) % 7 = 0 ∨ (z ^ 3) % 7 = 1 ∨ (z ^ 3) % 7 = 6 := by
  rw [Nat.pow_mod z 3 7]
  have hr : z % 7 < 7 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 7 = r at hr ⊢
  interval_cases r <;> norm_num

theorem pow_three_mod8_of_even {y : ℕ} (hy : y % 2 = 0) : 3 ^ y % 8 = 1 := by
  have hdiv : y = 2 * (y / 2) := by
    have h := (Nat.div_add_mod y 2).symm
    omega
  have hp := congrArg (fun n : ℕ => 3 ^ n % 8) hdiv
  calc
    3 ^ y % 8 = 3 ^ (2 * (y / 2)) % 8 := hp
    _ = (3 ^ 2) ^ (y / 2) % 8 := by rw [pow_mul]
    _ = ((3 ^ 2 % 8) ^ (y / 2)) % 8 := Nat.pow_mod _ _ _
    _ = 1 := by norm_num

theorem pow_three_mod7_of_mod6_eq_one {y : ℕ} (hy : y % 6 = 1) :
    3 ^ y % 7 = 3 := by
  have hdiv : y = 6 * (y / 6) + 1 := by
    have h := (Nat.div_add_mod y 6).symm
    omega
  have hp := congrArg (fun n : ℕ => 3 ^ n % 7) hdiv
  calc
    3 ^ y % 7 = 3 ^ (6 * (y / 6) + 1) % 7 := hp
    _ = ((3 ^ 6) ^ (y / 6) * 3) % 7 := by rw [pow_add, pow_mul]; norm_num
    _ = (((3 ^ 6) ^ (y / 6) % 7) * (3 % 7)) % 7 := Nat.mul_mod _ _ _
    _ = 3 := by rw [Nat.pow_mod]; norm_num

theorem pow_three_mod13_of_mod6_eq_five {y : ℕ} (hy : y % 6 = 5) :
    3 ^ y % 13 = 9 := by
  have hdiv : y = 6 * (y / 6) + 5 := by
    have h := (Nat.div_add_mod y 6).symm
    omega
  have hp := congrArg (fun n : ℕ => 3 ^ n % 13) hdiv
  calc
    3 ^ y % 13 = 3 ^ (6 * (y / 6) + 5) % 13 := hp
    _ = ((3 ^ 6) ^ (y / 6) * 3 ^ 5) % 13 := by rw [pow_add, pow_mul]
    _ = (((3 ^ 6) ^ (y / 6) % 13) * (3 ^ 5 % 13)) % 13 := Nat.mul_mod _ _ _
    _ = 9 := by rw [Nat.pow_mod]; norm_num

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
