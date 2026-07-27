import KuromineProof.Modular

namespace KuromineProof

theorem cube_mod4_ne_two (z : ℕ) : (z ^ 3) % 4 ≠ 2 := by
  rw [Nat.pow_mod z 3 4]
  have hr : z % 4 < 4 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 4 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod9_cases (z : ℕ) :
    (z ^ 3) % 9 = 0 ∨ (z ^ 3) % 9 = 1 ∨ (z ^ 3) % 9 = 8 := by
  rw [Nat.pow_mod z 3 9]
  have hr : z % 9 < 9 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 9 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod27_ne_nine (z : ℕ) : (z ^ 3) % 27 ≠ 9 := by
  rw [Nat.pow_mod z 3 27]
  have hr : z % 27 < 27 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 27 = r at hr ⊢
  interval_cases r <;> norm_num

theorem cube_mod13_ne_seven (z : ℕ) : (z ^ 3) % 13 ≠ 7 := by
  rw [Nat.pow_mod z 3 13]
  have hr : z % 13 < 13 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 13 = r at hr ⊢
  interval_cases r <;> norm_num

private theorem pow_mod_pow_eq_zero {a e n : ℕ} (h : e ≤ n) :
    a ^ n % a ^ e = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow a h)

theorem pow_two_mod4_zero {x : ℕ} (hx : 2 ≤ x) : 2 ^ x % 4 = 0 := by
  change 2 ^ x % 2 ^ 2 = 0
  exact pow_mod_pow_eq_zero hx

theorem pow_three_mod9_zero {y : ℕ} (hy : 2 ≤ y) : 3 ^ y % 9 = 0 := by
  change 3 ^ y % 3 ^ 2 = 0
  exact pow_mod_pow_eq_zero hy

theorem pow_three_mod27_zero {y : ℕ} (hy : 3 ≤ y) : 3 ^ y % 27 = 0 := by
  change 3 ^ y % 3 ^ 3 = 0
  exact pow_mod_pow_eq_zero hy

theorem pow_two_mod7 (x : ℕ) :
    2 ^ x % 7 = 1 ∨ 2 ^ x % 7 = 2 ∨ 2 ^ x % 7 = 4 := by
  have hxmod : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by
    have hlt : x % 3 < 3 := Nat.mod_lt x (by norm_num)
    omega
  rcases hxmod with hx | hx | hx
  · left
    calc
      2 ^ x % 7 = 2 ^ 0 % 7 :=
        nat_pow_mod_eq_of_period (a := 2) (d := 3) (m := 7) (by decide) hx
      _ = 1 := by norm_num
  · right; left
    calc
      2 ^ x % 7 = 2 ^ 1 % 7 :=
        nat_pow_mod_eq_of_period (a := 2) (d := 3) (m := 7) (by decide) hx
      _ = 2 := by norm_num
  · right; right
    calc
      2 ^ x % 7 = 2 ^ 2 % 7 :=
        nat_pow_mod_eq_of_period (a := 2) (d := 3) (m := 7) (by decide) hx
      _ = 4 := by norm_num

theorem cube_mod7_cases (z : ℕ) :
    (z ^ 3) % 7 = 0 ∨ (z ^ 3) % 7 = 1 ∨ (z ^ 3) % 7 = 6 := by
  rw [Nat.pow_mod z 3 7]
  have hr : z % 7 < 7 := Nat.mod_lt z (by norm_num)
  generalize hz : z % 7 = r at hr ⊢
  interval_cases r <;> norm_num

theorem pow_three_mod7_of_mod6_eq_one {y : ℕ} (hy : y % 6 = 1) :
    3 ^ y % 7 = 3 := by
  calc
    3 ^ y % 7 = 3 ^ 1 % 7 :=
      nat_pow_mod_eq_of_period (a := 3) (d := 6) (m := 7) (by decide) hy
    _ = 3 := by norm_num

theorem pow_three_mod13_of_mod6_eq_five {y : ℕ} (hy : y % 6 = 5) :
    3 ^ y % 13 = 9 := by
  calc
    3 ^ y % 13 = 3 ^ 5 % 13 :=
      nat_pow_mod_eq_of_period (a := 3) (d := 6) (m := 13) (by decide) hy
    _ = 9 := by norm_num

end KuromineProof
