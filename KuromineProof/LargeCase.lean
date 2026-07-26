import KuromineProof.Modular
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace KuromineProof

/-- If `y = 3η`, every solution satisfies `3^η < z`. -/
theorem three_pow_lt_z_of_solution
    {x y z η : ℕ}
    (hy : y = 3 * η)
    (hsol : Solves x y z) :
    3 ^ η < z := by
  subst y
  unfold Solves at hsol
  have ht_cube : (3 ^ η) ^ 3 < z ^ 3 := by
    have h2pos : 0 < 2 ^ x := by positivity
    calc
      (3 ^ η) ^ 3 = 3 ^ (3 * η) := by rw [← Nat.pow_mul, mul_comm]
      _ < 2 ^ x + 3 ^ (3 * η) + 5 := by omega
      _ = z ^ 3 := hsol
  exact lt_of_pow_lt_pow_left' 3 ht_cube

/-- From `y ≡ 45 (mod 48)` and `y = 3η`, obtain `η ≡ 3 (mod 4)`. -/
theorem eta_mod_four
    {y η : ℕ}
    (hy : y = 3 * η)
    (hy48 : y % 48 = 45) :
    η % 4 = 3 := by
  omega

private theorem five_dvd_z_of_congruences
    {x y z η : ℕ}
    (hx4 : x % 4 = 1)
    (hy48 : y % 48 = 45)
    (hy : y = 3 * η)
    (hsol : Solves x y z) :
    5 ∣ z := by
  subst y
  unfold Solves at hsol
  have hy4 : (3 * η) % 4 = 1 := by omega
  have h2x5 : 2 ^ x % 5 = 2 := by
    calc
      2 ^ x % 5 = 2 ^ 1 % 5 :=
        nat_pow_mod_eq_of_period (a := 2) (d := 4) (m := 5)
          (by decide) hx4
      _ = 2 := by norm_num
  have h3y5 : 3 ^ (3 * η) % 5 = 3 := by
    calc
      3 ^ (3 * η) % 5 = 3 ^ 1 % 5 :=
        nat_pow_mod_eq_of_period (a := 3) (d := 4) (m := 5)
          (by decide) hy4
      _ = 3 := by norm_num
  have hz_mod5 : z ^ 3 % 5 = 0 := by
    calc
      z ^ 3 % 5 = (2 ^ x + 3 ^ (3 * η) + 5) % 5 := by rw [← hsol]
      _ = 0 := by
        rw [Nat.add_mod (2 ^ x + 3 ^ (3 * η)), Nat.add_mod (2 ^ x), h2x5, h3y5]
  have hcube : 5 ∣ z ^ 3 := Nat.dvd_of_mod_eq_zero hz_mod5
  exact Nat.Prime.dvd_of_dvd_pow (by norm_num) hcube

private theorem z_mod_eight_of_congruences
    {x y z η : ℕ}
    (hx6 : 6 ≤ x)
    (hy48 : y % 48 = 45)
    (hy : y = 3 * η)
    (hsol : Solves x y z) :
    z % 8 = 6 := by
  subst y
  unfold Solves at hsol
  have hy16 : (3 * η) % 16 = 13 := by omega
  have h3y64 : 3 ^ (3 * η) % 64 = 19 := by
    calc
      3 ^ (3 * η) % 64 = 3 ^ 13 % 64 :=
        nat_pow_mod_eq_of_period (a := 3) (d := 16) (m := 64)
          (by decide) hy16
      _ = 19 := by norm_num
  have h2x64 : 2 ^ x % 64 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    simpa using Nat.pow_dvd_pow 2 hx6
  have hz3_mod64 : z ^ 3 % 64 = 24 := by
    calc
      z ^ 3 % 64 = (2 ^ x + 3 ^ (3 * η) + 5) % 64 := by rw [← hsol]
      _ = 24 := by
        rw [Nat.add_mod (2 ^ x + 3 ^ (3 * η)), Nat.add_mod (2 ^ x), h2x64, h3y64]
  have hrem : (z % 64) ^ 3 % 64 = 24 := by
    simpa [Nat.pow_mod] using hz3_mod64
  have hr : z % 64 < 64 := Nat.mod_lt z (by norm_num)
  generalize hz_r : z % 64 = r at hr hrem
  rw [← Nat.mod_mod_of_dvd z (by norm_num : 8 ∣ 64), hz_r]
  interval_cases r <;> (try rfl) <;> (revert hrem; norm_num)

/-- Under the two congruence conditions used in the human-readable proof,
    every large solution satisfies `z ≡ 30 (mod 40)`. -/
theorem z_mod_forty
    {x y z η : ℕ}
    (hx6 : 6 ≤ x)
    (hx4 : x % 4 = 1)
    (hy48 : y % 48 = 45)
    (hy : y = 3 * η)
    (hsol : Solves x y z) :
    z % 40 = 30 := by
  have hz_div5 : 5 ∣ z :=
    five_dvd_z_of_congruences hx4 hy48 hy hsol
  have hz_mod8 : z % 8 = 6 :=
    z_mod_eight_of_congruences hx6 hy48 hy hsol
  have hz_rem : z % 40 < 40 := Nat.mod_lt z (by norm_num)
  generalize hz_r : z % 40 = r at hz_rem
  have hz5_r : r % 5 = 0 := by
    rw [← hz_r, Nat.mod_mod_of_dvd z (by norm_num : 5 ∣ 40)]
    exact Nat.mod_eq_zero_of_dvd hz_div5
  have hz8_r : r % 8 = 6 := by
    rw [← hz_r, Nat.mod_mod_of_dvd z (by norm_num : 8 ∣ 40)]
    exact hz_mod8
  interval_cases r <;> revert hz5_r hz8_r <;> norm_num

/-- For `A = z - 3^η`, the congruence conditions imply `A ≡ 3 (mod 40)`. -/
theorem A_mod_forty
    {x y z η : ℕ}
    (hx6 : 6 ≤ x)
    (hx4 : x % 4 = 1)
    (hy48 : y % 48 = 45)
    (hy : y = 3 * η)
    (hsol : Solves x y z) :
    (z - 3 ^ η) % 40 = 3 := by
  have hz40 : z % 40 = 30 := z_mod_forty hx6 hx4 hy48 hy hsol
  have hη4 : η % 4 = 3 := eta_mod_four hy hy48
  have ht40 : 3 ^ η % 40 = 27 := by
    calc
      3 ^ η % 40 = 3 ^ 3 % 40 :=
        nat_pow_mod_eq_of_period (a := 3) (d := 4) (m := 40)
          (by decide) hη4
      _ = 27 := by norm_num
  have htz : 3 ^ η < z := three_pow_lt_z_of_solution hy hsol
  omega

/-- The factor `A = z - 3^η` divides `2^x + 5`. -/
theorem A_dvd_two_pow_add_five
    {x y z η : ℕ}
    (hy : y = 3 * η)
    (hsol : Solves x y z) :
    z - 3 ^ η ∣ 2 ^ x + 5 := by
  subst y
  have htz : 3 ^ η < z := three_pow_lt_z_of_solution rfl hsol
  unfold Solves at hsol
  have h_eq : z ^ 3 - (3 ^ η) ^ 3 = 2 ^ x + 5 := by
    have ht3 : (3 ^ η) ^ 3 = 3 ^ (3 * η) := by
      rw [← Nat.pow_mul, mul_comm]
    have h1 :
        z ^ 3 - (3 ^ η) ^ 3 =
          (2 ^ x + 5 + 3 ^ (3 * η)) - 3 ^ (3 * η) := by
      calc
        z ^ 3 - (3 ^ η) ^ 3 = z ^ 3 - 3 ^ (3 * η) := by rw [ht3]
        _ = (2 ^ x + 3 ^ (3 * η) + 5) - 3 ^ (3 * η) := by rw [← hsol]
        _ = (2 ^ x + 5 + 3 ^ (3 * η)) - 3 ^ (3 * η) := by omega
    have h2 :
        (2 ^ x + 5 + 3 ^ (3 * η)) - 3 ^ (3 * η) = 2 ^ x + 5 :=
      Nat.add_sub_cancel (2 ^ x + 5) (3 ^ (3 * η))
    exact h1.trans h2
  have h_factor :
      (z : ℤ) ^ 3 - (3 ^ η : ℤ) ^ 3 =
        ((z : ℤ) - (3 ^ η : ℤ)) *
          ((z : ℤ) ^ 2 + (z : ℤ) * (3 ^ η : ℤ) + (3 ^ η : ℤ) ^ 2) := by
    ring
  have h_prod :
      (z - 3 ^ η) * (z ^ 2 + z * 3 ^ η + (3 ^ η) ^ 2) = 2 ^ x + 5 := by
    zify [htz.le]
    have h_eq_z :
        (z : ℤ) ^ 3 - (3 ^ η : ℤ) ^ 3 = (2 ^ x + 5 : ℤ) := by
      have hle : (3 ^ η) ^ 3 ≤ z ^ 3 := by
        exact Nat.pow_le_pow_left htz.le 3
      zify [hle] at h_eq
      exact h_eq
    linear_combination h_factor + h_eq_z
  exact ⟨z ^ 2 + z * 3 ^ η + (3 ^ η) ^ 2, h_prod.symm⟩

/-- If `x` is odd and `A ∣ 2^x + 5`, then `-10` is a square modulo `A`. -/
theorem neg_ten_isSquare_of_odd
    {A x : ℕ}
    (_hA : A ≠ 0)
    (hx : Odd x)
    (hdiv : A ∣ 2 ^ x + 5) :
    IsSquare ((-10 : ℤ) : ZMod A) := by
  obtain ⟨k, rfl⟩ := hx
  refine ⟨(2 : ZMod A) ^ (k + 1), ?_⟩
  rw [← pow_two]
  have hzero : ((2 ^ (2 * k + 1) + 5 : ℕ) : ZMod A) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod A) A]
    exact hdiv
  have hbase : (2 : ZMod A) ^ (2 * k + 1) = -5 := by
    have hzero' : (2 : ZMod A) ^ (2 * k + 1) + 5 = 0 := by
      simpa using hzero
    linear_combination hzero'
  have hsq :
      ((2 : ZMod A) ^ (k + 1)) ^ 2 =
        (2 : ZMod A) * (2 : ZMod A) ^ (2 * k + 1) := by
    calc
      ((2 : ZMod A) ^ (k + 1)) ^ 2 = (2 : ZMod A) ^ ((k + 1) * 2) := by
        rw [← pow_mul]
      _ = (2 : ZMod A) ^ (1 + (2 * k + 1)) := by congr 1 <;> omega
      _ = (2 : ZMod A) * (2 : ZMod A) ^ (2 * k + 1) := by
        rw [pow_add, pow_one]
  rw [hsq, hbase]
  norm_num

/-- The Jacobi symbol `(-10 / A)` is `-1` whenever `A ≡ 3 (mod 40)`. -/
theorem jacobi_neg_ten_eq_neg_one
    {A : ℕ}
    (hAmod40 : A % 40 = 3) :
    jacobiSym (-10) A = -1 := by
  have hAodd : Odd A := by
    rw [Nat.odd_iff]
    omega
  calc
    jacobiSym (-10) A = jacobiSym (-10) (A % 40) := by
      simpa using jacobiSym.mod_right (-10) hAodd
    _ = jacobiSym (-10) 3 := by rw [hAmod40]
    _ = -1 := by norm_num

/-- The large-exponent part of the human-readable proof. -/
theorem no_solution_of_congruences
    {x y z : ℕ}
    (hx6 : 6 ≤ x)
    (hx4 : x % 4 = 1)
    (hy48 : y % 48 = 45)
    (hsol : Solves x y z) :
    False := by
  obtain ⟨η, hy⟩ : ∃ η : ℕ, y = 3 * η := by
    refine ⟨y / 3, ?_⟩
    omega
  let A := z - 3 ^ η
  have htz : 3 ^ η < z := three_pow_lt_z_of_solution hy hsol
  have hAmod : A % 40 = 3 := by
    dsimp [A]
    exact A_mod_forty hx6 hx4 hy48 hy hsol
  have hA_ne : A ≠ 0 := by
    dsimp [A]
    omega
  have hA_dvd : A ∣ 2 ^ x + 5 := by
    dsimp [A]
    exact A_dvd_two_pow_add_five hy hsol
  have hxodd : Odd x := by
    rw [Nat.odd_iff]
    omega
  have hsquare : IsSquare ((-10 : ℤ) : ZMod A) :=
    neg_ten_isSquare_of_odd hA_ne hxodd hA_dvd
  have hjacobi : jacobiSym (-10) A = -1 :=
    jacobi_neg_ten_eq_neg_one hAmod
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one hjacobi hsquare

end KuromineProof
