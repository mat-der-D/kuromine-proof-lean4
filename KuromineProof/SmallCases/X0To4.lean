import KuromineProof.SmallCases.Residues

namespace KuromineProof

/-- There are no solutions with `x < 5` and `y ≥ 3`. -/
theorem no_solution_x_lt_five_y_ge_three
    {x y z : ℕ}
    (hx : x < 5)
    (hy : 3 ≤ y)
    (h : Solves x y z) :
    False := by
  unfold Solves at h
  have hmod9 : (2 ^ x + 3 ^ y + 5) % 9 = (z ^ 3) % 9 :=
    congrArg (fun n : ℕ => n % 9) h
  have hx2 : x = 2 := by
    rcases cube_mod9_cases z with hz | hz | hz <;>
      rw [hz] at hmod9 <;>
      interval_cases x <;>
      norm_num [Nat.add_mod, pow_three_mod9_zero (by omega : 2 ≤ y)] at hmod9 <;>
      omega
  subst x
  have hmod27 : (2 ^ 2 + 3 ^ y + 5) % 27 = (z ^ 3) % 27 :=
    congrArg (fun n : ℕ => n % 27) h
  have hleft27 : (2 ^ 2 + 3 ^ y + 5) % 27 = 9 := by
    calc
      (2 ^ 2 + 3 ^ y + 5) % 27 = (3 ^ y + 9) % 27 := by
        apply congrArg (fun n : ℕ => n % 27)
        omega
      _ = (3 ^ y % 27 + 9 % 27) % 27 := Nat.add_mod _ _ _
      _ = 9 := by simp [pow_three_mod27_zero hy]
  rw [hleft27] at hmod27
  exact cube_mod27_ne_nine z hmod27.symm

end KuromineProof
