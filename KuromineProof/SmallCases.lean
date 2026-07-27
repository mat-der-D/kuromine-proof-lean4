import KuromineProof.SmallCases.SmallY
import KuromineProof.SmallCases.X0To4
import KuromineProof.SmallCases.X5

namespace KuromineProof

/-- The only solutions with `x < 6` or `y < 3` are the two known solutions. -/
theorem classify_small_cases
    {x y z : ℕ}
    (hsmall : x < 6 ∨ y < 3)
    (h : Solves x y z) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨
    (x = 5 ∧ y = 3 ∧ z = 4) := by
  rcases hsmall with hx6 | hy3
  · by_cases hylt : y < 3
    · left
      exact classify_solution_y_lt_three hylt h
    · have hyge : 3 ≤ y := by omega
      by_cases hx5 : x = 5
      · subst x
        right
        exact ⟨rfl, classify_solution_x_eq_five h⟩
      · have hxlt : x < 5 := by omega
        exact (no_solution_x_lt_five_y_ge_three hxlt hyge h).elim
  · left
    exact classify_solution_y_lt_three hy3 h

/-- The only solutions with `x < 6` are the two known solutions. -/
theorem classify_x_lt_six
    {x y z : ℕ}
    (hx : x < 6)
    (h : Solves x y z) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨
    (x = 5 ∧ y = 3 ∧ z = 4) :=
  classify_small_cases (Or.inl hx) h

end KuromineProof
