import KuromineProof.SmallCases.X0To4
import KuromineProof.SmallCases.X5

namespace KuromineProof

/-- The only solutions with `x < 6` are the two known solutions. -/
theorem classify_x_lt_six
    {x y z : ℕ}
    (hx : x < 6)
    (h : Solves x y z) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨
    (x = 5 ∧ y = 3 ∧ z = 4) := by
  interval_cases x
  · exact (solution_x_eq_zero h).elim
  · left
    exact ⟨rfl, solution_x_eq_one h⟩
  · exact (solution_x_eq_two h).elim
  · exact (solution_x_eq_three h).elim
  · exact (solution_x_eq_four h).elim
  · right
    exact ⟨rfl, solution_x_eq_five h⟩

end KuromineProof
