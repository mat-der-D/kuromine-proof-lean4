import KuromineProof.SmallCases
import KuromineProof.Sieve.Certificate

namespace KuromineProof

/-- Public large-exponent elimination theorem. -/
theorem no_large_solution
    {x y z : ℕ}
    (hx6 : 6 ≤ x)
    (hy3 : 3 ≤ y)
    (hsol : Solves x y z) :
    False :=
  no_solution_large_exponents hx6 hy3 hsol

/-- Complete classification over nonnegative exponents and nonnegative `z`. -/
theorem classify_natural_solutions
    {x y z : ℕ}
    (hsol : Solves x y z) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨
    (x = 5 ∧ y = 3 ∧ z = 4) := by
  by_cases hx : x < 6
  · exact classify_x_lt_six hx hsol
  · have hx6 : 6 ≤ x := by omega
    by_cases hy : 3 ≤ y
    · exact (no_large_solution hx6 hy hsol).elim
    · have hylt : y < 3 := by omega
      interval_cases y
      · exact (no_solution_y0_x_ge_2 (by omega) hsol).elim
      · exact (no_solution_y1 hsol).elim
      · exact (no_solution_y2_x_ge_3 (by omega) hsol).elim

end KuromineProof
