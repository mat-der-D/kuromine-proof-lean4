import KuromineProof.LargeCase
import KuromineProof.Sieve.Certificate
import KuromineProof.SmallCases

namespace KuromineProof

/-- Eliminate the remaining large-exponent range by combining the sieve
    congruences with the Jacobi-symbol argument. -/
theorem no_large_solution
    {x y z : ℕ}
    (hx6 : 6 ≤ x)
    (hy3 : 3 ≤ y)
    (hsol : Solves x y z) :
    False := by
  obtain ⟨hx4, hy48⟩ := congruences_of_large_solution hx6 hy3 hsol
  exact no_solution_of_congruences hx6 hx4 hy48 hsol

/-- Complete classification over nonnegative exponents and nonnegative `z`. -/
theorem classify_natural_solutions
    {x y z : ℕ}
    (hsol : Solves x y z) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨
    (x = 5 ∧ y = 3 ∧ z = 4) := by
  by_cases hsmall : x < 6 ∨ y < 3
  · exact classify_small_cases hsmall hsol
  · have hx6 : 6 ≤ x := by omega
    have hy3 : 3 ≤ y := by omega
    exact (no_large_solution hx6 hy3 hsol).elim

end KuromineProof
