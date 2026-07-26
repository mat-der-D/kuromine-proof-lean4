import KuromineProof.LargeCase

namespace KuromineProof

/-- Public form of the large-exponent elimination theorem. -/
theorem no_large_solution
    {x y z : ℕ}
    (hx6 : 6 ≤ x)
    (hx4 : x % 4 = 1)
    (hy48 : y % 48 = 45)
    (hsol : Solves x y z) :
    False :=
  no_solution_of_congruences hx6 hx4 hy48 hsol

end KuromineProof
