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

end KuromineProof
