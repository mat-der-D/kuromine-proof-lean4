import Mathlib

namespace KuromineProof

/-- The Kuromine equation over nonnegative integers. -/
def Solves (x y z : ℕ) : Prop :=
  2 ^ x + 3 ^ y + 5 = z ^ 3

/-- The first known solution. -/
theorem solves_102 : Solves 1 0 2 := by
  rfl

/-- The second known solution. -/
theorem solves_534 : Solves 5 3 4 := by
  rfl

end KuromineProof
