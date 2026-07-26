import KuromineProof.Main

namespace KuromineProof

/-- The Kuromine equation with integer exponents, interpreted in `ℚ`. -/
def SolvesInteger (x y z : ℤ) : Prop :=
  (2 : ℚ) ^ x + (3 : ℚ) ^ y + 5 = (z : ℚ) ^ (3 : ℕ)

example (a y : ℕ) (z : ℤ)
    (h : SolvesInteger (Int.negSucc a) (Int.ofNat y) z) : False := by
  unfold SolvesInteger at h
  simp at h
  trace_state
  sorry

end KuromineProof
