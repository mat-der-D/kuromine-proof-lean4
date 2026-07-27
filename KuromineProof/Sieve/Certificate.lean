import KuromineProof.Sieve.Initial

namespace KuromineProof

/-- The eight prime stages used in the simplified human-readable proof. -/
def sieveStages : List PeriodicStage :=
  [ { prime := 73, xPeriod := 9, yPeriod := 12 },
    { prime := 13, xPeriod := 12, yPeriod := 3 },
    { prime := 577, xPeriod := 144, yPeriod := 48 },
    { prime := 97, xPeriod := 48, yPeriod := 48 },
    { prime := 673, xPeriod := 48, yPeriod := 168 },
    { prime := 337, xPeriod := 21, yPeriod := 168 },
    { prime := 43, xPeriod := 14, yPeriod := 42 },
    { prime := 1009, xPeriod := 504, yPeriod := 168 } ]

section SieveValidity

set_option exponentiation.threshold 1000

/-- Each concrete stage has the stated prime and exponent periods. -/
private theorem sieveStages_valid : ∀ s ∈ sieveStages, s.IsValid := by
  intro s hs
  simp [sieveStages] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> norm_num

end SieveValidity

/-- The three residue classes left by the eight-stage certificate. -/
def finalClasses : List SieveResidueClass :=
  [ { xModulus := 1008, yModulus := 336, xResidue := 5, yResidue := 45 },
    { xModulus := 1008, yModulus := 336, xResidue := 725, yResidue := 45 },
    { xModulus := 1008, yModulus := 336, xResidue := 5, yResidue := 333 } ]

section SieveComputation

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

/-- Closed finite computation of the simplified sieve. -/
private theorem sieve_computation :
    runPeriodicSieve initialClasses sieveStages = finalClasses := by
  native_decide

end SieveComputation

/-- Every large solution satisfies the two congruences needed by the Jacobi argument. -/
theorem congruences_of_large_solution
    {x y z : ℕ}
    (hx6 : 6 ≤ x)
    (hy3 : 3 ≤ y)
    (hsol : Solves x y z) :
    x % 4 = 1 ∧ y % 48 = 45 := by
  have hcov0 : CoveredBy initialClasses x y :=
    initialClasses_cover hx6 hy3 hsol
  have hcov : CoveredBy (runPeriodicSieve initialClasses sieveStages) x y :=
    runPeriodicSieve_sound sieveStages_valid hsol hcov0
  rw [sieve_computation] at hcov
  rcases hcov with ⟨r, hrmem, _hrwf, hrmatch⟩
  simp [finalClasses] at hrmem
  rcases hrmem with rfl | rfl | rfl <;>
    exact ⟨
      (mod_eq_of_mod_eq_of_dvd (by norm_num : 4 ∣ 1008) hrmatch.1).trans (by norm_num),
      (mod_eq_of_mod_eq_of_dvd (by norm_num : 48 ∣ 336) hrmatch.2).trans (by norm_num)⟩

end KuromineProof
