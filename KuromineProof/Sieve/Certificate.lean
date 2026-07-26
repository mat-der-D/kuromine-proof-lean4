import KuromineProof.Sieve.Core
import KuromineProof.LargeCase

namespace KuromineProof

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

/-- The eight prime stages used in the simplified human-readable proof. -/
def sieveStages : List PeriodicStage :=
  [⟨73, 9, 12⟩,
   ⟨13, 12, 3⟩,
   ⟨577, 144, 48⟩,
   ⟨97, 48, 48⟩,
   ⟨673, 48, 168⟩,
   ⟨337, 21, 168⟩,
   ⟨43, 14, 42⟩,
   ⟨1009, 504, 168⟩]

/-- Each concrete stage has the stated prime and exponent periods. -/
theorem sieveStages_valid : ∀ s ∈ sieveStages, s.IsValid := by
  intro s hs
  simp [sieveStages] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [PeriodicStage.IsValid] <;> norm_num

/-- The three residue classes left by the eight-stage certificate. -/
def finalClasses : List SieveResidueClass :=
  [⟨1008, 336, 5, 45⟩,
   ⟨1008, 336, 725, 45⟩,
   ⟨1008, 336, 5, 333⟩]

/-- Closed finite computation of the simplified sieve. -/
theorem sieve_computation :
    runPeriodicSieve initialClasses sieveStages = finalClasses := by
  native_decide

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
  rcases hrmem with rfl | rfl | rfl <;> constructor
  · exact (mod_eq_of_mod_eq_of_dvd (by norm_num : 4 ∣ 1008) hrmatch.1).trans (by norm_num)
  · exact (mod_eq_of_mod_eq_of_dvd (by norm_num : 48 ∣ 336) hrmatch.2).trans (by norm_num)
  · exact (mod_eq_of_mod_eq_of_dvd (by norm_num : 4 ∣ 1008) hrmatch.1).trans (by norm_num)
  · exact (mod_eq_of_mod_eq_of_dvd (by norm_num : 48 ∣ 336) hrmatch.2).trans (by norm_num)
  · exact (mod_eq_of_mod_eq_of_dvd (by norm_num : 4 ∣ 1008) hrmatch.1).trans (by norm_num)
  · exact (mod_eq_of_mod_eq_of_dvd (by norm_num : 48 ∣ 336) hrmatch.2).trans (by norm_num)

/-- No solution exists in the remaining large-exponent range. -/
theorem no_solution_large_exponents
    {x y z : ℕ}
    (hx6 : 6 ≤ x)
    (hy3 : 3 ≤ y)
    (hsol : Solves x y z) :
    False := by
  rcases congruences_of_large_solution hx6 hy3 hsol with ⟨hx4, hy48⟩
  exact no_solution_of_congruences hx6 hx4 hy48 hsol

end KuromineProof
