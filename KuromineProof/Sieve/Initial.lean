import KuromineProof.Sieve.Soundness

namespace KuromineProof

/-- Initial residue pairs forced by the elementary mod-9 and mod-64 tests. -/
def initialPairs : List (ℕ × ℕ) :=
  [(2,1), (2,5), (2,9), (2,11), (2,13),
   (5,1), (5,5), (5,9), (5,11), (5,13)]

/-- Initial normalized classes modulo `(6,16)`. -/
def initialClasses : List SieveResidueClass :=
  initialPairs.map fun q =>
    { xModulus := 6, yModulus := 16, xResidue := q.1, yResidue := q.2 }

/-- Finite verification of the ten initial residue pairs. -/
theorem initialPairs_complete :
    ∀ rx : Fin 6, ∀ ry : Fin 16,
      isCubeModB 9 (2 ^ rx.val + 5) = true →
      isCubeModB 64 (3 ^ ry.val + 5) = true →
      (rx.val, ry.val) ∈ initialPairs := by
  intro rx ry
  fin_cases rx <;> fin_cases ry <;> decide

/-- Every solution with `x ≥ 6` and `y ≥ 3` is covered by the initial classes. -/
theorem initialClasses_cover
    {x y z : ℕ}
    (hx : 6 ≤ x) (hy : 3 ≤ y)
    (hsol : Solves x y z) :
    CoveredBy initialClasses x y := by
  let rx : Fin 6 := ⟨x % 6, Nat.mod_lt _ (by norm_num)⟩
  let ry : Fin 16 := ⟨y % 16, Nat.mod_lt _ (by norm_num)⟩
  have h9 : isCubeModB 9 (2 ^ rx.val + 5) = true := by
    apply isCubeModB_eq_true_of_zmod (z := (z : ZMod 9))
    have h3zero : (3 : ZMod 9) ^ y = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, y = k + 2 := ⟨y - 2, by omega⟩
      rw [pow_add]
      have h32 : (3 : ZMod 9) ^ 2 = 0 := by decide
      rw [h32, mul_zero]
    have h2period : (2 : ZMod 9) ^ 6 = 1 := by decide
    have h2reduce : (2 : ZMod 9) ^ x = (2 : ZMod 9) ^ rx.val := by
      dsimp [rx]
      exact zmod_pow_mod_eq 2 6 9 h2period x
    simpa [h2reduce, h3zero] using
      (zmod_equation_of_solution (m := 9) hsol)
  have h64 : isCubeModB 64 (3 ^ ry.val + 5) = true := by
    apply isCubeModB_eq_true_of_zmod (z := (z : ZMod 64))
    have h2zero : (2 : ZMod 64) ^ x = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, x = k + 6 := ⟨x - 6, by omega⟩
      rw [pow_add]
      have h26 : (2 : ZMod 64) ^ 6 = 0 := by decide
      rw [h26, mul_zero]
    have h3period : (3 : ZMod 64) ^ 16 = 1 := by decide
    have h3reduce : (3 : ZMod 64) ^ y = (3 : ZMod 64) ^ ry.val := by
      dsimp [ry]
      exact zmod_pow_mod_eq 3 16 64 h3period y
    simpa [h2zero, h3reduce] using
      (zmod_equation_of_solution (m := 64) hsol)
  have hpair : (rx.val, ry.val) ∈ initialPairs :=
    initialPairs_complete rx ry h9 h64
  let r : SieveResidueClass :=
    { xModulus := 6, yModulus := 16, xResidue := rx.val, yResidue := ry.val }
  refine ⟨r, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨(rx.val, ry.val), hpair, rfl⟩
  · exact
      { xModulus_pos := by norm_num
        yModulus_pos := by norm_num
        xResidue_lt := Nat.mod_lt _ (by norm_num)
        yResidue_lt := Nat.mod_lt _ (by norm_num) }
  · exact ⟨rfl, rfl⟩

end KuromineProof
