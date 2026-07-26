import KuromineProof.Modular

namespace KuromineProof

/-- Boolean test for whether `a` is a cube modulo `m`. -/
def isCubeModB (m a : ℕ) [NeZero m] : Bool :=
  (List.range m).any fun z => z ^ 3 % m == a % m

/-- A cube identity in `ZMod m` implies success of the Boolean cube test. -/
theorem isCubeModB_eq_true_of_zmod
    {m a : ℕ} [NeZero m] {z : ZMod m}
    (h : z ^ 3 = (a : ZMod m)) :
    isCubeModB m a = true := by
  unfold isCubeModB
  rw [List.any_eq_true]
  refine ⟨z.val, List.mem_range.mpr (ZMod.val_lt z), ?_⟩
  simp only [beq_iff_eq]
  apply nat_mod_eq_of_zmod_eq
  push_cast
  simpa only [ZMod.natCast_zmod_val] using h

/-- Convert a natural-number period certificate to `ZMod`. -/
theorem zmod_pow_eq_one_of_nat_mod_eq_one
    {a d m : ℕ} [NeZero m]
    (hm : 1 < m)
    (h : a ^ d % m = 1) :
    (a : ZMod m) ^ d = 1 := by
  have hcast :
      ((a ^ d : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
    rw [ZMod.natCast_eq_natCast_iff']
    simpa [Nat.mod_eq_of_lt hm] using h
  push_cast at hcast
  exact hcast

/-- A normalized pair of exponent congruence classes. -/
structure SieveResidueClass where
  xModulus : ℕ
  yModulus : ℕ
  xResidue : ℕ
  yResidue : ℕ
deriving DecidableEq, Repr

/-- Lift one congruence class to the least common multiples with new periods. -/
def refineClass (r : SieveResidueClass) (Px Py : ℕ) : List SieveResidueClass :=
  if Px == 0 || Py == 0 then [r] else
  let Mx' := Nat.lcm r.xModulus Px
  let My' := Nat.lcm r.yModulus Py
  let kxCount := Mx' / r.xModulus
  let kyCount := My' / r.yModulus
  (List.range kxCount).flatMap fun kx =>
    (List.range kyCount).map fun ky =>
      { xModulus := Mx'
        yModulus := My'
        xResidue := r.xResidue + kx * r.xModulus
        yResidue := r.yResidue + ky * r.yModulus }

/-- A residue class contains `(x,y)` when both congruences hold. -/
def SieveResidueClass.Matches (r : SieveResidueClass) (x y : ℕ) : Prop :=
  x % r.xModulus = r.xResidue ∧ y % r.yModulus = r.yResidue

/-- Normalization invariant for finite-sieve classes. -/
structure SieveResidueClass.WellFormed (r : SieveResidueClass) : Prop where
  xModulus_pos : 0 < r.xModulus
  yModulus_pos : 0 < r.yModulus
  xResidue_lt : r.xResidue < r.xModulus
  yResidue_lt : r.yResidue < r.yModulus

/-- One prime sieve stage, with certified periods for powers of 2 and 3. -/
structure PeriodicStage where
  prime : ℕ
  xPeriod : ℕ
  yPeriod : ℕ
deriving DecidableEq, Repr

/-- Mathematical validity of a prime sieve stage. -/
structure PeriodicStage.IsValid (s : PeriodicStage) : Prop where
  prime_prime : Nat.Prime s.prime
  prime_gt_three : 3 < s.prime
  xPeriod_pos : 0 < s.xPeriod
  yPeriod_pos : 0 < s.yPeriod
  two_period : 2 ^ s.xPeriod % s.prime = 1
  three_period : 3 ^ s.yPeriod % s.prime = 1

/-- Whether a refined residue class is locally compatible with a cube. -/
def PeriodicStage.allows (s : PeriodicStage) (r : SieveResidueClass) : Bool :=
  if hp : 0 < s.prime then
    letI : NeZero s.prime := ⟨hp.ne'⟩
    isCubeModB s.prime
      (2 ^ (r.xResidue % s.xPeriod) +
       3 ^ (r.yResidue % s.yPeriod) + 5)
  else
    false

/-- Refine all classes to the stage periods and discard inadmissible lifts. -/
def applyPeriodicStage
    (rs : List SieveResidueClass) (s : PeriodicStage) : List SieveResidueClass :=
  rs.flatMap fun r =>
    (refineClass r s.xPeriod s.yPeriod).filter fun r' => s.allows r'

/-- Run a finite list of prime sieve stages. -/
def runPeriodicSieve :
    List SieveResidueClass → List PeriodicStage → List SieveResidueClass
  | rs, [] => rs
  | rs, s :: ss => runPeriodicSieve (applyPeriodicStage rs s) ss

/-- A list of classes covers `(x,y)` if one normalized member contains it. -/
def CoveredBy (rs : List SieveResidueClass) (x y : ℕ) : Prop :=
  ∃ r ∈ rs, r.WellFormed ∧ r.Matches x y

end KuromineProof
