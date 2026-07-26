import KuromineProof.Modular

namespace KuromineProof

/-- Boolean test for whether `a` is a cube modulo `m`. -/
def isCubeModB (m a : ℕ) [NeZero m] : Bool :=
  (List.range m).any fun z => z ^ 3 % m == a % m

/-- A cube identity in `ZMod m` implies success of the Boolean cube test. -/
private theorem isCubeModB_eq_true_of_zmod
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
private theorem zmod_pow_eq_one_of_nat_mod_eq_one
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
def SieveResidueClass.WellFormed (r : SieveResidueClass) : Prop :=
  0 < r.xModulus ∧ 0 < r.yModulus ∧
  r.xResidue < r.xModulus ∧ r.yResidue < r.yModulus

/-- The `x`-modulus of a normalized residue class is positive. -/
theorem SieveResidueClass.WellFormed.xModulus_pos
    {r : SieveResidueClass} (h : r.WellFormed) :
    0 < r.xModulus :=
  h.1

/-- The `y`-modulus of a normalized residue class is positive. -/
theorem SieveResidueClass.WellFormed.yModulus_pos
    {r : SieveResidueClass} (h : r.WellFormed) :
    0 < r.yModulus :=
  h.2.1

/-- The `x`-residue lies in its normalized range. -/
theorem SieveResidueClass.WellFormed.xResidue_lt
    {r : SieveResidueClass} (h : r.WellFormed) :
    r.xResidue < r.xModulus :=
  h.2.2.1

/-- The `y`-residue lies in its normalized range. -/
theorem SieveResidueClass.WellFormed.yResidue_lt
    {r : SieveResidueClass} (h : r.WellFormed) :
    r.yResidue < r.yModulus :=
  h.2.2.2

/-- One prime sieve stage, with certified periods for powers of 2 and 3. -/
structure PeriodicStage where
  prime : ℕ
  xPeriod : ℕ
  yPeriod : ℕ
deriving DecidableEq, Repr

/-- Mathematical validity of a prime sieve stage. -/
def PeriodicStage.IsValid (s : PeriodicStage) : Prop :=
  Nat.Prime s.prime ∧ 3 < s.prime ∧
  0 < s.xPeriod ∧ 0 < s.yPeriod ∧
  2 ^ s.xPeriod % s.prime = 1 ∧
  3 ^ s.yPeriod % s.prime = 1

/-- The modulus of a valid stage is prime. -/
theorem PeriodicStage.IsValid.prime_prime
    {s : PeriodicStage} (h : s.IsValid) :
    Nat.Prime s.prime :=
  h.1

/-- The prime of a valid stage is greater than three. -/
theorem PeriodicStage.IsValid.prime_gt_three
    {s : PeriodicStage} (h : s.IsValid) :
    3 < s.prime :=
  h.2.1

/-- The period for powers of two is positive. -/
theorem PeriodicStage.IsValid.xPeriod_pos
    {s : PeriodicStage} (h : s.IsValid) :
    0 < s.xPeriod :=
  h.2.2.1

/-- The period for powers of three is positive. -/
theorem PeriodicStage.IsValid.yPeriod_pos
    {s : PeriodicStage} (h : s.IsValid) :
    0 < s.yPeriod :=
  h.2.2.2.1

/-- The stated period for powers of two is valid. -/
theorem PeriodicStage.IsValid.two_period
    {s : PeriodicStage} (h : s.IsValid) :
    2 ^ s.xPeriod % s.prime = 1 :=
  h.2.2.2.2.1

/-- The stated period for powers of three is valid. -/
theorem PeriodicStage.IsValid.three_period
    {s : PeriodicStage} (h : s.IsValid) :
    3 ^ s.yPeriod % s.prime = 1 :=
  h.2.2.2.2.2

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

/-- Every matching normalized class has a matching lift at the lcm moduli. -/
theorem refineClass_covers
    {r : SieveResidueClass} {Px Py x y : ℕ}
    (hr : r.WellFormed)
    (hPx : 0 < Px) (hPy : 0 < Py)
    (hmatch : r.Matches x y) :
    ∃ r' ∈ refineClass r Px Py,
      r'.WellFormed ∧ r'.Matches x y ∧
      r'.xModulus = Nat.lcm r.xModulus Px ∧
      r'.yModulus = Nat.lcm r.yModulus Py := by
  let Mx' := Nat.lcm r.xModulus Px
  let My' := Nat.lcm r.yModulus Py
  let xr := x % Mx'
  let yr := y % My'
  let kx := xr / r.xModulus
  let ky := yr / r.yModulus
  have hMx_dvd : r.xModulus ∣ Mx' := by
    dsimp [Mx']; exact Nat.dvd_lcm_left _ _
  have hMy_dvd : r.yModulus ∣ My' := by
    dsimp [My']; exact Nat.dvd_lcm_left _ _
  have hMx_pos : 0 < Mx' := by
    dsimp [Mx']; exact Nat.lcm_pos hr.xModulus_pos hPx
  have hMy_pos : 0 < My' := by
    dsimp [My']; exact Nat.lcm_pos hr.yModulus_pos hPy
  have hxr_lt : xr < Mx' := by
    dsimp [xr]; exact Nat.mod_lt _ hMx_pos
  have hyr_lt : yr < My' := by
    dsimp [yr]; exact Nat.mod_lt _ hMy_pos
  have hxr_mod : xr % r.xModulus = r.xResidue := by
    dsimp [xr, Mx']
    rw [Nat.mod_mod_of_dvd x (Nat.dvd_lcm_left r.xModulus Px)]
    exact hmatch.1
  have hyr_mod : yr % r.yModulus = r.yResidue := by
    dsimp [yr, My']
    rw [Nat.mod_mod_of_dvd y (Nat.dvd_lcm_left r.yModulus Py)]
    exact hmatch.2
  have hkx_lt : kx < Mx' / r.xModulus := by
    dsimp [kx]
    rw [Nat.div_lt_iff_lt_mul hr.xModulus_pos]
    rw [Nat.div_mul_cancel hMx_dvd]
    exact hxr_lt
  have hky_lt : ky < My' / r.yModulus := by
    dsimp [ky]
    rw [Nat.div_lt_iff_lt_mul hr.yModulus_pos]
    rw [Nat.div_mul_cancel hMy_dvd]
    exact hyr_lt
  have hxr_eq : xr = r.xResidue + kx * r.xModulus := by
    dsimp [kx]
    simpa [hxr_mod, Nat.add_comm, Nat.mul_comm] using
      (Nat.div_add_mod xr r.xModulus).symm
  have hyr_eq : yr = r.yResidue + ky * r.yModulus := by
    dsimp [ky]
    simpa [hyr_mod, Nat.add_comm, Nat.mul_comm] using
      (Nat.div_add_mod yr r.yModulus).symm
  let r' : SieveResidueClass :=
    { xModulus := Mx'
      yModulus := My'
      xResidue := r.xResidue + kx * r.xModulus
      yResidue := r.yResidue + ky * r.yModulus }
  refine ⟨r', ?_, ?_, ?_, ?_, ?_⟩
  · simp [refineClass, hPx.ne', hPy.ne', r', Mx', My', kx, ky,
      hkx_lt, hky_lt, hr.xModulus_pos.ne', hr.yModulus_pos.ne']
  · dsimp [SieveResidueClass.WellFormed, r']
    exact ⟨hMx_pos, hMy_pos, by simpa only [← hxr_eq] using hxr_lt,
      by simpa only [← hyr_eq] using hyr_lt⟩
  · dsimp [SieveResidueClass.Matches, r']
    constructor
    · rw [← hxr_eq]
    · rw [← hyr_eq]
  · rfl
  · rfl

/-- A genuine solution is accepted by a valid stage once its periods divide
    the current class moduli. -/
theorem PeriodicStage.allows_of_solution
    {s : PeriodicStage} {r : SieveResidueClass} {x y z : ℕ}
    (hs : s.IsValid)
    (hxdiv : s.xPeriod ∣ r.xModulus)
    (hydiv : s.yPeriod ∣ r.yModulus)
    (hmatch : r.Matches x y)
    (hsol : Solves x y z) :
    s.allows r = true := by
  have hp := hs.prime_prime
  have hp3 := hs.prime_gt_three
  letI : NeZero s.prime := ⟨hp.ne_zero⟩
  have hp1 : 1 < s.prime := by omega
  have h2 : (2 : ZMod s.prime) ^ s.xPeriod = 1 :=
    zmod_pow_eq_one_of_nat_mod_eq_one hp1 hs.two_period
  have h3 : (3 : ZMod s.prime) ^ s.yPeriod = 1 :=
    zmod_pow_eq_one_of_nat_mod_eq_one hp1 hs.three_period
  have hxrem : x % s.xPeriod = r.xResidue % s.xPeriod := by
    calc
      x % s.xPeriod = (x % r.xModulus) % s.xPeriod :=
        (Nat.mod_mod_of_dvd x hxdiv).symm
      _ = r.xResidue % s.xPeriod := by rw [hmatch.1]
  have hyrem : y % s.yPeriod = r.yResidue % s.yPeriod := by
    calc
      y % s.yPeriod = (y % r.yModulus) % s.yPeriod :=
        (Nat.mod_mod_of_dvd y hydiv).symm
      _ = r.yResidue % s.yPeriod := by rw [hmatch.2]
  have h2reduce :
      (2 : ZMod s.prime) ^ x =
        (2 : ZMod s.prime) ^ (x % s.xPeriod) :=
    zmod_pow_mod_eq 2 s.xPeriod s.prime h2 x
  have h3reduce :
      (3 : ZMod s.prime) ^ y =
        (3 : ZMod s.prime) ^ (y % s.yPeriod) :=
    zmod_pow_mod_eq 3 s.yPeriod s.prime h3 y
  have hcube :
      isCubeModB s.prime
        (2 ^ (x % s.xPeriod) + 3 ^ (y % s.yPeriod) + 5) = true := by
    apply isCubeModB_eq_true_of_zmod (z := (z : ZMod s.prime))
    simpa [h2reduce, h3reduce] using
      (zmod_equation_of_solution (m := s.prime) hsol)
  rw [hxrem, hyrem] at hcube
  simp [PeriodicStage.allows, hp.pos, hcube]

/-- One valid stage preserves coverage of every genuine solution. -/
theorem applyPeriodicStage_sound
    {rs : List SieveResidueClass} {s : PeriodicStage} {x y z : ℕ}
    (hs : s.IsValid)
    (hsol : Solves x y z)
    (hcov : CoveredBy rs x y) :
    CoveredBy (applyPeriodicStage rs s) x y := by
  rcases hcov with ⟨r, hrmem, hrwf, hrmatch⟩
  rcases refineClass_covers hrwf hs.xPeriod_pos hs.yPeriod_pos hrmatch with
    ⟨r', hr'mem, hr'wf, hr'match, hr'xmod, hr'ymod⟩
  have hxdiv : s.xPeriod ∣ r'.xModulus := by
    rw [hr'xmod]; exact Nat.dvd_lcm_right _ _
  have hydiv : s.yPeriod ∣ r'.yModulus := by
    rw [hr'ymod]; exact Nat.dvd_lcm_right _ _
  have hallows : s.allows r' = true :=
    s.allows_of_solution hs hxdiv hydiv hr'match hsol
  refine ⟨r', ?_, hr'wf, hr'match⟩
  unfold applyPeriodicStage
  rw [List.mem_flatMap]
  exact ⟨r, hrmem, by simp [hr'mem, hallows]⟩

/-- A valid list of stages preserves coverage. -/
theorem runPeriodicSieve_sound
    {rs : List SieveResidueClass} {ss : List PeriodicStage} {x y z : ℕ}
    (hvalid : ∀ s ∈ ss, s.IsValid)
    (hsol : Solves x y z)
    (hcov : CoveredBy rs x y) :
    CoveredBy (runPeriodicSieve rs ss) x y := by
  induction ss generalizing rs with
  | nil => simpa [runPeriodicSieve] using hcov
  | cons s ss ih =>
      have hs : s.IsValid := hvalid s (by simp)
      have htail : ∀ t ∈ ss, t.IsValid := by
        intro t ht
        exact hvalid t (by simp [ht])
      exact ih htail (applyPeriodicStage_sound hs hsol hcov)

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
  · dsimp [SieveResidueClass.WellFormed, r, rx, ry]
    exact ⟨by norm_num, by norm_num, Nat.mod_lt _ (by norm_num),
      Nat.mod_lt _ (by norm_num)⟩
  · exact ⟨rfl, rfl⟩

end KuromineProof