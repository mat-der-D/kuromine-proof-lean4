import KuromineProof.Sieve.Core

namespace KuromineProof

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
  · exact
      { xModulus_pos := hMx_pos
        yModulus_pos := hMy_pos
        xResidue_lt := by simpa only [← hxr_eq] using hxr_lt
        yResidue_lt := by simpa only [← hyr_eq] using hyr_lt }
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

end KuromineProof
