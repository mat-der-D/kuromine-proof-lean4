import KuromineProof.Basic
import Mathlib.Data.ZMod.Basic

namespace KuromineProof

/-- Read equality in `ZMod m` as equality of natural remainders. -/
theorem nat_mod_eq_of_zmod_eq {n a m : ℕ} [NeZero m]
    (h : (n : ZMod m) = (a : ZMod m)) :
    n % m = a % m := by
  have hval := congrArg ZMod.val h
  simpa [ZMod.val_natCast] using hval

/-- Convert a power identity in `ZMod m` to a natural-number remainder identity. -/
theorem nat_pow_mod_eq_of_zmod_pow_eq {a n r m : ℕ} [NeZero m]
    (h : (a : ZMod m) ^ n = (r : ZMod m)) :
    a ^ n % m = r % m := by
  apply nat_mod_eq_of_zmod_eq
  push_cast
  exact h

/-- Cast a natural-number solution of the Kuromine equation into `ZMod m`. -/
theorem zmod_equation_of_solution {m x y z : ℕ} [NeZero m]
    (hsol : Solves x y z) :
    (z : ZMod m) ^ 3 =
      (2 : ZMod m) ^ x + (3 : ZMod m) ^ y + 5 := by
  unfold Solves at hsol
  have hcast :
      ((z ^ 3 : ℕ) : ZMod m) =
        ((2 ^ x + 3 ^ y + 5 : ℕ) : ZMod m) := by
    rw [hsol]
  push_cast at hcast
  exact hcast

/-- Reduce an exponent modulo any certified period. -/
theorem zmod_pow_mod_eq (a d m : ℕ)
    (hperiod : (a : ZMod m) ^ d = 1) (n : ℕ) :
    (a : ZMod m) ^ n = (a : ZMod m) ^ (n % d) := by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [Nat.mod_zero]
  · have hdiv : n = d * (n / d) + n % d := (Nat.div_add_mod n d).symm
    nth_rw 1 [hdiv]
    rw [pow_add, pow_mul, hperiod, one_pow, one_mul]

end KuromineProof
