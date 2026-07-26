# kuromine-proof-lean4

A Lean 4 formalization of the simplified proof of the Kuromine equation

```text
2^x + 3^y + 5 = z^3.
```

The target theorem is that the only integer solutions are

```text
(x, y, z) = (1, 0, 2), (5, 3, 4).
```

## Current status

The following parts are formalized and verified by CI:

- the equation over nonnegative integers and the two known solutions;
- the eight-stage finite congruence sieve;
- the resulting conditions `x ≡ 1 (mod 4)` and `y ≡ 45 (mod 48)` for `x ≥ 6`, `y ≥ 3`;
- the elimination of that remaining range using `A = z - 3^(y/3)` and the Jacobi symbol.

The current public theorem is:

```lean
theorem no_large_solution
    {x y z : ℕ}
    (hx6 : 6 ≤ x)
    (hy3 : 3 ≤ y)
    (hsol : Solves x y z) :
    False
```

The remaining work is the classification of the small exponent cases and the reduction from integer exponents to nonnegative exponents.

## References

This project follows the simplified proof described in:

- https://smooth-pudding.hatenablog.com/entry/2026/07/26/082029

The earlier complete Lean formalization is used as a technical reference:

- https://github.com/nakashima-hikaru/kuromine-lean4

Code adapted from that repository is used under the Apache License 2.0.
