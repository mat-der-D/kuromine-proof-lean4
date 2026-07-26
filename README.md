# kuromine-proof-lean4

A Lean 4 formalization of the simplified proof of the Kuromine equation

```text
2^x + 3^y + 5 = z^3.
```

The main theorem proves that the only integer solutions are

```text
(x, y, z) = (1, 0, 2), (5, 3, 4).
```

Integer exponents are interpreted as powers in `ℚ`.

## Main theorem

```lean
theorem classify_integer_solutions
    {x y z : ℤ}
    (h : SolvesInteger x y z) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨
    (x = 5 ∧ y = 3 ∧ z = 4)
```

## Proof structure

1. Negative exponents are eliminated after clearing denominators, using reduction modulo `2` or `3`.
2. The cases with small exponents are classified directly.
3. An eight-stage finite sieve using the primes
   `73, 13, 577, 97, 673, 337, 43, 1009`
   leaves three residue classes modulo `(1008, 336)`.
4. These classes imply
   `x ≡ 1 (mod 4)` and `y ≡ 45 (mod 48)`.
5. The remaining range is eliminated using
   `A = z - 3^(y/3)` and the Jacobi symbol `(-10 / A)`.

The Lean modules follow the same high-level argument while keeping reusable
computation and soundness proofs separate:

- `SmallCases` handles the direct classifications.
- `Sieve.Core`, `Sieve.Soundness`, `Sieve.Initial`, and `Sieve.Certificate`
  separate the finite-sieve computation from its mathematical justification.
- `LargeCase` proves that the sieve congruences contradict the Jacobi-symbol
  argument.
- `NaturalClassification` combines the natural-number cases.
- `Main` reduces integer solutions to the natural-number classification.

The closed finite sieve is checked by `native_decide`; its soundness is proved separately.

## Build

The project uses Lean 4.30.0 and mathlib 4.30.0.

```bash
lake exe cache get
lake build
```

GitHub Actions runs the same proof verification on every push and pull request.

## References

The simplified proof formalized here is described in:

- https://smooth-pudding.hatenablog.com/entry/2026/07/26/082029

The earlier complete Lean formalization was used as a technical reference:

- https://github.com/nakashima-hikaru/kuromine-lean4

Code adapted from that repository is used under the Apache License 2.0.
