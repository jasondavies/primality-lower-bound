Vendored dependency closure of `ACC.LowerBounds.Smolensky.Formula` from
https://github.com/formalcs/circuit-complexity
at commit `8b1a1afd4a816edb0ed0716f20ec739ab2c033d9`.

The upstream sources are distributed under the included Apache-2.0 license.
The 34 included modules support both qualitative and quantitative Smolensky proofs.
`PrimalityLowerBound/Smolensky.lean` applies the qualitative theorem.
`PrimalityLowerBound/SmolenskyQuantitative.lean` uses the internal normalization,
simulation and polynomial-approximation APIs and adapts the polynomial obstruction
argument from `ACC/LowerBounds/Smolensky/Formula.lean` and its dependencies.

This is a parent-project-only Lake package: run builds from the repository root.
It uses the parent’s pinned Lean `v4.34.0` and Mathlib `v4.34.0`; it deliberately
has no separate toolchain or Mathlib dependency and does not support standalone builds.

Local compatibility change for Lean/Mathlib 4.34.0:
- `ACC/LowerBounds/Smolensky/Formula.lean`: removed a redundant `norm_num`
  after `gcongr`, which now closes the goal itself. No theorem statements changed.
