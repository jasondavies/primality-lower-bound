Vendored dependency closure of `ACC.LowerBounds.Smolensky.Formula` from
https://github.com/formalcs/circuit-complexity
at commit `8b1a1afd4a816edb0ed0716f20ec739ab2c033d9`.

The upstream sources are distributed under the included Apache-2.0 license.
Only the 34 modules needed by the qualitative Smolensky theorem are included.
The local Lake configuration uses the parent project’s pinned Mathlib and Lean.

Local compatibility change for Lean/Mathlib 4.34.0:
- `ACC/LowerBounds/Smolensky/Formula.lean`: removed a redundant `norm_num`
  after `gcongr`, which now closes the goal itself. No theorem statements changed.
