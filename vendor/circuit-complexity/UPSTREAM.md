Selected modules from https://github.com/formalcs/circuit-complexity
at commit `8b1a1afd4a816edb0ed0716f20ec739ab2c033d9`.

The 32 included modules are distributed under the included Apache-2.0 license.
They supply formula semantics, normalization, simulation, polynomial approximation
and the low-degree disagreement theorem used by the PLB Smolensky proof.
`PrimalityLowerBound/ACCTranslation.lean` translates PLB formulas to upstream formulas.
`PrimalityLowerBound/SmolenskyQuantitative.lean` uses the internal approximation APIs
and adapts the residue-counting argument from upstream
[`ACC/LowerBounds/Smolensky/Formula.lean`](https://github.com/formalcs/circuit-complexity/blob/8b1a1afd4a816edb0ed0716f20ec739ab2c033d9/ACC/LowerBounds/Smolensky/Formula.lean)
and its dependencies. This local obstruction proof is shared by the quantitative
and qualitative results in `PrimalityLowerBound/Quantitative.lean`.
The upstream `Formula.lean` and `Asymptotics/Polylogarithmic.lean` modules are not
included; the PLB proof uses its own shared asymptotic estimates.

This is a parent-project-only Lake package: run builds from the repository root.
It uses the parent’s pinned Lean `v4.34.0` and Mathlib `v4.34.0`; it deliberately
has no separate toolchain or Mathlib dependency and does not support standalone builds.

Local compatibility edits for Lean/Mathlib 4.34.0 (each modified source has a notice):

- `ACC/LowerBounds/BooleanDegree.lean`: replaced deprecated conditional lemmas and
  `push_neg`, removed redundant simp arguments, and updated proofs flagged by linters.
- `ACC/Formula/Transform/AndElimination.lean`: replaced deprecated `if_true` and
  `if_false` lemmas with `ite_true` and `ite_false`.
- `ACC/Probability/BoolAssignments.lean`: the same conditional-lemma updates.
- `ACC/Formula/Probabilistic/OrElimination/ApproximateOr.lean`: the same
  conditional-lemma updates.
- `ACC/LowerBounds/Smolensky/Restriction.lean`: updated deprecated conditional
  lemmas and removed the unused `ACC.Asymptotics.Polylogarithmic` import.

No retained upstream theorem statements have changed.
