Vendored dependency closure of `OAI.NumberTheory.PrimeGaps.Main` from
https://github.com/openai/math
at commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.

The 48 Lean modules are unchanged upstream sources, distributed under the included
Apache-2.0 license. This is a parent-project-only Lake package: run builds from
the repository root. It uses the parent’s pinned Lean `v4.34.0` and Mathlib
`v4.34.0`, rather than the upstream Lean 4.34.1 toolchain. It deliberately has
no separate toolchain or Mathlib dependency and does not support standalone builds.

The source theorem `OAI.LargePrimeGaps.siegelWalfisz` gives uniform character-sum
bounds. `PrimalityLowerBound/PageProof.lean` supplies the bridge to this project’s
prime-counting statement.
