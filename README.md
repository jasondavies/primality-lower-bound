# A Lower Bound for Primality — Lean 4 formalisation

A Lean 4 / Mathlib formalisation of

> E. Allender, M. Saks, I. Shparlinski, *A Lower Bound for Primality*,
> ECCC Comment 1 on Report TR99-010 (preliminary version in CCC 1999).
> <https://eccc.weizmann.ac.il/report/1999/010/comment/1/download/>

The paper shows that `Maj` is AC⁰-Turing reducible to the set of primes, to GCD and to
the square-free numbers. Together with Razborov–Smolensky this gives the corollary that none of
these sets is in AC⁰[p] for any prime p.

## Building

```
lake exe cache get
lake build
```

The toolchain is Lean `v4.34.0` with Mathlib `v4.34.0`. The development contains no `sorry`
and declares no axioms. `#print axioms` on every main theorem shows only `propext`,
`Classical.choice` and `Quot.sound`.

## What is proved

| Paper | Lean |
|---|---|
| Lemma 4: `Maj ≤ᵀ mult` | `maj_reduces_mult` |
| Lemma 5.1: `mult ≤ᵀ GCD` | `mult_reduces_gcd` |
| Lemma 5.2: `mult ≤ᵀ Primes` | `mult_reduces_primes` |
| Lemma 5.3: `mult ≤ᵀ Square-Free` | `mult_reduces_squarefree` |
| Theorem 1: `TC⁰ ⊆ AC⁰[GCD]` | `tc0_subset_ac0_gcd`, `tc0DAG_subset_ac0DAG_gcd` |
| Theorem 1: `TC⁰ ⊆ AC⁰[Square-Free]` | `tc0_subset_ac0_squarefree`, `tc0DAG_subset_ac0DAG_squarefree` |
| Theorem 1: `TC⁰ ⊆ AC⁰[Primes]` | `tc0_subset_ac0_primes`, `tc0DAG_subset_ac0DAG_primes` |
| Corollary 2: GCD, Square-Free and Primes not in `AC⁰[p]` | `gcd_not_mem_ac0DAG_mod`, `squarefree_not_mem_ac0DAG_mod`, `primes_not_mem_ac0DAG_mod` |
| Corollary 2: GCD, Square-Free and Primes size `≥ 2^(N^δ)` | `gcd_exp_lower_bound`, `squarefree_exp_lower_bound`, `primes_exp_lower_bound` |
| Transitivity of `≤ᵀ` | `Reduces.trans` |

### Formalised Page estimate

`pageEstimate` (`PageProof.lean`) proves the paper's equation (1): uniformly
for primes `p ≤ n` and `1 ≤ l < p`, the number of primes `q ≤ 2ⁿ` with `q ≡ l (mod p)` is
asymptotic to `2ⁿ / (n (p − 1) ln 2)`. The threshold is independent of the modulus and residue.
`primesWindow_lower_bound` then gives the lower bound in `(2ⁿ, 2ⁿ⁺¹]` used by the primality reduction.

The analytic input is the proved
[`OAI.LargePrimeGaps.siegelWalfisz`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PrimeGaps/Main.lean).
Its 48-module dependency closure is vendored unchanged, with its Apache-2.0 license and
[provenance](vendor/openai-math/UPSTREAM.md), and builds against this project's pinned
Lean 4.34.0 and Mathlib.

The bridge first uses character orthogonality to bound von Mangoldt sums in arithmetic
progressions. Removing prime powers gives a weighted prime-counting estimate at `2ⁿ`,
uniformly for `p ≤ n`. Splitting the primes at `rⁿ`, where `1 < r < 2` is chosen sufficiently
close to `2`, removes the logarithmic weights: the small-prime contribution tends to zero,
and the large-prime weights lie between `n log r` and `n log 2`.

All primality results use this proof directly. Page and both Smolensky results depend only
on `propext`, `Classical.choice`, and `Quot.sound`; the main results are unconditional.

### Formalised qualitative Smolensky theorem

`smolenskyTheorem` (`Quantitative.lean`) proves that, for distinct primes `p ≠ q`,
`Mod_q` is not in AC⁰[Mod_p]. It follows from `smolenskyExpTheorem`: a bound of
`2^(n^δ)` eventually exceeds every polynomial size bound. The six qualitative
`*_not_mem_ac0*_mod` theorems in `Main.lean` use the general lemma
`not_mem_ac0_mod_of_mult_reduces`: any language `A` with `mult ≤ᵀ A` lies outside
AC⁰[Mod_p] for prime `p`, by Smolensky and transitivity of reductions.

The shared proof uses 32 source modules from
[formalcs/circuit-complexity](https://github.com/formalcs/circuit-complexity/tree/8b1a1afd4a816edb0ed0716f20ec739ab2c033d9),
vendored with their Apache-2.0 license.
[UPSTREAM.md](vendor/circuit-complexity/UPSTREAM.md) records the revision, local proof
adaptations and compatibility edits.

### Formalised quantitative Smolensky theorem

`smolenskyExpTheorem` (`Quantitative.lean`) proves the exponential
lower bound for individual DAG circuits, uniformly over all sufficiently large input lengths.
`ACCTranslation.lean` translates PLB formulas to upstream ACC formulas, preserving evaluation
and node count and bounding depth. `SmolenskyQuantitative.lean` extracts an explicit
approximation for a single formula on `n ≥ 1` inputs, of size at most `B` with `n ≤ B`:
degree `O((log B)^(8d+1))`, with error
on at most a `1/n` fraction of inputs.
The locally adapted polynomial obstruction then gives size at least `2^t` on a polynomial
sequence of input lengths. Zero-padding and interpolation extend this to all large lengths in
`smolensky_formula_exp_bound`. Unfolding DAGs into formulas gives `smolenskyExpTheorem`.
The reductions for Corollary 2 apply the formula bound directly to the composed formula.

The quantitative Primes, GCD and square-free lower bounds are unconditional.
Their axiom dependencies are only `propext`, `Classical.choice` and `Quot.sound`.

## Circuit model

`Circuit.lean` defines unbounded fan-in circuits with `AND`, `OR`, `NOT` and oracle gates as
formulas (trees). It also defines non-uniform AC⁰ Turing reducibility `A ≤ᵀ B`, meaning
polynomial size and constant depth, and `AC0 L`. The paper's circuits are DAGs, so `DAG.lean`
defines DAG circuits whose size counts gates plus wires. It proves `dagReduces_iff`, which says
that the DAG model and the formula model give exactly the same reducibility. Theorem 1 and
the qualitative Corollary 2 are stated in both models; the exponential bounds use the DAG model.

Inputs are bit strings `x_{n−1} … x_0` that denote `∑ xᵢ 2ⁱ`, as in the paper. `GCD` and
`mult` take inputs of length `3m` and `2m`, read as triples and pairs of `m`-bit numbers.

## Deviations from the paper's proofs

The statements follow the paper. Some proofs were changed to make them simpler to formalise:

- **Lemma 4.** The paper computes `f_j(x) − r`, which can be negative. Instead we append
  `p_j − r` ones to `x`, so the query is pure wiring. Chinese remaindering uses the first
  `⌊log₂ n⌋ + 1` odd primes.
- **Bounding `p_j`.** `mult(x, j)` allows `j` up to `|x|`, so the circuits need `p_j` to be
  polynomial in `j`. We prove `p_j ≤ 8(j+1)²` from the central binomial coefficient
  (`NthPrime.lean`). Mathlib has no Chebyshev lower bound.
- **Lemma 5.2 (Primes).** We query `x + p·y` with `y ≥ 2` and no random sign. This keeps the
  query positive and different from `p`. The window is `(2^N, 2^{N+1}]` with
  `N = m + p + 1`, so that `p ≤ N` as equation (1) requires. Adleman's probabilistic argument
  becomes a greedy hitting-set lemma (`HittingSet.lean`).
- **Lemma 5.3 (Square-Free).** The paper multiplies `x` by `p` in AC⁰ and uses estimate (2),
  which involves `ζ(2)` and Möbius sums. We avoid multiplication. Since `2^{p(p−1)} ≡ 1 (mod p²)`,
  a number `h(x) ≡ p·x (mod p²)` can be wired directly from the bits of `x`. The advice `y`
  goes into the high bits. An elementary sieve then shows that at least a quarter of the
  candidates are square-free (`SquareFreeCount.lean`).
- **Proposition 3.** Only addition of a hard-wired constant is needed. It is implemented and
  proved as a carry-lookahead adder (`Adder.lean`). Short inputs are handled by brute-force DNFs.
- **Quantitative Corollary 2.** The exponential bound is derived by padding: a circuit on `N`
  bits also decides shorter inputs. For `GCD` it is stated for input lengths divisible by 3,
  because other lengths encode no triple and `GCD` is constant on them. The bound is on DAG
  size, which counts gates plus wires. Wires must be counted so that one gate cannot read an
  input many times for free. A circuit with `g` gates on `N` inputs and no repeated wires has
  at most `g (g + N)` wires. So a size bound of `2^(N^δ)` still forces at least
  `2^(N^δ / 2) − N − 1` gates, a stretched-exponential lower bound on the number of gates
  in terms of the input length `N`.

The remarks and open problems in Section 4 are not formalised. This includes the parity of
`ω(x)`.

## Files

| File | Contents |
|---|---|
| `Circuit.lean` | formulas, size and depth, substitution, composition, `≤ᵀ`, transitivity, DNF |
| `DAG.lean` | DAG circuits and equivalence with formulas |
| `Bits.lean` | values of bit strings |
| `Languages.lean` | `Maj`, `Mod_k`, `Primes`, `Square-Free`, `GCD`, `mult`, `TC⁰`, `p_j` |
| `NthPrime.lean` | `p_j ≤ 8 (j+1)²` |
| `Lemma4.lean` | `Maj ≤ᵀ mult` and the `Mod_{p_j} ≤ᵀ mult` gadget |
| `MultWrapper.lean` | building `mult` circuits from tests for divisibility by `p_j` |
| `GCD.lean` | `mult ≤ᵀ GCD` |
| `HittingSet.lean` | Adleman's argument as a hitting-set lemma |
| `SquareFreeCount.lean`, `SquareFree.lean` | `mult ≤ᵀ Square-Free` |
| `Adder.lean` | constant-depth adder |
| `Page.lean` | prime counts and dyadic windows |
| `PageProof.lean` | proof of equation (1) and its window consequence from Siegel–Walfisz |
| `Primes.lean` | `mult ≤ᵀ Primes` |
| `Main.lean` | Theorem 1 and Corollary 2 |
| `ACCTranslation.lean` | translation to upstream ACC formulas |
| `SmolenskyQuantitative.lean` | individual-formula approximation and quantitative polynomial obstruction |
| `Asymptotics.lean` | shared polynomial versus stretched-exponential estimates |
| `Quantitative.lean` | quantitative and qualitative Smolensky; exponential Corollary 2 |
