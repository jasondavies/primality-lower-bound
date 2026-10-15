import PrimalityLowerBound.Quantitative

/-!
# Main results

* **Theorem 1.** `TC⁰ ⊆ AC⁰[GCD]`, `TC⁰ ⊆ AC⁰[Square-Free]` and
  `TC⁰ ⊆ AC⁰[Primes]`.
* **Corollary 2.** `Primes`, `GCD` and `Square-Free` are not in `AC⁰[p]` for any prime `p`.
  These follow from the exponential bounds in `Quantitative.lean`, which also contains
  the quantitative and qualitative Smolensky theorems.

Both are stated for the formula model (`AC0`) and for the DAG-circuit model of the paper
(`AC0DAG`); the two models coincide (`AC0DAG_eq`).
-/

namespace PLB

open Circuit

/-! ### Theorem 1 -/

/-- `Maj ≤ᵀ GCD`. -/
theorem maj_reduces_gcd : Maj ≤ᵀ GCD := maj_reduces_mult.trans mult_reduces_gcd

/-- `Maj ≤ᵀ Square-Free`. -/
theorem maj_reduces_squarefree : Maj ≤ᵀ SquareFree :=
  maj_reduces_mult.trans mult_reduces_squarefree

/-- `Maj ≤ᵀ Primes`. -/
theorem maj_reduces_primes : Maj ≤ᵀ Primes :=
  maj_reduces_mult.trans mult_reduces_primes

/-- **Theorem 1** (GCD). -/
theorem tc0_subset_ac0_gcd : TC0 ⊆ AC0 GCD := AC0.subset_of_reduces maj_reduces_gcd

/-- **Theorem 1** (Square-Free). -/
theorem tc0_subset_ac0_squarefree : TC0 ⊆ AC0 SquareFree :=
  AC0.subset_of_reduces maj_reduces_squarefree

/-- **Theorem 1** (Primes). -/
theorem tc0_subset_ac0_primes : TC0 ⊆ AC0 Primes :=
  AC0.subset_of_reduces maj_reduces_primes

/-! ### Theorem 1 in the DAG-circuit model -/

/-- `TC⁰` in the DAG model: `AC⁰[Maj]` with circuits as DAGs. -/
def TC0DAG : Set Lang := AC0DAG Maj

lemma TC0DAG_eq : TC0DAG = TC0 := AC0DAG_eq Maj

/-- **Theorem 1** (GCD), DAG model. -/
theorem tc0DAG_subset_ac0DAG_gcd : TC0DAG ⊆ AC0DAG GCD := by
  rw [TC0DAG_eq, AC0DAG_eq]; exact tc0_subset_ac0_gcd

/-- **Theorem 1** (Square-Free), DAG model. -/
theorem tc0DAG_subset_ac0DAG_squarefree : TC0DAG ⊆ AC0DAG SquareFree := by
  rw [TC0DAG_eq, AC0DAG_eq]; exact tc0_subset_ac0_squarefree

/-- **Theorem 1** (Primes), DAG model. -/
theorem tc0DAG_subset_ac0DAG_primes : TC0DAG ⊆ AC0DAG Primes := by
  rw [TC0DAG_eq, AC0DAG_eq]; exact tc0_subset_ac0_primes

/-! ### Corollary 2 in the DAG-circuit model -/

/-- **Corollary 2** (GCD), from the exponential bound at lengths divisible by three. -/
theorem gcd_not_mem_ac0DAG_mod {p : ℕ} (hp : p.Prime) :
    GCD ∉ AC0DAG (ModLang p) := by
  apply not_mem_ac0DAG_of_exp_lower_bound (fun N => 3 ∣ N)
    (fun n => ⟨3 * n, by omega, by simp⟩)
  exact gcd_exp_lower_bound hp

/-- **Corollary 2** (Square-Free), from its exponential lower bound. -/
theorem squarefree_not_mem_ac0DAG_mod {p : ℕ} (hp : p.Prime) :
    SquareFree ∉ AC0DAG (ModLang p) := by
  apply not_mem_ac0DAG_of_exp_lower_bound (fun _ => True) (fun n => ⟨n, le_rfl, trivial⟩)
  simpa using squarefree_exp_lower_bound hp

/-- **Corollary 2** (Primes), from its exponential lower bound. -/
theorem primes_not_mem_ac0DAG_mod {p : ℕ}
    (hp : p.Prime) : Primes ∉ AC0DAG (ModLang p) := by
  apply not_mem_ac0DAG_of_exp_lower_bound (fun _ => True) (fun n => ⟨n, le_rfl, trivial⟩)
  simpa using primes_exp_lower_bound hp

/-! ### Corollary 2 in the formula model -/

/-- **Corollary 2** (GCD): `GCD ∉ AC⁰[p]` for every prime `p`. -/
theorem gcd_not_mem_ac0_mod {p : ℕ} (hp : p.Prime) :
    GCD ∉ AC0 (ModLang p) := by
  rw [← AC0DAG_eq]; exact gcd_not_mem_ac0DAG_mod hp

/-- **Corollary 2** (Square-Free): `Square-Free ∉ AC⁰[p]`. -/
theorem squarefree_not_mem_ac0_mod {p : ℕ} (hp : p.Prime) :
    SquareFree ∉ AC0 (ModLang p) := by
  rw [← AC0DAG_eq]; exact squarefree_not_mem_ac0DAG_mod hp

/-- **Corollary 2** (Primes): `Primes ∉ AC⁰[p]` for every prime `p`. -/
theorem primes_not_mem_ac0_mod {p : ℕ}
    (hp : p.Prime) : Primes ∉ AC0 (ModLang p) := by
  rw [← AC0DAG_eq]; exact primes_not_mem_ac0DAG_mod hp

end PLB
