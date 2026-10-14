import PrimalityLowerBound.Lemma4
import PrimalityLowerBound.GCD
import PrimalityLowerBound.SquareFree
import PrimalityLowerBound.Primes
import PrimalityLowerBound.DAG

/-!
# Main results

* **Theorem 1.** `TC⁰ ⊆ AC⁰[GCD]`, `TC⁰ ⊆ AC⁰[Square-Free]` (unconditional) and
  `TC⁰ ⊆ AC⁰[Primes]` (assuming equation (1) of the paper, `PageEstimate`).
* **Corollary 2.** Assuming Smolensky's theorem, none of `Primes`, `GCD`, `Square-Free` is in
  `AC⁰[p]` for any prime `p`.

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

/-- `Maj ≤ᵀ Primes`, assuming equation (1). -/
theorem maj_reduces_primes (hP : PageEstimate) : Maj ≤ᵀ Primes :=
  maj_reduces_mult.trans (mult_reduces_primes hP)

/-- **Theorem 1** (GCD). -/
theorem tc0_subset_ac0_gcd : TC0 ⊆ AC0 GCD := AC0.subset_of_reduces maj_reduces_gcd

/-- **Theorem 1** (Square-Free). -/
theorem tc0_subset_ac0_squarefree : TC0 ⊆ AC0 SquareFree :=
  AC0.subset_of_reduces maj_reduces_squarefree

/-- **Theorem 1** (Primes), assuming equation (1) (Page's theorem on primes in progressions). -/
theorem tc0_subset_ac0_primes (hP : PageEstimate) : TC0 ⊆ AC0 Primes :=
  AC0.subset_of_reduces (maj_reduces_primes hP)

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

/-- **Theorem 1** (Primes), DAG model, assuming equation (1). -/
theorem tc0DAG_subset_ac0DAG_primes (hP : PageEstimate) : TC0DAG ⊆ AC0DAG Primes := by
  rw [TC0DAG_eq, AC0DAG_eq]; exact tc0_subset_ac0_primes hP

/-! ### Corollary 2 -/

/-- Smolensky's theorem [Smo87] (building on Razborov [Raz87]), qualitative form: for distinct
primes `p` and `q`, `Mod_q` is not computed by polynomial-size constant-depth circuits (DAGs) of
`AND`, `OR`, `NOT` and `Mod_p` gates.  Not available in Mathlib; used as a hypothesis. -/
def SmolenskyTheorem : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ModLang q ∉ AC0DAG (ModLang p)

/-- `Mod_{p_j} ≤ᵀ mult`: a single `mult` gate (the gadget `M_{j,0}` of Lemma 4). -/
theorem modLang_reduces_mult {j : ℕ} (hj : 1 ≤ j) : ModLang (oddPrime j) ≤ᵀ mult := by
  refine Reduces.of_eventually 2 12 j fun n hn => ⟨resGate n j 0, depth_resGate_le n j 0, ?_, ?_⟩
  · refine (size_resGate_le n j 0).trans ?_
    have := resLen_le (n := n) (j := j) (r := 0) (by omega)
    have h1 : 1 ≤ (n + 2) ^ 11 := Nat.one_le_pow _ _ (by omega)
    calc 2 * resLen n j 0 + 1 ≤ 3 * (n + 2) ^ 11 := by omega
      _ ≤ (n + 2) * (n + 2) ^ 11 := Nat.mul_le_mul_right _ (by omega)
      _ = (n + 2) ^ 12 := by ring
  · intro z
    rw [eval_resGate n j 0 hj (oddPrime_prime j).pos, ModLang, decide_eq_decide,
      Nat.dvd_iff_mod_eq_zero]

/-- For every prime `p` there is an odd prime `q ≠ p` with `Mod_q ≤ᵀ mult`. -/
lemma exists_modLang_reduces_mult (p : ℕ) :
    ∃ q, q.Prime ∧ q ≠ p ∧ ModLang q ≤ᵀ mult := by
  by_cases hp : p = 3
  · refine ⟨5, by norm_num, by omega, ?_⟩
    rw [← oddPrime_two]; exact modLang_reduces_mult (by norm_num)
  · refine ⟨3, by norm_num, Ne.symm hp, ?_⟩
    rw [← oddPrime_one]; exact modLang_reduces_mult (by norm_num)

lemma not_mem_ac0_mod_of_mult_reduces (hS : SmolenskyTheorem) {A : Lang} (hA : mult ≤ᵀ A)
    {p : ℕ} (hp : p.Prime) : A ∉ AC0 (ModLang p) := by
  intro hAp
  obtain ⟨q, hq, hqp, hqm⟩ := exists_modLang_reduces_mult p
  have := hS p q hp hq (Ne.symm hqp)
  rw [AC0DAG_eq] at this
  exact this ((hqm.trans hA).trans hAp)

/-- **Corollary 2** (GCD): assuming Smolensky's theorem, `GCD ∉ AC⁰[p]` for every prime `p`. -/
theorem gcd_not_mem_ac0_mod (hS : SmolenskyTheorem) {p : ℕ} (hp : p.Prime) :
    GCD ∉ AC0 (ModLang p) :=
  not_mem_ac0_mod_of_mult_reduces hS mult_reduces_gcd hp

/-- **Corollary 2** (Square-Free): assuming Smolensky's theorem, `Square-Free ∉ AC⁰[p]`. -/
theorem squarefree_not_mem_ac0_mod (hS : SmolenskyTheorem) {p : ℕ} (hp : p.Prime) :
    SquareFree ∉ AC0 (ModLang p) :=
  not_mem_ac0_mod_of_mult_reduces hS mult_reduces_squarefree hp

/-- **Corollary 2** (Primes): assuming Smolensky's theorem and equation (1),
`Primes ∉ AC⁰[p]` for every prime `p`. -/
theorem primes_not_mem_ac0_mod (hS : SmolenskyTheorem) (hP : PageEstimate) {p : ℕ}
    (hp : p.Prime) : Primes ∉ AC0 (ModLang p) :=
  not_mem_ac0_mod_of_mult_reduces hS (mult_reduces_primes hP) hp

/-! ### Corollary 2 in the DAG-circuit model -/

theorem gcd_not_mem_ac0DAG_mod (hS : SmolenskyTheorem) {p : ℕ} (hp : p.Prime) :
    GCD ∉ AC0DAG (ModLang p) := by
  rw [AC0DAG_eq]; exact gcd_not_mem_ac0_mod hS hp

theorem squarefree_not_mem_ac0DAG_mod (hS : SmolenskyTheorem) {p : ℕ} (hp : p.Prime) :
    SquareFree ∉ AC0DAG (ModLang p) := by
  rw [AC0DAG_eq]; exact squarefree_not_mem_ac0_mod hS hp

theorem primes_not_mem_ac0DAG_mod (hS : SmolenskyTheorem) (hP : PageEstimate) {p : ℕ}
    (hp : p.Prime) : Primes ∉ AC0DAG (ModLang p) := by
  rw [AC0DAG_eq]; exact primes_not_mem_ac0_mod hS hP hp

end PLB
