import Mathlib

/-!
# Primes in arithmetic progressions: equation (1) of the paper

The paper uses the following consequence of Page's theorem [P35] (see also Prachar [P57]):
uniformly for primes `p ≤ n` and `1 ≤ l < p`,
`π(2ⁿ, p, l) ∼ 2ⁿ / (n (p - 1) ln 2)`.
We state the estimate as `PageEstimate` and derive the lower bound used by the reduction.
`PageProof.lean` proves `pageEstimate : PageEstimate` from a vendored Siegel–Walfisz theorem.
-/

namespace PLB

/-- `π(x, m, l)`: the number of primes `q ≤ x` with `q ≡ l (mod m)`. -/
def primesAP (x m l : ℕ) : ℕ := ((Finset.range (x + 1)).filter fun q => q.Prime ∧ q % m = l).card

/-- Equation (1) of the paper: `π(2ⁿ, p, l) ∼ 2ⁿ / (n (p - 1) ln 2)` uniformly for primes `p ≤ n`
and `1 ≤ l < p`. -/
def PageEstimate : Prop :=
  ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ p l : ℕ, p.Prime → 1 ≤ l → l < p → p ≤ n →
    |(primesAP (2 ^ n) p l : ℝ) / (2 ^ n / (n * ((p : ℝ) - 1) * Real.log 2)) - 1| ≤ ε

/-- Primes in the window `(2ⁿ, 2ⁿ⁺¹]` congruent to `l` mod `p`. -/
def primesWindow (n p l : ℕ) : Finset ℕ :=
  (Finset.Ioc (2 ^ n) (2 ^ (n + 1))).filter fun q => q.Prime ∧ q % p = l

lemma primesAP_succ_eq (n p l : ℕ) :
    primesAP (2 ^ (n + 1)) p l = primesAP (2 ^ n) p l + (primesWindow n p l).card := by
  unfold primesAP primesWindow
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
    have : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    constructor
    · rintro ⟨hq, h⟩
      by_cases hqn : q < 2 ^ n + 1
      · exact Or.inl ⟨hqn, h⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, h⟩
    · rintro (⟨hq, h⟩ | ⟨⟨h1, h2⟩, h⟩)
      · exact ⟨by omega, h⟩
      · exact ⟨by omega, h⟩
  · rw [Finset.disjoint_left]
    intro q h1 h2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at h1 h2
    omega

/-- The consequence of (1) that we use: for large `n`, the window `(2ⁿ, 2ⁿ⁺¹]` contains at least
`2ⁿ / (2 (n + 1) p)` primes `≡ l (mod p)`. -/
theorem PageEstimate.window (hP : PageEstimate) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ p l : ℕ, p.Prime → 1 ≤ l → l < p → p ≤ n →
      2 ^ n ≤ 2 * (n + 1) * p * (primesWindow n p l).card := by
  obtain ⟨N₁, hN₁⟩ := hP (1 / 10) (by norm_num)
  refine ⟨max N₁ 6, fun n hn p l hp hl hlp hpn => ?_⟩
  have hn6 : 6 ≤ n := le_of_max_le_right hn
  have h1 := hN₁ n (le_of_max_le_left hn) p l hp hl hlp hpn
  have h2 := hN₁ (n + 1) (by have := le_of_max_le_left hn; omega) p l hp hl hlp (by omega)
  rw [primesAP_succ_eq] at h2
  push_cast at h2
  set a := (primesAP (2 ^ n) p l : ℝ)
  set w := ((primesWindow n p l).card : ℝ)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hnr : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  set B := (2 : ℝ) ^ n / (((p : ℝ) - 1) * Real.log 2) with hB
  have hBpos : 0 < B := by positivity
  have hA1 : (2 : ℝ) ^ n / (n * ((p : ℝ) - 1) * Real.log 2) = B / n := by
    rw [hB]; field_simp
  have hA2 : (2 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((p : ℝ) - 1) * Real.log 2) =
      2 * B / (n + 1) := by
    rw [hB, pow_succ]; field_simp
  rw [hA1] at h1
  rw [hA2] at h2
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : a ≤ (11 / 10) * (B / n) := by
    have := (abs_le.1 h1).2
    have hpos : 0 < B / n := by positivity
    have : a / (B / n) ≤ 11 / 10 := by linarith
    rwa [div_le_iff₀ hpos] at this
  have hw : (9 / 10) * (2 * B / (n + 1)) ≤ a + w := by
    have := (abs_le.1 h2).1
    have hpos : 0 < 2 * B / (n + 1) := by positivity
    have : (9 / 10 : ℝ) ≤ (a + w) / (2 * B / (n + 1)) := by linarith
    rwa [le_div_iff₀ hpos] at this
  -- `w ≥ B / (2 (n + 1))`
  have hw2 : B / (2 * (n + 1)) ≤ w := by
    have e1 : (9 / 10) * (2 * B / (n + 1)) - (11 / 10) * (B / n) - B / (2 * (n + 1)) =
        B * (n / 5 - 11 / 10) / (n * (n + 1)) := by field_simp; ring
    have e2 : 0 ≤ B * (n / 5 - 11 / 10) / (n * (n + 1)) := by
      apply div_nonneg (mul_nonneg hBpos.le (by linarith)) (by positivity)
    linarith
  -- `B ≥ 2ⁿ / p`
  have hBp : (2 : ℝ) ^ n / p ≤ B := by
    rw [hB]
    apply div_le_div_of_nonneg_left (by positivity) (by nlinarith)
    nlinarith
  have hfinal : (2 : ℝ) ^ n ≤ 2 * (n + 1) * p * w := by
    have : (2 : ℝ) ^ n / p / (2 * (n + 1)) ≤ w :=
      le_trans (div_le_div_of_nonneg_right hBp (by positivity)) hw2
    rw [div_div, div_le_iff₀ (by positivity)] at this
    linarith
  have : ((2 ^ n : ℕ) : ℝ) ≤ ((2 * (n + 1) * p * (primesWindow n p l).card : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

end PLB
