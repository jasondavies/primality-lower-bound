import Mathlib

/-!
# Primes in arithmetic progressions: equation (1) of the paper

The paper uses the following consequence of Page's theorem [P35] (see also Prachar [P57]):
uniformly for primes `p ≤ n` and `1 ≤ l < p`,
`π(2ⁿ, p, l) ∼ 2ⁿ / (n (p - 1) ln 2)`.
This file defines the prime counts and windows used in the estimate.
`PageProof.lean` proves `pageEstimate` and `primesWindow_lower_bound` from a vendored
Siegel–Walfisz theorem.
-/

namespace PLB

/-- `π(x, m, l)`: the number of primes `q ≤ x` with `q ≡ l (mod m)`. -/
def primesAP (x m l : ℕ) : ℕ := ((Finset.range (x + 1)).filter fun q => q.Prime ∧ q % m = l).card

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

end PLB
