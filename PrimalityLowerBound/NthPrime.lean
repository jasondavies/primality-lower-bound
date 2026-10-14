import Mathlib

/-!
# A polynomial upper bound for the `k`-th prime

Chebyshev-type estimate from the central binomial coefficient:
`nth Nat.Prime k ≤ 8 (k + 1)²`.
-/

namespace PLB

open Nat Finset

/-- `4 ^ N ≤ (2N) ^ (π(2N) + 1)` (Chebyshev's argument). -/
lemma four_pow_le_pow_primeCounting (N : ℕ) (hN : 0 < N) :
    4 ^ N ≤ (2 * N) ^ (primeCounting (2 * N) + 1) := by
  have h1 := four_pow_le_two_mul_self_mul_centralBinom N hN
  have h2 : centralBinom N ≤ (2 * N) ^ primeCounting (2 * N) := by
    rw [← prod_pow_factorization_centralBinom N]
    calc ∏ p ∈ range (2 * N + 1), p ^ (centralBinom N).factorization p
        ≤ ∏ p ∈ range (2 * N + 1), (if p.Prime then 2 * N else 1) := by
          refine Finset.prod_le_prod fun p _ => ?_
          split_ifs with hp
          · exact pow_factorization_choose_le (by omega)
          · simp [factorization_eq_zero_of_not_prime _ hp]
      _ = (2 * N) ^ primeCounting (2 * N) := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const,
            ← primesLE_card_eq_primeCounting, primesLE_eq_filter_range]
  calc 4 ^ N ≤ 2 * N * centralBinom N := h1
    _ ≤ 2 * N * (2 * N) ^ primeCounting (2 * N) := by gcongr
    _ = (2 * N) ^ (primeCounting (2 * N) + 1) := by ring

lemma eight_mul_sq_lt (a : ℕ) (ha : 1 ≤ a) : 8 * a ^ 2 < 2 ^ (8 * a) := by
  have h1 : a < 2 ^ a := Nat.lt_two_pow_self
  have h2 : a ^ 2 < (2 ^ a) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
  have h3 : 8 ≤ 2 ^ (6 * a) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (6 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 8 * a ^ 2 < 8 * (2 ^ a) ^ 2 := by omega
    _ ≤ 2 ^ (6 * a) * (2 ^ a) ^ 2 := by gcongr
    _ = 2 ^ (8 * a) := by rw [← pow_mul, ← pow_add]; ring_nf

/-- The `k`-th prime (0-indexed, `nth Nat.Prime 0 = 2`) is at most `8 (k + 1)²`. -/
theorem nth_prime_le (k : ℕ) : nth Nat.Prime k ≤ 8 * (k + 1) ^ 2 := by
  set a := k + 1
  set N := 4 * a ^ 2
  have hN : 0 < N := by positivity
  have hcount : k < primeCounting (2 * N) := by
    by_contra hlt
    rw [not_lt] at hlt
    have h := four_pow_le_pow_primeCounting N hN
    have h' : (2 * N) ^ (primeCounting (2 * N) + 1) ≤ (2 * N) ^ a :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h'' : (2 * N) ^ a < 4 ^ N := by
      calc (2 * N) ^ a = (8 * a ^ 2) ^ a := by simp only [N]; ring
        _ < (2 ^ (8 * a)) ^ a := Nat.pow_lt_pow_left (eight_mul_sq_lt a (by omega)) (by omega)
        _ = 4 ^ N := by
          rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; simp only [N]; ring_nf
    omega
  have := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := 2 * N + 1) hcount
  omega

end PLB
