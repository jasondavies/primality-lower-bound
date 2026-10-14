import PrimalityLowerBound.Bits
import PrimalityLowerBound.NthPrime

/-!
# The languages of the paper

All inputs are bit strings `x = x_{n-1} … x_0` representing `∑ xᵢ 2ⁱ`.
-/

namespace PLB

open Nat

/-- `Maj`: at least half of the input bits are `1`. -/
def Maj : Lang := fun n x => decide (n ≤ 2 * ones x)

/-- `Mod_k`: `k` divides the number of ones. -/
def ModLang (k : ℕ) : Lang := fun _ x => decide (k ∣ ones x)

/-- `Primes`: the input, read in binary, is a prime number. -/
def Primes : Lang := fun _ x => decide (val x).Prime

/-- `Square-Free`: the input, read in binary, is not divisible by any perfect square `> 1`.
(In particular `0` is not square-free.) -/
def SquareFree : Lang := fun _ x => decide (Squarefree (val x))

/-- `GCD`: inputs of length `3m` encode a triple `(x, y, i)` of `m`-bit numbers; accept iff the
`i`-th bit of `gcd(x, y)` is `1`. -/
def GCD : Lang := fun n z =>
  decide (n % 3 = 0) &&
    (Nat.gcd (valFrom z 0 (n / 3)) (valFrom z (n / 3) (n / 3))).testBit (valFrom z (2 * (n / 3)) (n / 3))

/-- `p_j`, the `j`-th odd prime: `p_1 = 3, p_2 = 5, …` (so `p_j = nth Nat.Prime j`). -/
noncomputable def oddPrime (j : ℕ) : ℕ := nth Nat.Prime j

/-- `mult`: inputs of length `2m` encode a pair `(x, j)` of `m`-bit numbers; accept iff
`1 ≤ j ≤ m` and `p_j ∣ x`. -/
noncomputable def mult : Lang := fun n z =>
  decide (n % 2 = 0 ∧ 1 ≤ valFrom z (n / 2) (n / 2) ∧ valFrom z (n / 2) (n / 2) ≤ n / 2 ∧
    oddPrime (valFrom z (n / 2) (n / 2)) ∣ valFrom z 0 (n / 2))

/-- `TC⁰ = AC⁰[Maj]`. -/
def TC0 : Set Lang := AC0 Maj

/-! ### Basic facts about `p_j` -/

lemma oddPrime_prime (j : ℕ) : (oddPrime j).Prime := prime_nth_prime j

lemma oddPrime_strictMono : StrictMono oddPrime := nth_strictMono infinite_setOfPred_prime

lemma oddPrime_injective : Function.Injective oddPrime := oddPrime_strictMono.injective

lemma add_two_le_oddPrime (j : ℕ) : j + 2 ≤ oddPrime j := add_two_le_nth_prime j

lemma three_le_oddPrime {j : ℕ} (hj : 1 ≤ j) : 3 ≤ oddPrime j := by
  have := add_two_le_oddPrime j; omega

lemma oddPrime_one : oddPrime 1 = 3 := nth_prime_one_eq_three

lemma oddPrime_two : oddPrime 2 = 5 := nth_prime_two_eq_five

lemma oddPrime_le (j : ℕ) : oddPrime j ≤ 8 * (j + 1) ^ 2 := nth_prime_le j

lemma oddPrime_odd {j : ℕ} (hj : 1 ≤ j) : Odd (oddPrime j) :=
  (oddPrime_prime j).odd_of_ne_two (by have := three_le_oddPrime hj; omega)

lemma two_pow_pred_modEq_one {j : ℕ} (hj : 1 ≤ j) :
    2 ^ (oddPrime j - 1) ≡ 1 [MOD oddPrime j] := by
  have hp := oddPrime_prime j
  rw [← totient_prime hp]
  apply ModEq.pow_totient
  exact (Nat.coprime_primes prime_two hp).2 (by have := three_le_oddPrime hj; omega)

end PLB
