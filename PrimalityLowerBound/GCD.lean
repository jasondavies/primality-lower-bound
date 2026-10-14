import PrimalityLowerBound.MultWrapper

/-!
# Lemma 5.1: `mult ≤ᵀ GCD`

`p ∣ x` iff `gcd(x, p) = p` iff every bit of `gcd(x, p)` agrees with the corresponding bit of `p`;
each bit of `gcd(x, p)` is one `GCD` oracle query.
-/

namespace PLB

open Circuit

/-- Bit `s` of the `GCD` query `(x, p, i)` with all three fields of width `w`. -/
noncomputable def gcdQuery (m w p i : ℕ) (s : ℕ) : Circuit (2 * m) :=
  if s < w then inBit m s
  else if s < 2 * w then const (p.testBit (s - w))
  else const (i.testBit (s - 2 * w))

/-- The oracle gate returning bit `i` of `gcd(x, p)`. -/
noncomputable def gcdGate (m w p i : ℕ) : Circuit (2 * m) :=
  oracle (k := 3 * w) fun s => gcdQuery m w p i s

lemma eval_gcdGate (m w p i : ℕ) (hmw : m ≤ w) (hp : p < 2 ^ w) (hi : i < 2 ^ w)
    (z : Fin (2 * m) → Bool) :
    (gcdGate m w p i).eval GCD z = (Nat.gcd (valFrom z 0 m) p).testBit i := by
  set y : Fin (3 * w) → Bool := fun s => (gcdQuery m w p i s).eval GCD z
  have h0 : valFrom y 0 w = valFrom z 0 m := by
    apply bitsVal_eq_of_testBit
    · intro s hs
      rw [zero_add, getD_of_lt y (by omega)]
      simp only [y, gcdQuery, ite_eq_left hs, eval_inBit]
      rw [valFrom, testBit_bitsVal]; simp
    · exact (valFrom_lt z 0 m).trans_le (Nat.pow_le_pow_right (by omega) hmw)
  have h1 : valFrom y w w = p := by
    apply bitsVal_eq_of_testBit
    · intro s hs
      rw [getD_of_lt y (by omega)]
      simp only [y, gcdQuery, ite_eq_right (show ¬ (w + s < w) by omega),
        ite_eq_left (show w + s < 2 * w by omega), eval_const]
      congr 1; omega
    · exact hp
  have h2 : valFrom y (2 * w) w = i := by
    apply bitsVal_eq_of_testBit
    · intro s hs
      rw [getD_of_lt y (by omega)]
      simp only [y, gcdQuery, ite_eq_right (show ¬ (2 * w + s < w) by omega),
        ite_eq_right (show ¬ (2 * w + s < 2 * w) by omega), eval_const]
      congr 1; omega
    · exact hi
  show GCD (3 * w) y = _
  simp only [GCD, Nat.mul_mod_right, show 3 * w / 3 = w by omega, decide_true, Bool.true_and,
    h0, h1, h2]

/-- Circuit deciding `p ∣ x` with `GCD` gates. -/
noncomputable def gcdDiv (m w p : ℕ) : Circuit (2 * m) :=
  and (k := w) fun i => if p.testBit i then gcdGate m w p i else not (gcdGate m w p i)

lemma eval_gcdDiv (m w p : ℕ) (hp0 : 0 < p) (hmw : m ≤ w) (hp : p < 2 ^ w)
    (z : Fin (2 * m) → Bool) :
    (gcdDiv m w p).eval GCD z = decide (p ∣ valFrom z 0 m) := by
  have hiw : ∀ i : Fin w, (i : ℕ) < 2 ^ w := fun i => i.2.trans Nat.lt_two_pow_self
  have hbit : ∀ i : Fin w, ((if p.testBit i then gcdGate m w p i else not (gcdGate m w p i)).eval
      GCD z = true ↔ (Nat.gcd (valFrom z 0 m) p).testBit i = p.testBit i) := by
    intro i
    split <;> simp_all [eval_gcdGate m w p i hmw hp (hiw i)]
  rw [gcdDiv, eval_and, decide_eq_decide, ← Nat.gcd_eq_right_iff_dvd]
  simp only [hbit]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w
    · exact h ⟨i, hi⟩
    · have hg : Nat.gcd (valFrom z 0 m) p < 2 ^ i :=
        (Nat.gcd_le_right _ hp0).trans_lt (hp.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [Nat.testBit_lt_two_pow hg,
        Nat.testBit_lt_two_pow (hp.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))]
  · intro h i; rw [h]

lemma size_gcdDiv_le (m w p : ℕ) : (gcdDiv m w p).size ≤ w * (3 * w + 2) + 1 := by
  refine size_and_le _ fun i => ?_
  have hg : (gcdGate m w p i).size ≤ 3 * w + 1 := by
    refine (size_oracle_le _ (s := 1) fun s => ?_).trans (by simp)
    simp only [gcdQuery]; split_ifs <;> simp [size_inBit, size_const]
  split
  · omega
  · simp only [size]; omega

lemma depth_gcdDiv_le (m w p : ℕ) : (gcdDiv m w p).depth ≤ 4 := by
  refine (depth_and_le _ (d := 3) fun i => ?_)
  have hg : (gcdGate m w p i).depth ≤ 2 := by
    refine depth_oracle_le _ fun s => ?_
    simp only [gcdQuery]; split_ifs
    · exact depth_inBit_le _ _
    · exact depth_const _
    · exact depth_const _
  split
  · omega
  · simp only [depth]; omega

/-- **Lemma 5.1.** `mult ≤ᵀ GCD`. -/
theorem mult_reduces_gcd : mult ≤ᵀ GCD := by
  refine mult_reduces_of 4 12 1 fun m hm j hj1 hjm => ?_
  set p := oddPrime j
  set w := m + p
  have hp0 : 0 < p := (oddPrime_prime j).pos
  have hp : p < 2 ^ w := Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  refine ⟨gcdDiv m w p, depth_gcdDiv_le m w p, ?_, eval_gcdDiv m w p hp0 (by omega) hp⟩
  have hw : w ≤ (m + 2) ^ 4 := by
    have h1 : p ≤ 8 * (m + 1) ^ 2 := (oddPrime_le j).trans (by gcongr)
    have h2 : 9 ≤ (m + 2) ^ 2 := by nlinarith
    have h3 : (m + 2) ^ 4 = (m + 2) ^ 2 * (m + 2) ^ 2 := by ring
    have h4 : m + 8 * (m + 1) ^ 2 ≤ 9 * (m + 2) ^ 2 := by nlinarith
    calc w ≤ m + 8 * (m + 1) ^ 2 := by omega
      _ ≤ 9 * (m + 2) ^ 2 := h4
      _ ≤ (m + 2) ^ 2 * (m + 2) ^ 2 := Nat.mul_le_mul_right _ h2
      _ = (m + 2) ^ 4 := h3.symm
  refine (size_gcdDiv_le m w p).trans ?_
  have h5 : 5 ≤ (m + 2) ^ 4 := by
    have : 2 ^ 4 ≤ (m + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  calc w * (3 * w + 2) + 1 ≤ (m + 2) ^ 4 * (5 * (m + 2) ^ 4) := by
        have : 1 ≤ w := by omega
        nlinarith
    _ ≤ (m + 2) ^ 4 * ((m + 2) ^ 4 * (m + 2) ^ 4) := by gcongr
    _ = (m + 2) ^ 12 := by ring

end PLB
