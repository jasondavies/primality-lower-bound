import PrimalityLowerBound.MultWrapper
import PrimalityLowerBound.HittingSet
import PrimalityLowerBound.SquareFreeCount

/-!
# Lemma 5.3: `mult ≤ᵀ Square-Free`

Deviation from the paper (which uses `p x + ε p² y` and the analytic estimate (2)): the AC⁰ part
must multiply `x` by `p`, which we avoid as follows.  With `L = p (p - 1)` we have
`2^L ≡ 1 (mod p²)`, so the number
`h(x) = p² + ∑_{i < m} xᵢ (p 2ⁱ mod p²) 2^{L (i+1)}`
is obtained from `x` by pure wiring (the summands occupy disjoint blocks of `L` bits), is odd, and
satisfies `h(x) ≡ p x (mod p²)`.  We query `h(x) + 2^M p² y` (the advice `y` occupies the high
bits; again wiring).  If `p ∣ x` this is divisible by `p²`; otherwise at least a quarter of the
`y` make it square-free (`squarefree_density`).
-/

namespace PLB

open Circuit

/-- Block width `L = p (p - 1)`. -/
def sfL (p : ℕ) : ℕ := p * (p - 1)

/-- `aᵢ = p 2ⁱ mod p²`. -/
def sfA (p i : ℕ) : ℕ := (p * 2 ^ i) % p ^ 2

/-- Number of low bits used by `h(x)`. -/
def sfM (p m : ℕ) : ℕ := sfL p * (m + 1)

/-- The advice `y` ranges below `2 ^ sfE p m`. -/
def sfE (p m : ℕ) : ℕ := sfM p m + 2 * p + 7

/-- Length of the query. -/
def sfQ (p m : ℕ) : ℕ := sfM p m + (sfE p m + 2 * p)

/-- Bit `s` of `h(x)`. -/
def sfHBit (p x s : ℕ) : Bool :=
  if s / sfL p = 0 then (p ^ 2).testBit (s % sfL p)
  else x.testBit (s / sfL p - 1) && (sfA p (s / sfL p - 1)).testBit (s % sfL p)

/-- `h(x)`. -/
def sfH (p m x : ℕ) : ℕ := bitsVal (sfHBit p x) (sfM p m)

lemma sq_lt_two_pow_two_mul (p : ℕ) : p ^ 2 < 2 ^ (2 * p) := by
  have h1 : p ^ 2 < (2 ^ p) ^ 2 := Nat.pow_lt_pow_left Nat.lt_two_pow_self (by norm_num)
  calc p ^ 2 < (2 ^ p) ^ 2 := h1
    _ = 2 ^ (2 * p) := by rw [← pow_mul, mul_comm]

lemma sq_lt_two_pow_sfL {p : ℕ} (hp3 : 3 ≤ p) : p ^ 2 < 2 ^ sfL p := by
  have h2 : p * 2 ≤ p * (p - 1) := Nat.mul_le_mul_left p (by omega)
  calc p ^ 2 < 2 ^ (2 * p) := sq_lt_two_pow_two_mul p
    _ ≤ 2 ^ sfL p := Nat.pow_le_pow_right (by norm_num) (by unfold sfL; omega)

lemma sfL_pos {p : ℕ} (hp3 : 3 ≤ p) : 0 < sfL p := by unfold sfL; apply Nat.mul_pos <;> omega

lemma sfH_lt (p m x : ℕ) : sfH p m x < 2 ^ sfM p m := bitsVal_lt _ _

section facts

variable {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
include hp hp3

omit hp in
lemma sfH_eq (m x : ℕ) :
    sfH p m x = p ^ 2 + ∑ b ∈ Finset.range m, 2 ^ (sfL p * (b + 1)) * ((x.testBit b).toNat * sfA p b) := by
  have hL := sfL_pos hp3
  have hsq := sq_lt_two_pow_sfL hp3
  rw [sfH, sfM, bitsVal_blocks, Finset.sum_range_succ', add_comm]
  congr 1
  · rw [mul_zero, pow_zero, one_mul]
    apply bitsVal_eq_of_testBit _ hsq
    intro t ht
    simp only [sfHBit, zero_add, Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, ite_true]
  · refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    apply bitsVal_eq_of_testBit
    · intro t ht
      have hdiv : (sfL p * (b + 1) + t) / sfL p = b + 1 := by
        rw [Nat.mul_add_div hL, Nat.div_eq_of_lt ht, add_zero]
      have hmod : (sfL p * (b + 1) + t) % sfL p = t := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
      simp only [sfHBit, hdiv, hmod, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]
      cases x.testBit b <;> simp
    · calc (x.testBit b).toNat * sfA p b ≤ 1 * sfA p b := Nat.mul_le_mul_right _ (Bool.toNat_le _)
        _ < 2 ^ sfL p := by
          rw [one_mul]; exact (Nat.mod_lt _ (by positivity)).trans hsq

lemma two_pow_sfL_eq_one : (2 : ZMod (p ^ 2)) ^ sfL p = 1 := by
  have hcop : Nat.Coprime 2 (p ^ 2) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime_pow hp (by norm_num), pow_one] at h
  have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
  push_cast at this
  rw [sfL]; exact this

lemma sfH_cast {m x : ℕ} (hx : x < 2 ^ m) : (sfH p m x : ZMod (p ^ 2)) = p * x := by
  have hx' : x = ∑ b ∈ Finset.range m, (x.testBit b).toNat * 2 ^ b := by
    rw [← bitsVal_eq_sum]
    exact (bitsVal_eq_of_testBit (fun i _ => rfl) hx).symm
  have h2 := two_pow_sfL_eq_one hp hp3
  rw [sfH_eq hp3]
  conv_rhs => rw [hx']
  push_cast
  have hp2 : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hp2, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sfA, ZMod.natCast_mod, pow_mul, h2, one_pow, one_mul]
  push_cast; ring

lemma sfH_odd (m x : ℕ) : sfH p m x % 2 = 1 := by
  have hL := sfL_pos hp3
  have h := testBit_bitsVal (sfHBit p x) (sfM p m) 0
  have hM : 0 < sfM p m := by unfold sfM; positivity
  have hpo : (p ^ 2) % 2 = 1 := by
    have : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two (by omega))
    simp [Nat.pow_mod, this]
  rw [← sfH, Nat.testBit_zero] at h
  simp only [hM, decide_true, Bool.true_and, sfHBit, Nat.zero_div, Nat.zero_mod, ite_true,
    Nat.testBit_zero, hpo] at h
  exact of_decide_eq_true h

lemma sq_dvd_sfH_iff {m x : ℕ} (hx : x < 2 ^ m) : p ^ 2 ∣ sfH p m x ↔ p ∣ x := by
  rw [← ZMod.natCast_eq_zero_iff, sfH_cast hp hp3 hx, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff,
    sq]
  exact Nat.mul_dvd_mul_iff_left hp.pos

end facts

/-! ### The circuit -/

/-- Bit `s` of the query `h(x) + 2^M p² y`. -/
noncomputable def sfQBit (p m y s : ℕ) : Circuit (2 * m) :=
  if s < sfM p m then
    if s / sfL p = 0 then const ((p ^ 2).testBit (s % sfL p))
    else if (sfA p (s / sfL p - 1)).testBit (s % sfL p) then inBit m (s / sfL p - 1)
      else const false
  else const ((p ^ 2 * y).testBit (s - sfM p m))

/-- The `Square-Free` oracle gate on `h(x) + 2^M p² y`. -/
noncomputable def sfGate (p m y : ℕ) : Circuit (2 * m) :=
  oracle (k := sfQ p m) fun s => sfQBit p m y s

lemma eval_sfGate {p m y : ℕ} (hp3 : 3 ≤ p) (hy : y < 2 ^ sfE p m)
    (z : Fin (2 * m) → Bool) :
    (sfGate p m y).eval SquareFree z =
      decide (Squarefree (sfH p m (valFrom z 0 m) + 2 ^ sfM p m * p ^ 2 * y)) := by
  set x := valFrom z 0 m
  set Yv : Fin (sfQ p m) → Bool := fun s => (sfQBit p m y s).eval SquareFree z
  have hL := sfL_pos hp3
  have hval : val Yv = sfH p m x + 2 ^ sfM p m * p ^ 2 * y := by
    show bitsVal (getD Yv) (sfM p m + (sfE p m + 2 * p)) = _
    rw [bitsVal_add, mul_assoc]
    congr 1
    · apply bitsVal_congr
      intro s hs
      rw [getD_of_lt Yv (by unfold sfQ; omega)]
      simp only [Yv, sfQBit, ite_eq_left hs]
      by_cases h0 : s / sfL p = 0
      · simp [sfHBit, h0]
      · have hb : s / sfL p - 1 < m := by
          have : s / sfL p < m + 1 := Nat.div_lt_of_lt_mul (by unfold sfM at hs; exact hs)
          generalize s / sfL p = b at h0 this ⊢
          omega
        have hxb : getD z (s / sfL p - 1) = x.testBit (s / sfL p - 1) := by
          rw [show x = valFrom z 0 m from rfl, valFrom, testBit_bitsVal]; simp [hb]
        simp only [sfHBit, h0, ite_false]
        split
        · next ha => simp [hb, hxb, ha]
        · next ha => simp [ha]
    · congr 1
      apply bitsVal_eq_of_testBit
      · intro t ht
        rw [getD_of_lt Yv (by unfold sfQ; omega)]
        simp only [Yv, sfQBit, ite_eq_right (show ¬ (sfM p m + t < sfM p m) by omega), eval_const]
        congr 1; omega
      · calc p ^ 2 * y < 2 ^ (2 * p) * 2 ^ sfE p m := by
              apply Nat.mul_lt_mul_of_lt_of_le (sq_lt_two_pow_two_mul p) hy.le
              positivity
          _ = 2 ^ (sfE p m + 2 * p) := by rw [← pow_add, add_comm]
  show SquareFree (sfQ p m) Yv = _
  rw [SquareFree, hval]

lemma size_sfGate_le (p m y : ℕ) : (sfGate p m y).size ≤ sfQ p m + 1 := by
  refine (size_gate_le _ _ (s := 1) fun s => ?_).trans (by simp)
  simp only [sfQBit]; split_ifs <;> simp [size_inBit, size_const]

lemma depth_sfGate_le (p m y : ℕ) : (sfGate p m y).depth ≤ 2 := by
  refine depth_gate_le _ _ fun s => ?_
  simp only [sfQBit]; split_ifs
  · exact depth_const _
  · exact depth_inBit_le _ _
  · exact depth_const _
  · exact depth_const _

lemma sfQ_le {p m : ℕ} (hp : p ≤ 8 * (m + 1) ^ 2) : sfQ p m ≤ (m + 2) ^ 13 := by
  set P := m + 2
  have hP : 2 ≤ P := by omega
  have hp' : p ≤ 8 * P ^ 2 := hp.trans (by gcongr; omega)
  have hL : sfL p ≤ 64 * P ^ 4 := by
    calc sfL p ≤ p * p := by unfold sfL; exact Nat.mul_le_mul_left _ (by omega)
      _ ≤ (8 * P ^ 2) * (8 * P ^ 2) := Nat.mul_le_mul hp' hp'
      _ = 64 * P ^ 4 := by ring
  have hM : sfM p m ≤ 64 * P ^ 5 := by
    calc sfM p m ≤ 64 * P ^ 4 * P := by unfold sfM; exact Nat.mul_le_mul hL (by omega)
      _ = 64 * P ^ 5 := by ring
  have hP2 : P ^ 2 ≤ P ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1 : 1 ≤ P ^ 5 := Nat.one_le_pow _ _ (by omega)
  have h256 : 256 ≤ P ^ 8 := by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ P ^ 8 := Nat.pow_le_pow_left hP 8
  calc sfQ p m = 2 * sfM p m + 4 * p + 7 := by unfold sfQ sfE; ring
    _ ≤ 2 * (64 * P ^ 5) + 4 * (8 * P ^ 5) + 7 * P ^ 5 := by
        have : 8 * P ^ 2 ≤ 8 * P ^ 5 := by omega
        omega
    _ = 167 * P ^ 5 := by ring
    _ ≤ P ^ 8 * P ^ 5 := Nat.mul_le_mul_right _ (by omega)
    _ = P ^ 13 := by ring

/-- **Lemma 5.3.** `mult ≤ᵀ Square-Free` (unconditionally). -/
theorem mult_reduces_squarefree : mult ≤ᵀ SquareFree := by
  refine mult_reduces_of 4 18 1 fun m hm j hj1 hjm => ?_
  set p := oddPrime j
  have hp : p.Prime := oddPrime_prime j
  have hp3 : 3 ≤ p := three_le_oddPrime hj1
  set M := sfM p m
  set E := sfE p m
  have hL := sfL_pos hp3
  have hM1 : 1 ≤ M := by unfold M sfM; nlinarith
  have hE : E = M + 2 * p + 7 := rfl
  -- advice selection
  set X := (Finset.range (2 ^ m)).filter fun x => ¬ p ∣ x
  set Y := Finset.range (2 ^ E)
  have hYne : Y.Nonempty := ⟨0, by simp [Y]⟩
  have hdens : ∀ x ∈ X, Y.card ≤ 4 * (Y.filter fun y =>
      Squarefree (sfH p m x + 2 ^ M * p ^ 2 * y)).card := by
    intro x hx
    simp only [X, Finset.mem_filter, Finset.mem_range] at hx
    have := squarefree_density p M (sfH p m x) (2 ^ E) (2 ^ (E - 3)) hp hp3 hM1
      (sfH_lt p m x) (sfH_odd hp hp3 m x)
      (by rw [sq_dvd_sfH_iff hp hp3 hx.1]; exact hx.2) ?_ ?_
    · simpa [Y] using this
    · calc 2 ^ M * p ^ 2 * 2 ^ E ≤ 2 ^ M * 2 ^ (2 * p) * 2 ^ E :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (sq_lt_two_pow_two_mul p).le)
        _ = 2 ^ (M + 2 * p + E) := by rw [← pow_add, ← pow_add]
        _ ≤ 2 ^ ((E - 3) + (E - 3)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ (E - 3) * 2 ^ (E - 3) := pow_add _ _ _
    · rw [show 8 = 2 ^ 3 by norm_num, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨ys, hlen, hysY, hhit⟩ := exists_hitting_list X Y hYne
    (fun x y => Squarefree (sfH p m x + 2 ^ M * p ^ 2 * y)) 4 m (by norm_num)
    ((Finset.card_filter_le _ _).trans (by simp)) hdens
  refine ⟨adviceDiv (sfGate p m) ys,
    (depth_adviceDiv_le _ _ fun y => depth_sfGate_le p m y).trans (by omega), ?_, ?_⟩
  · have hQ : sfQ p m ≤ (m + 2) ^ 13 := sfQ_le ((oddPrime_le j).trans (by gcongr))
    set P := m + 2
    have hP : 3 ≤ P := by omega
    have h1 : 1 ≤ P ^ 13 := Nat.one_le_pow _ _ (by omega)
    have h9 : 9 ≤ P ^ 2 := by nlinarith
    calc (adviceDiv (sfGate p m) ys).size ≤ ys.length * (P ^ 13 + 1) + 2 :=
          size_adviceDiv_le _ _ fun y => (size_sfGate_le _ _ _).trans (by omega)
      _ ≤ (4 * (m + 1)) * (P ^ 13 + 1) + 2 := by gcongr
      _ ≤ (4 * P) * (2 * P ^ 13) + P ^ 14 := by
          have : 2 ≤ P ^ 14 := by
            calc 2 ≤ P := by omega
              _ = P ^ 1 := (pow_one P).symm
              _ ≤ P ^ 14 := Nat.pow_le_pow_right (by omega) (by norm_num)
          gcongr <;> omega
      _ = 9 * P ^ 14 := by ring
      _ ≤ P ^ 2 * P ^ 14 := Nat.mul_le_mul_right _ h9
      _ ≤ P ^ 18 := by rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  · refine eval_adviceDiv _ ys (fun x y => Squarefree (sfH p m x + 2 ^ M * p ^ 2 * y))
      (fun y hy z => eval_sfGate hp3 (by simpa [Y] using hysY y hy) z) ?_ ?_
    · intro x hx y _ hpx hsq
      rw [Nat.squarefree_iff_prime_squarefree] at hsq
      apply hsq p hp
      rw [← sq]
      exact dvd_add ((sq_dvd_sfH_iff hp hp3 hx).2 hpx) (Dvd.dvd.mul_right (dvd_mul_left _ _) _)
    · intro x hx hpx
      exact hhit x (by simp [X, hx, hpx])

end PLB
