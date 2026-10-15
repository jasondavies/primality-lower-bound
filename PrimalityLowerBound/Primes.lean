import PrimalityLowerBound.MultWrapper
import PrimalityLowerBound.HittingSet
import PrimalityLowerBound.Adder
import PrimalityLowerBound.PageProof

/-!
# Lemma 5.2: `mult ≤ᵀ Primes`

Test whether `p ∣ x` by asking whether `x + p y` is prime for a few advice values `y ≥ 2`:
if `p ∣ x` then `x + p y` is a proper multiple of `p`; otherwise, by equation (1), a
`1/poly` fraction of the `y ∈ [2, 2^{N+1}]` (with `N = m + p + 1`) make `x + p y` prime, and by
the hitting-set lemma (Adleman's argument) a polynomial number of fixed `y` suffice for all `x`.

Deviation from the paper: we use `y ≥ 2` and no random sign `ε`, so that the query `x + p y` is
always positive and `≠ p`.
-/

namespace PLB

open Circuit

/-- Query length: `N + p + 2` with `N = m + p + 1`. -/
def prLen (m p : ℕ) : ℕ := m + 2 * p + 3

/-- The `Primes` oracle gate on `x + p y`, computed by the constant-depth adder. -/
noncomputable def primeGate (m p y : ℕ) : Circuit (2 * m) :=
  oracle (k := prLen m p) fun i => sumBitC (fun k => inBit m k) (p * y) i

lemma eval_primeGate {m p y : ℕ} (hy : y ≤ 2 ^ (m + p + 2)) (z : Fin (2 * m) → Bool) :
    (primeGate m p y).eval Primes z = decide (Nat.Prime (valFrom z 0 m + p * y)) := by
  set x := valFrom z 0 m
  have ha : ∀ k, (inBit m k : Circuit (2 * m)).eval Primes z = x.testBit k := by
    intro k
    rw [eval_inBit, show x = valFrom z 0 m from rfl, valFrom, testBit_bitsVal]
    simp
  have hlt : x + p * y < 2 ^ prLen m p := by
    have hx : x < 2 ^ (m + p + 2) :=
      (valFrom_lt z 0 m).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hp : p < 2 ^ p := Nat.lt_two_pow_self
    have : p * y ≤ 2 ^ p * 2 ^ (m + p + 2) := Nat.mul_le_mul hp.le hy
    calc x + p * y < 2 ^ (m + p + 2) + 2 ^ p * 2 ^ (m + p + 2) := by omega
      _ ≤ 2 ^ p * 2 ^ (m + p + 2) + 2 ^ p * 2 ^ (m + p + 2) := by
          gcongr; exact Nat.le_mul_of_pos_left _ (by positivity)
      _ = 2 ^ prLen m p := by unfold prLen; rw [← two_mul, ← pow_add, ← pow_succ']; ring_nf
  show Primes (prLen m p) _ = _
  rw [Primes]
  congr 2
  apply bitsVal_eq_of_testBit _ hlt
  intro i hi
  rw [getD_of_lt _ hi]
  exact eval_sumBitC ha i

lemma size_primeGate_le (m p y : ℕ) :
    (primeGate m p y).size ≤ prLen m p * (32 * prLen m p ^ 2) + 1 := by
  refine size_gate_le _ _ fun i => ?_
  refine (size_sumBitC_le (s := 1) (fun k => (size_inBit m k).le) i).trans ?_
  have : (i : ℕ) + 1 ≤ prLen m p := i.2
  have : ((i : ℕ) + 1) ^ 2 ≤ prLen m p ^ 2 := Nat.pow_le_pow_left this 2
  omega

lemma depth_primeGate_le (m p y : ℕ) : (primeGate m p y).depth ≤ 8 :=
  depth_gate_le _ _ fun i => (depth_sumBitC_le (d := 1) (fun k => depth_inBit_le m k) i)

/-- Every prime in the window yields an advice value `y ∈ [2, 2^{N+1}]` with `x + p y` prime. -/
lemma window_card_le {m p x : ℕ} (hp : 0 < p) (hx : x < 2 ^ m) :
    (primesWindow (m + p + 1) p (x % p)).card ≤
      ((Finset.Icc 2 (2 ^ (m + p + 2))).filter fun y => Nat.Prime (x + p * y)).card := by
  set N := m + p + 1
  apply Finset.card_le_card_of_injOn (fun q => (q - x) / p)
  · intro q hq
    simp only [primesWindow, Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq] at hq
    obtain ⟨⟨hq1, hq2⟩, hqp, hqmod⟩ := hq
    have h2N : 2 ^ N = 2 ^ m * 2 ^ (p + 1) := by rw [← pow_add]; rfl
    have hxq : x < q := by
      have : 2 ^ m ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hdvd : p ∣ q - x := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hqmod)
    have hpy : p * ((q - x) / p) = q - x := Nat.mul_div_cancel' hdvd
    have h2p : 2 * p ≤ q - x := by
      have h1 : 2 * p + 1 ≤ 2 ^ (p + 1) := by
        have := @Nat.lt_two_pow_self p; rw [pow_succ]; omega
      have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have : 2 ^ m * (2 * p + 1) ≤ 2 ^ N := by rw [h2N]; exact Nat.mul_le_mul_left _ h1
      have h3 : 2 ^ m * (2 * p + 1) = 2 ^ m * (2 * p) + 2 ^ m := by ring
      have h4 : 2 * p ≤ 2 ^ m * (2 * p) := Nat.le_mul_of_pos_left _ (by positivity)
      omega
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_contra h
      push Not at h
      have : p * ((q - x) / p) < p * 2 := Nat.mul_lt_mul_of_pos_left h hp
      omega
    · calc (q - x) / p ≤ q - x := Nat.div_le_self _ _
        _ ≤ 2 ^ (N + 1) := by omega
    · rw [hpy, Nat.add_sub_cancel' hxq.le]; exact hqp
  · intro q₁ hq₁ q₂ hq₂ heq
    simp only [primesWindow, Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq] at hq₁ hq₂
    have hx1 : x < q₁ := by
      have : 2 ^ m ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hx2 : x < q₂ := by
      have : 2 ^ m ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h1 := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hq₁.2.2))
    have h2 := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hq₂.2.2))
    simp only at heq
    rw [heq] at h1
    omega

/-- **Lemma 5.2.** `mult ≤ᵀ Primes`, using the proved Page estimate. -/
theorem mult_reduces_primes : mult ≤ᵀ Primes := by
  obtain ⟨N₀, hN₀⟩ := primesWindow_lower_bound
  refine mult_reduces_of 10 45 (N₀ + 1) fun m hm j hj1 hjm => ?_
  set p := oddPrime j
  have hp : p.Prime := oddPrime_prime j
  have hp3 : 3 ≤ p := three_le_oddPrime hj1
  set N := m + p + 1
  set K := 4 * (N + 1) * p
  set X := (Finset.range (2 ^ m)).filter fun x => ¬ p ∣ x
  set Y := Finset.Icc 2 (2 ^ (N + 1))
  have hYne : Y.Nonempty := ⟨2, by
    simp only [Y, Finset.mem_Icc, le_refl, true_and]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)⟩
  have hdens : ∀ x ∈ X, Y.card ≤ K * (Y.filter fun y => Nat.Prime (x + p * y)).card := by
    intro x hx
    simp only [X, Finset.mem_filter, Finset.mem_range] at hx
    have hl : 1 ≤ x % p := by
      rcases Nat.eq_zero_or_pos (x % p) with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) hx.2
      · exact h
    have hw := hN₀ N (by omega) p (x % p) hp hl (Nat.mod_lt _ hp.pos) (by omega)
    have hc := window_card_le hp.pos hx.1
    have hY : Y.card ≤ 2 * 2 ^ N := by
      simp only [Y, Nat.card_Icc]
      have : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ, mul_comm]
      omega
    calc Y.card ≤ 2 * 2 ^ N := hY
      _ ≤ 2 * (2 * (N + 1) * p * (primesWindow N p (x % p)).card) := by omega
      _ ≤ 2 * (2 * (N + 1) * p * (Y.filter fun y => Nat.Prime (x + p * y)).card) := by
          gcongr
      _ = K * (Y.filter fun y => Nat.Prime (x + p * y)).card := by simp only [K]; ring
  obtain ⟨ys, hlen, hysY, hhit⟩ := exists_hitting_list X Y hYne
    (fun x y => Nat.Prime (x + p * y)) K m (by positivity)
    ((Finset.card_filter_le _ _).trans (by simp)) hdens
  have hyb : ∀ y ∈ ys, 2 ≤ y ∧ y ≤ 2 ^ (m + p + 2) := fun y hy => by
    have := hysY y hy
    simp only [Y, Finset.mem_Icc] at this
    exact this
  refine ⟨adviceDiv (primeGate m p) ys,
    (depth_adviceDiv_le _ _ fun y => depth_primeGate_le m p y).trans (by omega), ?_, ?_⟩
  · -- size bookkeeping
    set P := m + 2
    have hP : 3 ≤ P := by omega
    have hp8 : p ≤ 8 * P ^ 2 := (oddPrime_le j).trans (by gcongr; omega)
    have hP2 : 1 ≤ P ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hPP : P ≤ P ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left _ (by omega)
    have hlenP : prLen m p ≤ 17 * P ^ 2 := by
      unfold prLen
      have : m + 3 ≤ P ^ 2 := by simp only [P] at hPP ⊢; nlinarith
      omega
    have hgate : ∀ y, (primeGate m p y).size ≤ 2 * 32 * 17 ^ 3 * P ^ 6 := by
      intro y
      refine (size_primeGate_le m p y).trans ?_
      have h1 : prLen m p ^ 2 ≤ (17 * P ^ 2) ^ 2 := Nat.pow_le_pow_left hlenP 2
      have h2 : prLen m p * (32 * prLen m p ^ 2) ≤ (17 * P ^ 2) * (32 * (17 * P ^ 2) ^ 2) :=
        Nat.mul_le_mul hlenP (Nat.mul_le_mul_left _ h1)
      have h3 : (17 * P ^ 2) * (32 * (17 * P ^ 2) ^ 2) = 32 * 17 ^ 3 * P ^ 6 := by ring
      have h4 : 1 ≤ P ^ 6 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have hlenK : ys.length ≤ 4 * (9 * P ^ 2) * (8 * P ^ 2) * P := by
      refine hlen.trans ?_
      simp only [K]
      have : N + 1 ≤ 9 * P ^ 2 := by simp only [N]; omega
      gcongr; omega
    have hc : (4 * (9 * P ^ 2) * (8 * P ^ 2) * P) * (2 * 32 * 17 ^ 3 * P ^ 6) + 2 ≤
        2 ^ 30 * P ^ 11 := by
      have : (4 * (9 * P ^ 2) * (8 * P ^ 2) * P) * (2 * 32 * 17 ^ 3 * P ^ 6) =
          (4 * 9 * 8 * 2 * 32 * 17 ^ 3) * P ^ 11 := by ring
      have h1 : 1 ≤ P ^ 11 := Nat.one_le_pow _ _ (by omega)
      rw [this]; norm_num; omega
    have h30 : 2 ^ 30 ≤ P ^ 30 := Nat.pow_le_pow_left (by omega) 30
    calc (adviceDiv (primeGate m p) ys).size ≤ ys.length * (2 * 32 * 17 ^ 3 * P ^ 6) + 2 :=
          size_adviceDiv_le _ _ hgate
      _ ≤ (4 * (9 * P ^ 2) * (8 * P ^ 2) * P) * (2 * 32 * 17 ^ 3 * P ^ 6) + 2 := by gcongr
      _ ≤ 2 ^ 30 * P ^ 11 := hc
      _ ≤ P ^ 30 * P ^ 11 := Nat.mul_le_mul_right _ h30
      _ ≤ P ^ 45 := by rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  · refine eval_adviceDiv _ ys (fun x y => Nat.Prime (x + p * y))
      (fun y hy z => eval_primeGate (hyb y hy).2 z) ?_ ?_
    · intro x _ y hy hpx hprime
      have hd : p ∣ x + p * y := dvd_add hpx (dvd_mul_right _ _)
      rcases hprime.eq_one_or_self_of_dvd p hd with h | h
      · omega
      · have : 2 * p ≤ p * y := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (hyb y hy).1
        omega
    · intro x hx hpx
      exact hhit x (by simp [X, hx, hpx])

end PLB
