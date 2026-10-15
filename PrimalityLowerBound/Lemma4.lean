import PrimalityLowerBound.Languages

/-!
# Lemma 4: `Maj ≤ᵀ mult`

Chinese remaindering plus the observation of Boppana and Lagarias: spreading the bits of `x`
`u = p - 1` positions apart gives a number congruent to the number of ones of `x` modulo `p`.

Deviation from the paper: instead of computing `f_j(x) - r` (which needs a subtractor and may be
negative) we append `p_j - r` ones to `x`, which is pure wiring.
-/

namespace PLB

open Circuit

/-- Length of the `x`-part of the `mult` query for `M_{j,r}` on `n` input bits. -/
noncomputable def resLen (n j r : ℕ) : ℕ := (oddPrime j - 1) * (n + (oddPrime j - r))

/-- Bit `i` of the `mult` query computing `M_{j,r}`: the `x`-part is `f_j(x 1^{p_j - r})` and the
`j`-part is `j` in binary. -/
noncomputable def resQuery (n j r : ℕ) (i : ℕ) : Circuit n :=
  if i < resLen n j r then
    if i % (oddPrime j - 1) = 0 then
      if h : i / (oddPrime j - 1) < n then input ⟨i / (oddPrime j - 1), h⟩ else const true
    else const false
  else const (j.testBit (i - resLen n j r))

/-- A single `mult` oracle gate computing `M_{j,r}(x)`, i.e. `#ones(x) ≡ r (mod p_j)`. -/
noncomputable def resGate (n j r : ℕ) : Circuit n :=
  oracle (k := 2 * resLen n j r) fun i => resQuery n j r i

lemma testBit_toNat (b : Bool) (s : ℕ) : b.toNat.testBit s = (decide (s = 0) && b) := by
  cases b <;> cases s <;> simp [Nat.testBit_succ]

lemma mod_add_sub_dvd_iff {a p r : ℕ} (hr : r < p) : p ∣ a + (p - r) ↔ a % p = r := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  have hs : a % p < p := Nat.mod_lt _ (by omega)
  have hpr : (p - r) % p = p - r ∨ r = 0 := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.mod_eq_of_lt (by omega))
  rcases hpr with h | rfl
  · rw [h]
    by_cases hle : r ≤ a % p
    · rw [show a % p + (p - r) = (a % p - r) + p by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp

lemma eval_resGate (n j r : ℕ) (hj : 1 ≤ j) (hr : r < oddPrime j) (z : Fin n → Bool) :
    (resGate n j r).eval mult z = decide (ones z % oddPrime j = r) := by
  set p := oddPrime j with hp
  set u := p - 1 with hu
  set m := resLen n j r with hm
  have hp3 : 3 ≤ p := three_le_oddPrime hj
  have hjp : j + 2 ≤ p := add_two_le_oddPrime j
  have hm' : m = u * (n + (p - r)) := rfl
  have hjm : j ≤ m := by
    have h1 : 1 ≤ n + (p - r) := by omega
    calc j ≤ u * 1 := by omega
      _ ≤ u * (n + (p - r)) := Nat.mul_le_mul_left _ h1
      _ = m := hm'.symm
  set y : Fin (2 * m) → Bool := fun i => (resQuery n j r i).eval mult z with hy
  have hgate : (resGate n j r).eval mult z = mult (2 * m) y := rfl
  -- the `j` part
  have hJ : valFrom y m m = j := by
    apply bitsVal_eq_of_testBit
    · intro i hi
      rw [getD_of_lt y (by omega)]
      simp only [y, resQuery, ← hm]
      rw [ite_eq_right (by omega), eval_const]
      congr 1; omega
    · calc j ≤ m := hjm
        _ < 2 ^ m := Nat.lt_two_pow_self
  -- the `x` part
  set x' : ℕ → Bool := fun b => if b < n then getD z b else true with hx'
  have hblock : ∀ b < n + (p - r), bitsVal (fun s => getD y (0 + (u * b + s))) u = (x' b).toNat := by
    intro b hb
    apply bitsVal_eq_of_testBit
    · intro s hs
      have hlt : u * b + s < m := by
        rw [hm']
        calc u * b + s < u * b + u := by omega
          _ = u * (b + 1) := by ring
          _ ≤ u * (n + (p - r)) := Nat.mul_le_mul_left _ (by omega)
      rw [zero_add, getD_of_lt y (by omega), testBit_toNat]
      simp only [y, resQuery, ← hm, ← hp, ← hu]
      rw [ite_eq_left hlt]
      have hmod : (u * b + s) % u = s := by
        rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hs
      have hdiv : (u * b + s) / u = b := by
        rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hs]; simp
      rw [hmod]
      by_cases hs0 : s = 0
      · subst hs0
        simp only [hdiv, ite_true, decide_true, Bool.true_and, x']
        by_cases hbn : b < n
        · rw [dite_eq_left hbn, ite_eq_left hbn, getD_of_lt z hbn]; rfl
        · rw [dite_eq_right hbn, ite_eq_right hbn, eval_const]
      · simp [hs0]
    · calc (x' b).toNat ≤ 1 := Bool.toNat_le _
        _ < 2 ^ u := Nat.one_lt_two_pow (by omega)
  have hX : valFrom y 0 m = ∑ b ∈ Finset.range (n + (p - r)), 2 ^ (u * b) * (x' b).toNat := by
    unfold valFrom
    conv_lhs => arg 2; rw [hm']
    rw [bitsVal_blocks]
    exact Finset.sum_congr rfl fun b hb => by rw [hblock b (Finset.mem_range.1 hb)]
  have hsum : ∑ b ∈ Finset.range (n + (p - r)), (x' b).toNat = ones z + (p - r) := by
    rw [Finset.sum_range_add, ones_eq_sum]
    congr 1
    · exact Finset.sum_congr rfl fun b hb => by
        simp [x', Finset.mem_range.1 hb]
    · simp [x']
  have hcong : (valFrom y 0 m : ZMod p) = ((ones z + (p - r) : ℕ) : ZMod p) := by
    have h2u : ((2 : ℕ) : ZMod p) ^ u = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (two_pow_pred_modEq_one hj)
      simpa [← hp, ← hu] using this
    rw [hX, ← hsum]
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [pow_mul]
    have : (2 : ZMod p) ^ u = 1 := by exact_mod_cast h2u
    rw [this, one_pow, one_mul]
  have hdvd : p ∣ valFrom y 0 m ↔ ones z % p = r := by
    rw [← mod_add_sub_dvd_iff hr, ← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, hcong]
  rw [hgate]
  simp only [mult, Nat.mul_mod_right, show 2 * m / 2 = m by omega, hJ, ← hp, hdvd]
  simp [hj, hjm]

lemma size_resGate_le (n j r : ℕ) : (resGate n j r).size ≤ 2 * resLen n j r + 1 := by
  refine (size_gate_le _ _ (s := 1) fun i => ?_).trans (by simp)
  simp only [resQuery]
  split_ifs <;> simp [size, size_const]

lemma depth_resGate_le (n j r : ℕ) : (resGate n j r).depth ≤ 2 := by
  refine depth_gate_le _ _ fun i => ?_
  simp only [resQuery]
  split_ifs <;> simp [depth, depth_const]

/-! ### Chinese remaindering -/

lemma eq_of_mod_oddPrime_eq {a t n k : ℕ} (ha : a ≤ n) (ht : t ≤ n) (hk : n < 2 ^ k)
    (h : ∀ j ∈ Finset.Icc 1 k, a % oddPrime j = t % oddPrime j) : a = t := by
  have hprod : 2 ^ k ≤ ∏ j ∈ Finset.Icc 1 k, oddPrime j := by
    calc 2 ^ k = ∏ _j ∈ Finset.Icc 1 k, 2 := by simp
      _ ≤ ∏ j ∈ Finset.Icc 1 k, oddPrime j :=
          Finset.prod_le_prod fun j _ => (oddPrime_prime j).two_le
  have key : ∀ a t : ℕ, a ≤ n → (∀ j ∈ Finset.Icc 1 k, a % oddPrime j = t % oddPrime j) →
      a - t = 0 := by
    intro a t ha h
    have hd : ∏ q ∈ (Finset.Icc 1 k).image oddPrime, q ∣ a - t := by
      apply Finset.prod_primes_dvd
      · intro q hq
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
        exact (oddPrime_prime j).prime
      · intro q hq
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (h j hj))
    rw [Finset.prod_image fun x _ y _ hxy => oddPrime_injective hxy] at hd
    exact Nat.eq_zero_of_dvd_of_lt hd (by omega)
  have h1 := key a t ha h
  have h2 := key t a ht fun j hj => (h j hj).symm
  omega

/-! ### The circuit for `Maj` -/

/-- Number of primes used for Chinese remaindering. -/
def crtLen (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- `Maj(x) = ⋁_{t ≥ n/2} Sum_t(x)`, `Sum_t(x) = ⋀_{j ≤ k} M_{j, t mod p_j}(x)`. -/
noncomputable def majCircuit (n : ℕ) : Circuit n :=
  orL (((List.range (n + 1)).filter fun t => n ≤ 2 * t).map fun t =>
    andL ((List.range' 1 (crtLen n)).map fun j => resGate n j (t % oddPrime j)))

lemma eval_majCircuit (n : ℕ) (z : Fin n → Bool) : (majCircuit n).eval mult z = Maj n z := by
  have hres : ∀ t j, 1 ≤ j → (resGate n j (t % oddPrime j)).eval mult z =
      decide (ones z % oddPrime j = t % oddPrime j) := fun t j hj =>
    eval_resGate n j _ hj (Nat.mod_lt _ (by have := three_le_oddPrime hj; omega)) z
  have hand : ∀ t, (andL ((List.range' 1 (crtLen n)).map fun j =>
      resGate n j (t % oddPrime j))).eval mult z = true ↔
      (∀ j ∈ Finset.Icc 1 (crtLen n), ones z % oddPrime j = t % oddPrime j) := by
    intro t
    rw [eval_andL, decide_eq_true_eq]
    constructor
    · intro h j hj
      rw [Finset.mem_Icc] at hj
      have := h _ (List.mem_map.2 ⟨j, List.mem_range'.2 ⟨j - 1, by omega, by omega⟩, rfl⟩)
      rwa [hres t j hj.1, decide_eq_true_eq] at this
    · intro h c hc
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hj
      rw [hres t _ (by omega), decide_eq_true_eq]
      exact h _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  rw [majCircuit, eval_orL, Maj, decide_eq_decide]
  constructor
  · rintro ⟨c, hc, hce⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at ht
    rw [hand] at hce
    have := eq_of_mod_oddPrime_eq (ones_le z) (by omega : t ≤ n)
      (Nat.lt_pow_succ_log_self (by norm_num) n) hce
    omega
  · intro h
    refine ⟨_, List.mem_map.2 ⟨ones z, ?_, rfl⟩, ?_⟩
    · rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by have := ones_le z; omega, h⟩
    · rw [hand]
      intro j _; rfl

lemma depth_majCircuit_le (n : ℕ) : (majCircuit n).depth ≤ 4 := by
  refine depth_orL_le _ fun c hc => ?_
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hc
  refine depth_andL_le _ fun c hc => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
  exact depth_resGate_le _ _ _

lemma resLen_le {n j r : ℕ} (hj : j ≤ n + 1) : resLen n j r ≤ (n + 2) ^ 11 := by
  have hp : oddPrime j ≤ (n + 2) ^ 5 := by
    calc oddPrime j ≤ 8 * (j + 1) ^ 2 := oddPrime_le j
      _ ≤ (n + 2) ^ 3 * (n + 2) ^ 2 := by
          have h8 : 2 ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
          have hj2 : (j + 1) ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          exact Nat.mul_le_mul (by simpa using h8) hj2
      _ = (n + 2) ^ 5 := by ring
  have hn : n ≤ (n + 2) ^ 5 := by
    calc n ≤ (n + 2) ^ 1 := by simp
      _ ≤ (n + 2) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc resLen n j r ≤ oddPrime j * (n + oddPrime j) := by
        unfold resLen; gcongr <;> omega
    _ ≤ (n + 2) ^ 5 * ((n + 2) ^ 5 + (n + 2) ^ 5) := by gcongr
    _ ≤ (n + 2) ^ 5 * (n + 2) ^ 6 := by
        gcongr
        rw [pow_succ]; nlinarith
    _ = (n + 2) ^ 11 := by ring

lemma size_majCircuit_le (n : ℕ) : (majCircuit n).size ≤ (n + 2) ^ 16 := by
  have hk : crtLen n ≤ n + 1 := by
    have := Nat.log_le_self 2 n
    simp only [crtLen]; omega
  have hgate : ∀ t j, j ∈ List.range' 1 (crtLen n) →
      (resGate n j (t % oddPrime j)).size ≤ 2 * (n + 2) ^ 11 + 1 := by
    intro t j hj
    rw [List.mem_range'] at hj
    exact (size_resGate_le _ _ _).trans (by have := resLen_le (n := n) (j := j) (r := t % oddPrime j) (by omega); omega)
  have hand : ∀ t, (andL ((List.range' 1 (crtLen n)).map fun j => resGate n j (t % oddPrime j))).size
      ≤ (n + 1) * (2 * (n + 2) ^ 11 + 1) + 1 := by
    intro t
    refine (size_andL_le _ (s := 2 * (n + 2) ^ 11 + 1) ?_).trans ?_
    · intro c hc
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
      exact hgate t j hj
    · simp only [List.length_map, List.length_range']
      gcongr
  refine (size_orL_le _ (s := (n + 1) * (2 * (n + 2) ^ 11 + 1) + 1) ?_).trans ?_
  · intro c hc
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hc
    exact hand t
  · simp only [List.length_map]
    have hlen : ((List.range (n + 1)).filter fun t => n ≤ 2 * t).length ≤ n + 1 :=
      (List.length_filter_le _ _).trans (by simp)
    have h1 : 1 ≤ (n + 2) ^ 11 := Nat.one_le_pow _ _ (by omega)
    calc _ ≤ (n + 1) * ((n + 1) * (2 * (n + 2) ^ 11 + 1) + 1) + 1 := by gcongr
      _ ≤ (n + 2) * ((n + 2) * (3 * (n + 2) ^ 11) + (n + 2) ^ 11) + (n + 2) ^ 11 := by
          gcongr <;> omega
      _ ≤ (n + 2) * ((n + 2) * ((n + 2) ^ 2 * (n + 2) ^ 11) + (n + 2) * (n + 2) ^ 11) +
            (n + 2) * (n + 2) * (n + 2) ^ 11 := by
          have h3 : 3 ≤ (n + 2) ^ 2 := by nlinarith
          gcongr <;> nlinarith
      _ ≤ (n + 2) ^ 16 := by
          have hA : (n + 2) * (n + 2) = (n + 2) ^ 2 := by ring
          have h16 : (n + 2) ^ 16 = (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) * (n + 2) ^ 11 := by ring
          rw [h16]
          generalize (n + 2) ^ 11 = P at *
          have e1 : (n + 2) * ((n + 2) * ((n + 2) ^ 2 * P) + (n + 2) * P) + (n + 2) * (n + 2) * P
              = (n + 2) ^ 2 * (n + 2) ^ 2 * P + 2 * ((n + 2) ^ 2 * P) := by ring
          rw [e1]
          generalize hA2 : (n + 2) ^ 2 = A at *
          have h2 : 4 ≤ A := by subst hA2; nlinarith
          have hN : 2 ≤ n + 2 := by omega
          have h3 : 2 * (A * P) ≤ A * (A * P) := Nat.mul_le_mul_right _ (by omega)
          have : A * A * P + 2 * (A * P) ≤ A * A * P + A * A * P := by
            rw [mul_assoc A A P]; omega
          calc A * A * P + 2 * (A * P) ≤ A * A * P * 2 := by omega
            _ ≤ A * A * P * (n + 2) := by gcongr
            _ = A * A * (n + 2) * P := by ring

/-- **Lemma 4.** `Maj ≤ᵀ mult`. -/
theorem maj_reduces_mult : Maj ≤ᵀ mult :=
  ⟨4, 16, fun n => ⟨majCircuit n, depth_majCircuit_le n, size_majCircuit_le n,
    eval_majCircuit n⟩⟩

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

end PLB
