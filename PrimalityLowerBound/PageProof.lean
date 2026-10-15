import PrimalityLowerBound.Page
import OAI.NumberTheory.PrimeGaps.Main

/-!
# Page's estimate from Siegel–Walfisz

The upstream character bound is uniform in conductors up to powers of `log x`.
Character orthogonality gives an arithmetic-progression von Mangoldt estimate.
Removing prime powers and specialising to `x = 2^n` gives a uniform weighted-prime
asymptotic for `p ≤ n`. A cutoff at `r^n`, with `1 < r < 2`, then removes the weights.

See `vendor/openai-math/UPSTREAM.md` for the source revision and license.
-/

namespace PLB.PageProof
open OAI.LargePrimeGaps

/-- Uniform arithmetic-progression bound obtained from the proved character estimate. -/
theorem uniform_psi_ap_bound (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ q a : ℕ, 0 < q → (q : ℝ) ≤ (Real.log x) ^ B →
        a < q → a.Coprime q →
        |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a - x / q.totient| ≤
          M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
  classical
  obtain ⟨M, hM, x₀, hx₀, h⟩ := siegelWalfisz A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro x hx q a hq hqlog ha hcop
  let : NeZero q := ⟨ne_of_gt hq⟩
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hχ (χ : DirichletCharacter ℂ q) :
      ‖primeCharacterError x χ.primitiveCharacter‖ ≤ M * x * (Real.log x) ^ (-A) := by
    apply h x hx χ.conductor (Nat.pos_of_ne_zero χ.conductor_ne_zero) _ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
    exact (show (χ.conductor : ℝ) ≤ q by exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level).trans hqlog
  calc
    _ ≤ characterMeanError x q := endpointClassError_le_character_sum x hq ha hcop
    _ ≤ (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ.primitiveCharacter‖) /
          (q.totient : ℝ) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q :=
      characterMeanError_le_primitive_average x hq
    _ ≤ (∑ _χ : DirichletCharacter ℂ q, M * x * (Real.log x) ^ (-A)) /
          (q.totient : ℝ) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
      gcongr
      exact hχ _
    _ = _ := by simp [hcard, mul_div_cancel_left₀ _ hphi.ne']


open Filter Topology

/-- Logarithmically weighted primes in one residue class. -/
noncomputable def thetaAP (X p l : ℕ) : ℝ := residuePrefix theta X p l

private noncomputable def thetaError (M : ℝ) (n : ℕ) : ℝ :=
  (M / Real.log 2 ^ 4) / (n : ℝ) ^ 3 +
    (n : ℝ) ^ 3 / (2 : ℝ) ^ n +
    (2 * Real.log 2) * ((n : ℝ) ^ 2 / (Real.sqrt 2) ^ n)

private lemma thetaError_tendsto (M : ℝ) :
    Tendsto (thetaError M) atTop (𝓝 0) := by
  have h1 := tendsto_const_div_pow (M / Real.log 2 ^ 4) 3 (by decide)
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1 : ℝ) < 2)
  have h3 := (tendsto_pow_const_div_const_pow_of_one_lt 2
    Real.one_lt_sqrt_two).const_mul (2 * Real.log 2)
  convert (h1.add h2).add h3 using 1 <;> first | rfl | norm_num

/-- The weighted prime count has the required asymptotic, uniformly for prime moduli `p ≤ n`. -/
theorem theta_dyadic_uniform :
    ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ p l : ℕ,
      p.Prime → 1 ≤ l → l < p → p ≤ n →
      |thetaAP (2 ^ n) p l * ((p : ℝ) - 1) / (2 : ℝ) ^ n - 1| ≤ ε := by
  obtain ⟨M, hM, x₀, hx₀, hpsi⟩ := uniform_psi_ap_bound 4 2 (by norm_num) (by norm_num)
  intro ε hε
  have hlarge := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop x₀
  have hsmall := (thetaError_tendsto M).eventually (gt_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hlarge.and hsmall)
  refine ⟨max N₀ 4, ?_⟩
  intro n hn p l hp hl hlp hpn
  obtain ⟨hX, hE⟩ := hN₀ n (by omega)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpn' : (p : ℝ) ≤ n := by exact_mod_cast hpn
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hmod : (p : ℝ) ≤ (Real.log ((2 : ℝ) ^ n)) ^ (2 : ℝ) := by
    rw [Real.rpow_two, Real.log_pow]
    have : (n : ℝ) / 2 ≤ n * Real.log 2 := by nlinarith
    nlinarith [sq_nonneg ((n : ℝ) - 4)]
  have hcop : l.Coprime p := (Nat.coprime_of_lt_prime (by omega) hlp hp).symm
  have hψ := hpsi ((2 : ℝ) ^ n) hX p l hp.pos hmod hlp hcop
  have hcast : (((2 ^ n : ℕ) : ℝ)) = (2 : ℝ) ^ n := by norm_cast
  have hlogp : Real.log p ≤ n := (Real.log_le_self (by positivity)).trans hpn'
  have hpp : ((p.totient : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]; norm_num
  have hfloor : ⌊(2 : ℝ) ^ n⌋₊ = 2 ^ n := by rw [← hcast, Nat.floor_natCast]
  rw [hfloor, Nat.log_pow (by norm_num), hpp, Real.log_pow] at hψ
  have hψ' : |residuePrefix ArithmeticFunction.vonMangoldt (2 ^ n) p l -
        (2 : ℝ) ^ n / ((p : ℝ) - 1)| ≤
      M * (2 : ℝ) ^ n / ((n : ℝ) * Real.log 2) ^ 4 + (n : ℝ) ^ 2 := by
    apply hψ.trans
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = (4 : ℕ) by norm_num,
      Real.rpow_natCast]
    have := mul_le_mul_of_nonneg_left hlogp hn0.le
    simpa [div_eq_mul_inv, pow_two] using add_le_add_left this
      (M * (2 : ℝ) ^ n * (((n : ℝ) * Real.log 2) ^ 4)⁻¹)
  have hprimepower := residueSlice_primepower_error
    (U := 2 ^ n) (Nat.one_le_pow _ _ (by omega)) 0 p l
  rw [hcast, Real.log_pow] at hprimepower
  have hθ : |thetaAP (2 ^ n) p l - (2 : ℝ) ^ n / ((p : ℝ) - 1)| ≤
      M * (2 : ℝ) ^ n / ((n : ℝ) * Real.log 2) ^ 4 + (n : ℝ) ^ 2 +
      2 * Real.sqrt ((2 : ℝ) ^ n) * (n * Real.log 2) := by
    calc
      _ ≤ |residuePrefix ArithmeticFunction.vonMangoldt (2 ^ n) p l -
          (2 : ℝ) ^ n / ((p : ℝ) - 1)| +
          |residuePrefix ArithmeticFunction.vonMangoldt (2 ^ n) p l - thetaAP (2 ^ n) p l| := by
        exact abs_sub_le _ _ _ |>.trans_eq (by rw [abs_sub_comm (thetaAP _ _ _)]; ring)
      _ ≤ _ := add_le_add hψ' hprimepower
  have hnorm : |thetaAP (2 ^ n) p l * ((p : ℝ) - 1) / (2 : ℝ) ^ n - 1| =
      |thetaAP (2 ^ n) p l - (2 : ℝ) ^ n / ((p : ℝ) - 1)| *
        ((p : ℝ) - 1) / (2 : ℝ) ^ n := by
    have he : thetaAP (2 ^ n) p l * ((p : ℝ) - 1) / (2 : ℝ) ^ n - 1 =
        (thetaAP (2 ^ n) p l - (2 : ℝ) ^ n / ((p : ℝ) - 1)) *
          ((p : ℝ) - 1) / (2 : ℝ) ^ n := by
      field_simp [(sub_pos.mpr hp1).ne']
    rw [he, abs_div, abs_mul, abs_of_pos (sub_pos.mpr hp1),
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
  rw [hnorm]
  apply le_trans _ hE.le
  calc
    _ ≤ (M * (2 : ℝ) ^ n / ((n : ℝ) * Real.log 2) ^ 4 + (n : ℝ) ^ 2 +
        2 * Real.sqrt ((2 : ℝ) ^ n) * (n * Real.log 2)) * n / (2 : ℝ) ^ n := by
      gcongr
      linarith
    _ = thetaError M n := by
      have hs : Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
        clear * - n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
      rw [hs]
      have hsq : (Real.sqrt 2) ^ n * (Real.sqrt 2) ^ n = (2 : ℝ) ^ n := by
        rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
      unfold thetaError
      field_simp
      linear_combination (2 * (n : ℝ) ^ 5 * Real.log 2 ^ 5) * hsq



lemma thetaAP_eq_sum (X p l : ℕ) :
    thetaAP X p l =
      ∑ q ∈ (Finset.range (X + 1)).filter (fun q => q.Prime ∧ q % p = l), Real.log q := by
  classical
  have hs : (Finset.Ioc 0 X).filter (fun q => q.Prime ∧ q % p = l) =
      (Finset.range (X + 1)).filter (fun q => q.Prime ∧ q % p = l) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨hq0, hqX⟩, hp, hm⟩; exact ⟨by omega, hp, hm⟩
    · rintro ⟨hqX, hp, hm⟩; exact ⟨⟨hp.pos, by omega⟩, hp, hm⟩
  rw [← hs]
  simp only [thetaAP, residuePrefix, residueSlice, theta, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : q.Prime <;> by_cases hm : q % p = l <;> simp [hp, hm]

lemma thetaAP_le_count_log (X p l : ℕ) :
    thetaAP X p l ≤ (primesAP X p l : ℝ) * Real.log X := by
  rw [thetaAP_eq_sum, primesAP]
  calc
    _ ≤ ∑ _q ∈ (Finset.range (X + 1)).filter
        (fun q => q.Prime ∧ q % p = l), Real.log X := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hX, hp, _⟩ := Finset.mem_filter.mp hq
      apply Real.log_le_log (by exact_mod_cast hp.pos)
      exact_mod_cast (show q ≤ X by have := Finset.mem_range.mp hX; omega)
    _ = _ := by simp

/-- Splitting at `y` loses at most `⌊y⌋ + 1` small primes. -/
lemma count_log_le_thetaAP_add (X p l : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    (primesAP X p l : ℝ) * Real.log y ≤
      thetaAP X p l + (y + 1) * Real.log y := by
  classical
  let S := (Finset.range (X + 1)).filter (fun q => q.Prime ∧ q % p = l)
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hsum : ∑ q ∈ S, Real.log y ≤
      ∑ q ∈ S, (Real.log q + if q ≤ ⌊y⌋₊ then Real.log y else 0) := by
    apply Finset.sum_le_sum
    intro q hq
    have hp : q.Prime := (Finset.mem_filter.mp hq).2.1
    have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hp.one_le)
    by_cases hqy : q ≤ ⌊y⌋₊
    · simp only [ite_eq_left hqy]; linarith
    · simp only [ite_eq_right hqy, add_zero]
      exact Real.log_le_log (by linarith) ((Nat.floor_lt (by linarith)).mp (by omega)).le
  have hcard : (S.filter (fun q => q ≤ ⌊y⌋₊)).card ≤ ⌊y⌋₊ + 1 := by
    calc
      _ ≤ (Finset.range (⌊y⌋₊ + 1)).card := Finset.card_le_card (by
        intro q hq
        have := (Finset.mem_filter.mp hq).2
        simpa only [Finset.mem_range] using (show q < ⌊y⌋₊ + 1 by omega))
      _ = _ := Finset.card_range _
  rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard' : ((S.filter (fun q => q ≤ ⌊y⌋₊)).card : ℝ) ≤ y + 1 := by
    have h := Nat.floor_le (show 0 ≤ y by linarith)
    exact (show ((S.filter (fun q => q ≤ ⌊y⌋₊)).card : ℝ) ≤ (⌊y⌋₊ : ℝ) + 1 by
      exact_mod_cast hcard).trans (by linarith)
  have hbound := mul_le_mul_of_nonneg_right hcard' hlog
  rw [thetaAP_eq_sum]
  change (S.card : ℝ) * Real.log y ≤ (∑ q ∈ S, Real.log q) + (y + 1) * Real.log y
  linarith



private noncomputable def smallCountError (r : ℝ) (n : ℕ) : ℝ :=
  Real.log 2 * ((n : ℝ) ^ 2 * (r / 2) ^ n + (n : ℝ) ^ 2 / (2 : ℝ) ^ n)

private lemma smallCountError_tendsto {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r < 2) :
    Tendsto (smallCountError r) atTop (𝓝 0) := by
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (show 0 ≤ r / 2 by positivity) (show r / 2 < 1 by linarith)
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)
  convert (h1.add h2).const_mul (Real.log 2) using 1 <;> first | rfl | norm_num

private lemma smallCountError_eq (r : ℝ) (n : ℕ) :
    smallCountError r n = (r ^ n + 1) * (n : ℝ) ^ 2 * Real.log 2 / (2 : ℝ) ^ n := by
  unfold smallCountError
  rw [div_pow]
  ring

end PageProof

open PageProof in
/-- Page's estimate, proved from the uniform Siegel–Walfisz character bound. -/
theorem pageEstimate : PageEstimate := by
  intro ε hε
  let a : ℝ := 4 / (4 + ε)
  let η : ℝ := ε / (4 + ε)
  have hden : 0 < 4 + ε := by linarith
  have ha : 0 < a := div_pos (by norm_num) hden
  have ha1 : a < 1 := (div_lt_one hden).mpr (by linarith)
  have hη : 0 < η := div_pos hε hden
  have hηε : η ≤ ε := (div_le_iff₀ hden).mpr (by nlinarith)
  have hae : 1 + η = a * (1 + ε / 2) := by dsimp [a, η]; field_simp; ring
  let r : ℝ := (2 : ℝ) ^ a
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) ha
  have hr0 : 0 < r := by linarith
  have hr2 : r < 2 := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) ha1
  have hlogr : Real.log r = a * Real.log 2 := Real.log_rpow (by norm_num) a
  obtain ⟨N₁, hN₁⟩ := theta_dyadic_uniform η hη
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    ((smallCountError_tendsto hr0.le hr2).eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max (max N₁ N₂) 1, ?_⟩
  intro n hn p l hp hl hlp hpn
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpn' : (p : ℝ) ≤ n := by exact_mod_cast hpn
  have hX : (0 : ℝ) < 2 ^ n := by positivity
  have hθ := abs_le.mp (hN₁ n (by omega) p l hp hl hlp hpn)
  have hsmall := hN₂ n (by omega)
  let u : ℝ := (primesAP (2 ^ n) p l : ℝ) * (n * Real.log 2) * ((p : ℝ) - 1) / (2 : ℝ) ^ n
  let v : ℝ := thetaAP (2 ^ n) p l * ((p : ℝ) - 1) / (2 : ℝ) ^ n
  let w : ℝ := (r ^ n + 1) * (n * Real.log 2) * ((p : ℝ) - 1) / (2 : ℝ) ^ n
  have hv : v ≤ u := by
    have h := mul_le_mul_of_nonneg_right (thetaAP_le_count_log (2 ^ n) p l)
      (show 0 ≤ ((p : ℝ) - 1) / (2 : ℝ) ^ n by positivity)
    push_cast at h
    rw [Real.log_pow] at h
    simpa [u, v, div_eq_mul_inv, mul_assoc] using h
  have hw : w ≤ smallCountError r n := by
    rw [smallCountError_eq]
    dsimp [w]
    calc
      _ ≤ (r ^ n + 1) * (n * Real.log 2) * n / (2 : ℝ) ^ n := by gcongr; linarith
      _ = _ := by ring
  have hupper : a * u ≤ v + a * w := by
    have hy : 1 ≤ r ^ n := one_le_pow₀ hr1.le
    have h := mul_le_mul_of_nonneg_right (count_log_le_thetaAP_add (2 ^ n) p l hy)
      (show 0 ≤ ((p : ℝ) - 1) / (2 : ℝ) ^ n by positivity)
    rw [Real.log_pow, hlogr] at h
    convert h using 1 <;> dsimp [u, v, w] <;> ring
  have hu : |u - 1| ≤ ε := by
    apply abs_le.mpr
    constructor
    · change -η ≤ v - 1 ∧ v - 1 ≤ η at hθ
      linarith [hθ.1]
    · have hvupper : v ≤ 1 + η := by linarith [hθ.2]
      have hwupper : w ≤ ε / 2 := hw.trans hsmall.le
      have haupper : a * u ≤ a * (1 + ε) := by
        calc
          _ ≤ v + a * w := hupper
          _ ≤ (1 + η) + a * (ε / 2) := add_le_add hvupper (mul_le_mul_of_nonneg_left hwupper ha.le)
          _ = a * (1 + ε) := by rw [hae]; ring
      have := le_of_mul_le_mul_left haupper ha
      linarith
  convert hu using 2
  dsimp [u]
  field_simp

end PLB
