import Mathlib

/-!
# Polynomial bounds versus stretched exponentials

Shared estimates for the quantitative Smolensky proof and its qualitative consequence.
-/

namespace PLB

/-- Every fixed power is eventually below a stretched exponential with any positive
coefficient in the exponent. -/
lemma eventually_pow_le_exp (a : ℕ) {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ a ≤ (2 : ℝ) ^ (ε * (N : ℝ) ^ γ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := (isLittleO_log_rpow_atTop hγ).bound
    (c := ε * Real.log 2 / ((a : ℝ) + 1)) (by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (h1.and (Filter.eventually_ge_atTop (1 : ℝ)))] with N hN
  obtain ⟨hb, h1N⟩ := hN
  have hlogN : Real.log N ≤ ε * Real.log 2 / ((a : ℝ) + 1) * (N : ℝ) ^ γ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1N),
      abs_of_nonneg (by positivity)] at hb
    exact hb
  have hbound : (a : ℝ) * Real.log N ≤ Real.log 2 * (ε * (N : ℝ) ^ γ) := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) + 1)).1
      (show Real.log N ≤ ε * Real.log 2 * (N : ℝ) ^ γ / ((a : ℝ) + 1) by
        convert hlogN using 1; ring)
    nlinarith [Real.log_nonneg h1N]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc (N : ℝ) ^ a = Real.exp (Real.log ((N : ℝ) ^ a)) :=
      (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (Real.log 2 * (ε * (N : ℝ) ^ γ)) := by
      apply Real.exp_le_exp.2
      simpa only [Real.log_pow] using hbound

/-- The same estimate after a fixed shift of the input length. -/
lemma eventually_pow_add_le_exp (a b : ℕ) {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ((N : ℝ) + b) ^ a ≤ (2 : ℝ) ^ (ε * (N : ℝ) ^ γ) := by
  filter_upwards [eventually_pow_le_exp (a + 1) hγ hε,
    Filter.eventually_ge_atTop ((b + 1) ^ a), Filter.eventually_ge_atTop 1] with N hN hlarge hN1
  have hlarge' : ((b : ℝ) + 1) ^ a ≤ N := by exact_mod_cast hlarge
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  calc ((N : ℝ) + b) ^ a ≤ ((N : ℝ) * (b + 1)) ^ a := by
        gcongr
        nlinarith [show (0 : ℝ) ≤ b by positivity]
    _ = (N : ℝ) ^ a * ((b : ℝ) + 1) ^ a := mul_pow _ _ _
    _ ≤ (N : ℝ) ^ a * N := mul_le_mul_of_nonneg_left hlarge' (by positivity)
    _ = (N : ℝ) ^ (a + 1) := (pow_succ _ _).symm
    _ ≤ _ := hN

end PLB
