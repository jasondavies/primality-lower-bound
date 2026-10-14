import Mathlib

/-!
# Square-free numbers in an arithmetic progression (elementary lower bound)

For `h` odd with `p² ∤ h` and `q = 2^M p²`, at least a quarter of the numbers `h + q y`,
`y < Y`, are square-free (for `Y` large).  This is the (weaker, elementary) replacement of the
paper's estimate (2), which is all that the reduction needs.
-/

namespace PLB

lemma card_dvd_affine_le (d h q Y : ℕ) (hcop : Nat.Coprime d q) :
    ((Finset.range Y).filter fun y => d ∣ h + q * y).card ≤ Y / d + 1 := by
  have := Finset.card_le_card_of_injOn (fun y => y / d)
    (s := (Finset.range Y).filter fun y => d ∣ h + q * y) (t := Finset.range (Y / d + 1)) ?_ ?_
  · simpa using this
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hy
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hy.1.le)
  · intro y₁ hy₁ y₂ hy₂ heq
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hy₁ hy₂
    have h1 : h + q * y₁ ≡ h + q * y₂ [MOD d] :=
      (Nat.modEq_zero_iff_dvd.2 hy₁.2).trans (Nat.modEq_zero_iff_dvd.2 hy₂.2).symm
    have h2 : q * y₁ ≡ q * y₂ [MOD d] := Nat.ModEq.add_left_cancel' h h1
    have h3 : y₁ ≡ y₂ [MOD d] := Nat.ModEq.cancel_left_of_coprime hcop h2
    simp only at heq
    rw [← Nat.div_add_mod y₁ d, ← Nat.div_add_mod y₂ d, heq, h3]

lemma sum_inv_sq_Ioc_le (T : ℕ) (hT : 2 ≤ T) :
    ∑ ℓ ∈ Finset.Ioc 2 T, (1 : ℝ) / (ℓ : ℝ) ^ 2 ≤ 1 / 2 - 1 / T := by
  induction T, hT using Nat.le_induction with
  | base => norm_num
  | succ T hT ih =>
    rw [Finset.sum_Ioc_succ_top hT]
    have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
    have key : (1 : ℝ) / ((T + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / T - 1 / ((T + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

lemma sum_div_sq_Ioc_le (T Y : ℕ) :
    (∑ ℓ ∈ Finset.Ioc 2 T, ((Y / ℓ ^ 2 : ℕ) : ℝ)) ≤ Y / 2 := by
  rcases Nat.lt_or_ge T 2 with hT | hT
  · rw [Finset.Ioc_eq_empty (by omega)]; simp; positivity
  calc (∑ ℓ ∈ Finset.Ioc 2 T, ((Y / ℓ ^ 2 : ℕ) : ℝ)) ≤ ∑ ℓ ∈ Finset.Ioc 2 T, (Y : ℝ) * (1 / (ℓ : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        rw [mul_one_div]
        have := Nat.cast_div_le (α := ℝ) (m := Y) (n := ℓ ^ 2)
        simpa using this
    _ = Y * ∑ ℓ ∈ Finset.Ioc 2 T, (1 : ℝ) / (ℓ : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ Y * (1 / 2) := by
        gcongr
        have := sum_inv_sq_Ioc_le T hT
        have : (0 : ℝ) ≤ 1 / T := by positivity
        linarith
    _ = Y / 2 := by ring

/-- **Square-free density.**  Let `p ≥ 3` be prime, `M ≥ 1`, `q = 2^M p²`, `h < 2^M` odd with
`p² ∤ h`.  If `q Y ≤ T²` and `8 T ≤ Y` then at least a quarter of `h + q y` (`y < Y`) are
square-free. -/
theorem squarefree_density (p M h Y T : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hM : 1 ≤ M)
    (hh : h < 2 ^ M) (hodd : h % 2 = 1) (hph : ¬ p ^ 2 ∣ h)
    (hT : 2 ^ M * p ^ 2 * Y ≤ T * T) (hTY : 8 * T ≤ Y) :
    Y ≤ 4 * ((Finset.range Y).filter fun y => Squarefree (h + 2 ^ M * p ^ 2 * y)).card := by
  set q := 2 ^ M * p ^ 2 with hq
  set good := (Finset.range Y).filter fun y => Squarefree (h + q * y)
  set bad := (Finset.range Y).filter fun y => ¬ Squarefree (h + q * y)
  set S := (Finset.Ioc 2 T).filter fun ℓ => ℓ.Prime ∧ ℓ ≠ p
  have hsplit : good.card + bad.card = Y := by
    rw [Finset.card_filter_add_card_filter_not]; simp
  have hsub : bad ⊆ S.biUnion fun ℓ => (Finset.range Y).filter fun y => ℓ ^ 2 ∣ h + q * y := by
    intro y hy
    simp only [bad, Finset.mem_filter, Finset.mem_range] at hy
    obtain ⟨hyY, hsq⟩ := hy
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨ℓ, hℓ, hdvd⟩ := hsq
    have hNpos : 0 < h + q * y := by omega
    have hqeven : 2 ∣ q := by
      rw [hq]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      have : 2 ∣ h + q * y := (Dvd.intro _ rfl).trans hdvd
      have : 2 ∣ q * y := Dvd.dvd.mul_right hqeven _
      omega
    have hℓp : ℓ ≠ p := by
      rintro rfl
      apply hph
      have h1 : ℓ ^ 2 ∣ q * y := by rw [hq]; exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
      rw [← sq] at hdvd
      exact (Nat.dvd_add_right h1).1 (by rwa [add_comm] at hdvd)
    have hℓ3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
    have hℓT : ℓ < T := by
      have h1 : ℓ * ℓ ≤ h + q * y := Nat.le_of_dvd hNpos hdvd
      have h2 : h + q * y < T * T := by
        have : q * y + q ≤ q * Y := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hyY
        have : 2 ^ M ≤ q := by rw [hq]; exact Nat.le_mul_of_pos_right _ (by positivity)
        omega
      by_contra hc
      push Not at hc
      have : T * T ≤ ℓ * ℓ := Nat.mul_le_mul hc hc
      omega
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, S]
    exact ⟨ℓ, ⟨⟨by omega, hℓT.le⟩, hℓ, hℓp⟩, hyY, by rwa [sq]⟩
  have hbad : (bad.card : ℝ) ≤ Y / 2 + T := by
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∀ ℓ ∈ S, ((Finset.range Y).filter fun y => ℓ ^ 2 ∣ h + q * y).card ≤ Y / ℓ ^ 2 + 1 := by
      intro ℓ hℓ
      simp only [S, Finset.mem_filter, Finset.mem_Ioc] at hℓ
      apply card_dvd_affine_le
      rw [hq]
      apply Nat.Coprime.mul_right
      · apply Nat.Coprime.pow
        exact (Nat.coprime_primes hℓ.2.1 Nat.prime_two).2 (by omega)
      · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hℓ.2.1 hp).2 hℓ.2.2)
    have h3 : (bad.card : ℝ) ≤ ∑ ℓ ∈ S, ((Y / ℓ ^ 2 + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1.trans (Finset.sum_le_sum h2)
    have h4 : ∑ ℓ ∈ S, ((Y / ℓ ^ 2 + 1 : ℕ) : ℝ) ≤ ∑ ℓ ∈ Finset.Ioc 2 T, ((Y / ℓ ^ 2 + 1 : ℕ) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
    have h5 : ∑ ℓ ∈ Finset.Ioc 2 T, ((Y / ℓ ^ 2 + 1 : ℕ) : ℝ) ≤ Y / 2 + T := by
      push_cast
      rw [Finset.sum_add_distrib]
      have := sum_div_sq_Ioc_le T Y
      have hc : ((Finset.Ioc 2 T).card : ℝ) ≤ T := by
        have : (Finset.Ioc 2 T).card ≤ T := by simp
        exact_mod_cast this
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      linarith
    linarith
  have hY : (8 * T : ℝ) ≤ Y := by exact_mod_cast hTY
  have : (Y : ℝ) ≤ 4 * good.card := by
    have : (good.card : ℝ) + bad.card = Y := by exact_mod_cast hsplit
    linarith
  exact_mod_cast this

end PLB
