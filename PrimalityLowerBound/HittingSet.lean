import Mathlib

/-!
# Adleman's trick as a hitting-set lemma

If every `x ∈ X` (with `|X| ≤ 2^m`) is "hit" by at least a `1/K` fraction of `Y`, then a list of
`K (m + 1)` elements of `Y` hits every `x ∈ X`.  This replaces the probabilistic argument
("there must be at least one sequence of probabilistic inputs…") by a greedy one.
-/

namespace PLB

lemma exists_good_hit {α β : Type*} (U : Finset α) (Y : Finset β) (hY : Y.Nonempty)
    (R : α → β → Prop) [∀ a b, Decidable (R a b)] (K : ℕ)
    (h : ∀ x ∈ U, Y.card ≤ K * (Y.filter (R x)).card) :
    ∃ y ∈ Y, U.card ≤ K * (U.filter fun x => R x y).card := by
  have hsum : ∑ y ∈ Y, (U.filter fun x => R x y).card = ∑ x ∈ U, (Y.filter (R x)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have key : ∑ _y ∈ Y, U.card ≤ ∑ y ∈ Y, K * (U.filter fun x => R x y).card := by
    rw [← Finset.mul_sum, hsum, Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_comm]
    calc U.card * Y.card = ∑ _x ∈ U, Y.card := by simp
      _ ≤ ∑ x ∈ U, K * (Y.filter (R x)).card := Finset.sum_le_sum h
  exact Finset.exists_le_of_sum_le hY key

theorem exists_hitting_list {α β : Type*} (X : Finset α) (Y : Finset β) (hY : Y.Nonempty)
    (R : α → β → Prop) [∀ a b, Decidable (R a b)] (K m : ℕ) (hK : 0 < K)
    (hX : X.card ≤ 2 ^ m) (h : ∀ x ∈ X, Y.card ≤ K * (Y.filter (R x)).card) :
    ∃ ys : List β, ys.length ≤ K * (m + 1) ∧ (∀ y ∈ ys, y ∈ Y) ∧ ∀ x ∈ X, ∃ y ∈ ys, R x y := by
  -- greedy: after `t` steps at most `|X| (1 - 1/K)^t` elements are not hit
  have step : ∀ t : ℕ, ∃ ys : List β, ys.length = t ∧ (∀ y ∈ ys, y ∈ Y) ∧
      ((X.filter fun x => ∀ y ∈ ys, ¬ R x y).card : ℝ) ≤ X.card * (1 - 1 / (K : ℝ)) ^ t := by
    intro t
    induction t with
    | zero => exact ⟨[], rfl, by simp, by simp⟩
    | succ t ih =>
      obtain ⟨ys, hlen, hys, hU⟩ := ih
      set U := X.filter fun x => ∀ y ∈ ys, ¬ R x y
      obtain ⟨y, hyY, hy⟩ := exists_good_hit U Y hY R K fun x hx => h x (Finset.filter_subset _ _ hx)
      refine ⟨y :: ys, by simp [hlen], ?_, ?_⟩
      · intro y' hy'
        rcases List.mem_cons.1 hy' with rfl | h'
        · exact hyY
        · exact hys y' h'
      · have hU' : (X.filter fun x => ∀ y' ∈ y :: ys, ¬ R x y') = U.filter fun x => ¬ R x y := by
          ext x
          simp only [Finset.mem_filter, List.mem_cons, U]
          constructor
          · rintro ⟨hx, h'⟩
            exact ⟨⟨hx, fun y' hy' => h' y' (Or.inr hy')⟩, h' y (Or.inl rfl)⟩
          · rintro ⟨⟨hx, h'⟩, h''⟩
            refine ⟨hx, fun y' hy' => ?_⟩
            rcases hy' with rfl | hy'
            · exact h''
            · exact h' y' hy'
        rw [hU']
        have hsplit := Finset.card_filter_add_card_filter_not (s := U) (p := fun x => R x y)
        have hKr : (0 : ℝ) < K := by exact_mod_cast hK
        have hyr : (U.card : ℝ) ≤ K * ((U.filter fun x => R x y).card : ℝ) := by exact_mod_cast hy
        have hcard : ((U.filter fun x => ¬ R x y).card : ℝ) ≤ U.card * (1 - 1 / (K : ℝ)) := by
          have : ((U.filter fun x => ¬ R x y).card : ℝ) =
              U.card - (U.filter fun x => R x y).card := by
            rw [← hsplit]; push_cast; ring
          rw [this, mul_sub, mul_one, mul_one_div]
          have : (U.card : ℝ) / K ≤ (U.filter fun x => R x y).card := by
            rw [div_le_iff₀ hKr]; linarith
          linarith
        have h1K : 0 ≤ 1 - 1 / (K : ℝ) := by
          rw [sub_nonneg, div_le_one hKr]; exact_mod_cast hK
        calc ((U.filter fun x => ¬ R x y).card : ℝ) ≤ U.card * (1 - 1 / (K : ℝ)) := hcard
          _ ≤ X.card * (1 - 1 / (K : ℝ)) ^ t * (1 - 1 / (K : ℝ)) :=
              mul_le_mul_of_nonneg_right hU h1K
          _ = X.card * (1 - 1 / (K : ℝ)) ^ (t + 1) := by ring
  obtain ⟨ys, hlen, hys, hU⟩ := step (K * (m + 1))
  refine ⟨ys, hlen.le, hys, ?_⟩
  -- the number of elements not hit is `< 1`
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h1K : 0 ≤ 1 - 1 / (K : ℝ) := by
    rw [sub_nonneg, div_le_one hKr]; exact_mod_cast hK
  have hexp : (1 - 1 / (K : ℝ)) ^ (K * (m + 1)) ≤ Real.exp (-(m + 1 : ℝ)) := by
    calc (1 - 1 / (K : ℝ)) ^ (K * (m + 1)) ≤ (Real.exp (-(1 / (K : ℝ)))) ^ (K * (m + 1)) := by
          apply pow_le_pow_left₀ h1K
          have := Real.add_one_le_exp (-(1 / (K : ℝ)))
          linarith
      _ = Real.exp (-(m + 1 : ℝ)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have h2 : (2 : ℝ) ^ m * Real.exp (-(m + 1 : ℝ)) < 1 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have : (2 : ℝ) ^ (m + 1) ≤ Real.exp (m + 1 : ℝ) := by
      calc (2 : ℝ) ^ (m + 1) ≤ Real.exp 1 ^ (m + 1) := pow_le_pow_left₀ (by norm_num) he _
        _ = Real.exp (m + 1 : ℝ) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    calc (2 : ℝ) ^ m < 2 ^ (m + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      _ ≤ _ := this
  have hlt : ((X.filter fun x => ∀ y ∈ ys, ¬ R x y).card : ℝ) < 1 := by
    calc _ ≤ X.card * (1 - 1 / (K : ℝ)) ^ (K * (m + 1)) := hU
      _ ≤ (2 : ℝ) ^ m * Real.exp (-(m + 1 : ℝ)) := by
          apply mul_le_mul _ hexp (pow_nonneg h1K _) (by positivity)
          exact_mod_cast hX
      _ < 1 := h2
  have hzero : (X.filter fun x => ∀ y ∈ ys, ¬ R x y).card = 0 := by
    have : ((X.filter fun x => ∀ y ∈ ys, ¬ R x y).card : ℝ) < 1 := hlt
    exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
  intro x hx
  by_contra hcon
  push Not at hcon
  have : x ∈ X.filter fun x => ∀ y ∈ ys, ¬ R x y := Finset.mem_filter.2 ⟨hx, hcon⟩
  rw [Finset.card_eq_zero] at hzero
  simp [hzero] at this

end PLB
