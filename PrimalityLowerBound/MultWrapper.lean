import PrimalityLowerBound.Languages

/-!
# Reducing `mult` to a language: the common wrapper

To reduce `mult(x, j)` to a language `X` it suffices to build, for every `j ≤ m`, a circuit that
decides `p_j ∣ x` for `m`-bit `x`; the wrapper selects the right one according to the `j` part of
the input (`⋁_{j} [input j-part = j] ∧ D_j`).
-/

namespace PLB

open Circuit

/-- The bit `s` of the input, or `false` if `s ≥ m` (a wire or a constant). -/
def inBit {n : ℕ} (m s : ℕ) : Circuit n := wire (if s < m then idx n s else none)

@[simp] lemma eval_inBit {n : ℕ} (L : Lang) (z : Fin n → Bool) (m s : ℕ) :
    (inBit m s : Circuit n).eval L z = (decide (s < m) && getD z s) := by
  unfold inBit
  by_cases hs : s < m <;> simp [hs]

lemma size_inBit {n : ℕ} (m s : ℕ) : (inBit m s : Circuit n).size = 1 := size_wire _

lemma depth_inBit_le {n : ℕ} (m s : ℕ) : (inBit m s : Circuit n).depth ≤ 1 := depth_wire_le _

/-- `valFrom z s m = V` iff the bits agree, for `V < 2^m`. -/
lemma valFrom_eq_iff {n : ℕ} (z : Fin n → Bool) (s m V : ℕ) (hV : V < 2 ^ m) :
    valFrom z s m = V ↔ ∀ i < m, getD z (s + i) = V.testBit i := by
  constructor
  · rintro rfl i hi
    rw [valFrom, testBit_bitsVal]; simp [hi]
  · exact fun h => bitsVal_eq_of_testBit h hV

/-- Circuit testing whether the `m`-bit block starting at `m` encodes `j`. -/
def eqCircuit (m j : ℕ) : Circuit (2 * m) :=
  and (k := m) fun s => lit ⟨m + s, by omega⟩ (j.testBit s)

lemma eval_eqCircuit (L : Lang) (m j : ℕ) (hj : j < 2 ^ m) (z : Fin (2 * m) → Bool) :
    (eqCircuit m j).eval L z = decide (valFrom z m m = j) := by
  rw [eqCircuit, eval_and, decide_eq_decide, valFrom_eq_iff z m m j hj]
  constructor
  · intro h i hi
    have := h ⟨i, hi⟩
    rw [eval_lit, decide_eq_true_eq] at this
    rw [getD_of_lt z (by omega)]; exact this
  · intro h i
    rw [eval_lit, decide_eq_true_eq]
    have := h i i.2
    rwa [getD_of_lt z (by omega)] at this

lemma size_eqCircuit_le (m j : ℕ) : (eqCircuit m j).size ≤ 2 * m + 1 := by
  refine (size_gate_le _ _ (s := 2) fun _ => size_lit_le _ _).trans (by omega)

lemma depth_eqCircuit_le (m j : ℕ) : (eqCircuit m j).depth ≤ 2 :=
  depth_gate_le _ _ fun _ => depth_lit_le _ _

/-- The circuit for `mult` on `2m` bits from circuits `D j` deciding `p_j ∣ x`. -/
def multCircuit (m : ℕ) (D : ℕ → Circuit (2 * m)) : Circuit (2 * m) :=
  orL ((List.range' 1 m).map fun j => andL [eqCircuit m j, D j])

lemma eval_multCircuit (X : Lang) (m : ℕ) (D : ℕ → Circuit (2 * m))
    (hD : ∀ j, 1 ≤ j → j ≤ m → ∀ z, (D j).eval X z = decide (oddPrime j ∣ valFrom z 0 m))
    (z : Fin (2 * m) → Bool) : (multCircuit m D).eval X z = mult (2 * m) z := by
  rw [multCircuit, eval_orL, mult, decide_eq_decide]
  simp only [Nat.mul_mod_right, show 2 * m / 2 = m by omega, true_and]
  constructor
  · rintro ⟨c, hc, hce⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range'_1] at hj
    have hjm : j < 2 ^ m := by
      have := @Nat.lt_two_pow_self m; omega
    rw [eval_andL, decide_eq_true_eq] at hce
    have h1 := hce (eqCircuit m j) (by simp)
    have h2 := hce (D j) (by simp)
    rw [eval_eqCircuit X m _ hjm, decide_eq_true_eq] at h1
    rw [hD _ (by omega) (by omega), decide_eq_true_eq] at h2
    rw [h1]
    exact ⟨by omega, by omega, h2⟩
  · rintro ⟨h1, h2, h3⟩
    set j := valFrom z m m
    refine ⟨_, List.mem_map.2 ⟨j, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩, ?_⟩
    rw [eval_andL, decide_eq_true_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [eval_eqCircuit X m _ (valFrom_lt z m m)]; simp
    · rw [hD _ h1 h2]; simpa using h3

lemma multCircuit_size_le (m : ℕ) (D : ℕ → Circuit (2 * m)) {S : ℕ} (hS : 1 ≤ S)
    (hD : ∀ j, (D j).size ≤ S) : (multCircuit m D).size ≤ (2 * m + 2) ^ 4 * S := by
  refine (size_orL_le _ (s := 2 * (2 * m + 1 + S) + 1) ?_).trans ?_
  · intro c hc
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
    refine (size_andL_le _ (s := 2 * m + 1 + S) ?_).trans (le_of_eq (by simp))
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have := size_eqCircuit_le m j; omega
    · have := hD j; omega
  · simp only [List.length_map, List.length_range']
    generalize hN : 2 * m + 2 = N
    have hN2 : 2 ≤ N := by omega
    have hNS : N ≤ N * S := Nat.le_mul_of_pos_right _ hS
    have hSN : S ≤ N * S := Nat.le_mul_of_pos_left _ (by omega)
    have hNN : 4 ≤ N * N := by nlinarith
    have h1 : 2 * (2 * m + 1 + S) + 1 ≤ N ^ 3 * S := by
      have : N ^ 3 * S = (N * N) * (N * S) := by ring
      rw [this]
      have : 4 * (N * S) ≤ (N * N) * (N * S) := Nat.mul_le_mul_right _ hNN
      omega
    calc m * (2 * (2 * m + 1 + S) + 1) + 1 ≤ m * (N ^ 3 * S) + N ^ 3 * S := by
          gcongr
          have : 1 ≤ N ^ 3 * S := Nat.one_le_iff_ne_zero.2 (by positivity)
          exact this
      _ = (m + 1) * (N ^ 3 * S) := by ring
      _ ≤ N * (N ^ 3 * S) := by gcongr; omega
      _ = N ^ 4 * S := by ring

lemma multCircuit_depth_le (m : ℕ) (D : ℕ → Circuit (2 * m)) {d : ℕ}
    (hD : ∀ j, (D j).depth ≤ d) : (multCircuit m D).depth ≤ d + 4 := by
  refine depth_orL_le _ fun c hc => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
  refine (depth_andL_le _ (d := d + 2) fun c hc => ?_).trans (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact (depth_eqCircuit_le m j).trans (by omega)
  · exact (hD j).trans (by omega)

/-! ### Deciding `p ∣ x` from advice (Adleman's trick) -/

/-- `¬ ⋁_{y ∈ ys} g y`: decides `p ∣ x` when the gates `g y` test a property `R x y` that fails
whenever `p ∣ x` and that some advice value `y ∈ ys` satisfies whenever `p ∤ x`. -/
def adviceDiv {m : ℕ} (g : ℕ → Circuit (2 * m)) (ys : List ℕ) : Circuit (2 * m) :=
  not (orL (ys.map g))

lemma eval_adviceDiv {X : Lang} {m p : ℕ} (g : ℕ → Circuit (2 * m)) (ys : List ℕ)
    (R : ℕ → ℕ → Prop) [∀ x y, Decidable (R x y)]
    (hg : ∀ y ∈ ys, ∀ z, (g y).eval X z = decide (R (valFrom z 0 m) y))
    (hdvd : ∀ x < 2 ^ m, ∀ y ∈ ys, p ∣ x → ¬ R x y)
    (hhit : ∀ x < 2 ^ m, ¬ p ∣ x → ∃ y ∈ ys, R x y) (z : Fin (2 * m) → Bool) :
    (adviceDiv g ys).eval X z = decide (p ∣ valFrom z 0 m) := by
  set x := valFrom z 0 m
  have hx : x < 2 ^ m := valFrom_lt z 0 m
  rw [adviceDiv, eval_not, eval_orL]
  by_cases hpx : p ∣ x
  · have hno : ¬ ∃ c ∈ ys.map g, c.eval X z = true := by
      rintro ⟨c, hc, hce⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
      rw [hg y hy, decide_eq_true_eq] at hce
      exact hdvd x hx y hy hpx hce
    rw [decide_eq_false hno]; simp [hpx]
  · obtain ⟨y, hy, hR⟩ := hhit x hx hpx
    have hyes : ∃ c ∈ ys.map g, c.eval X z = true :=
      ⟨g y, List.mem_map.2 ⟨y, hy, rfl⟩, by rw [hg y hy]; simpa using hR⟩
    rw [decide_eq_true hyes]; simp [hpx]

lemma depth_adviceDiv_le {m d : ℕ} (g : ℕ → Circuit (2 * m)) (ys : List ℕ)
    (h : ∀ y, (g y).depth ≤ d) : (adviceDiv g ys).depth ≤ d + 2 := by
  have : (orL (ys.map g)).depth ≤ d + 1 :=
    depth_orL_le _ fun c hc => by obtain ⟨y, -, rfl⟩ := List.mem_map.1 hc; exact h y
  simp only [adviceDiv, depth]; omega

lemma size_adviceDiv_le {m s : ℕ} (g : ℕ → Circuit (2 * m)) (ys : List ℕ)
    (h : ∀ y, (g y).size ≤ s) : (adviceDiv g ys).size ≤ ys.length * s + 2 := by
  have : (orL (ys.map g)).size ≤ ys.length * s + 1 :=
    (size_orL_le _ fun c hc => by obtain ⟨y, -, rfl⟩ := List.mem_map.1 hc; exact h y).trans
      (by simp)
  simp only [adviceDiv, size]; omega

/-- **The wrapper.** To show `mult ≤ᵀ X` it suffices to decide `p_j ∣ x` (for `m`-bit `x` and
`1 ≤ j ≤ m`, `m` large) by polynomial-size constant-depth circuits with `X` gates. -/
theorem mult_reduces_of {X : Lang} (d c M₀ : ℕ)
    (h : ∀ m ≥ M₀, ∀ j, 1 ≤ j → j ≤ m → ∃ D : Circuit (2 * m), D.depth ≤ d ∧
      D.size ≤ (m + 2) ^ c ∧ ∀ z, D.eval X z = decide (oddPrime j ∣ valFrom z 0 m)) :
    mult ≤ᵀ X := by
  refine Reduces.of_eventually (d + 5) (c + 4) (2 * M₀) fun n hn => ?_
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [← two_mul]
    have hm : M₀ ≤ m := by omega
    choose D hDd hDs hDe using h m hm
    let D' : ℕ → Circuit (2 * m) := fun j =>
      if hj : 1 ≤ j ∧ j ≤ m then D j hj.1 hj.2 else const false
    refine ⟨multCircuit m D', ?_, ?_, ?_⟩
    · refine (multCircuit_depth_le m D' (d := max d 1) fun j => ?_).trans (by omega)
      simp only [D']; split
      · exact (hDd _ _ _).trans (le_max_left _ _)
      · exact (depth_const _).trans (le_max_right _ _)
    · have hS : ∀ j, (D' j).size ≤ (m + 2) ^ c := fun j => by
        simp only [D']; split
        · exact hDs _ _ _
        · rw [size_const]; exact Nat.one_le_pow _ _ (by omega)
      refine (multCircuit_size_le m D' (Nat.one_le_pow _ _ (by omega)) hS).trans ?_
      calc (2 * m + 2) ^ 4 * (m + 2) ^ c ≤ (2 * m + 2) ^ 4 * (2 * m + 2) ^ c := by
            gcongr; omega
        _ = (2 * m + 2) ^ (c + 4) := by ring
    · refine eval_multCircuit X m D' (fun j hj1 hj2 z => ?_)
      simp only [D', dite_eq_left (show 1 ≤ j ∧ j ≤ m from ⟨hj1, hj2⟩)]
      exact hDe _ _ _ z
  · refine ⟨const false, (depth_const _).trans (by omega), ?_, fun z => ?_⟩
    · rw [size_const]; exact Nat.one_le_pow _ _ (by omega)
    · simp [mult, Nat.add_mod]

end PLB
