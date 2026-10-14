import PrimalityLowerBound.Bits

/-!
# Proposition 3 (2): adding a constant in constant depth

A carry-lookahead adder: bit `i` of `A + C` is `Aᵢ ⊕ Cᵢ ⊕ carryᵢ` where
`carryᵢ = ⋁_{k < i} (Aₖ ∧ Cₖ ∧ ⋀_{k < l < i} (A_l ∨ C_l))`.
The constant `C` is hard-wired.
-/

namespace PLB

open Circuit

/-! ### Arithmetic -/

/-- The carry into position `i` when adding `A` and `C`. -/
def carry (A C i : ℕ) : Bool := decide (2 ^ i ≤ A % 2 ^ i + C % 2 ^ i)

lemma testBit_add_carry (A C i : ℕ) :
    (A + C).testBit i = (A.testBit i ^^ (C.testBit i ^^ carry A C i)) := by
  simp only [Nat.testBit_eq_decide_div_mod_eq, carry]
  rw [Nat.add_div (by positivity)]
  rcases Nat.mod_two_eq_zero_or_one (A / 2 ^ i) with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one (C / 2 ^ i) with hc | hc <;>
  by_cases h : 2 ^ i ≤ A % 2 ^ i + C % 2 ^ i <;>
  simp [h, ha, hc, Nat.add_mod]

lemma mod_two_pow_succ' (x i : ℕ) : x % 2 ^ (i + 1) = 2 ^ i * (x.testBit i).toNat + x % 2 ^ i := by
  rw [Nat.mod_pow_succ, Nat.add_comm, Nat.toNat_testBit]

lemma carry_zero (A C : ℕ) : carry A C 0 = false := by simp [carry, Nat.mod_one]

lemma carry_succ (A C i : ℕ) : carry A C (i + 1) =
    ((A.testBit i && C.testBit i) || ((A.testBit i || C.testBit i) && carry A C i)) := by
  simp only [carry, mod_two_pow_succ']
  have hA : A % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
  have hC : C % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
  rw [pow_succ]
  cases A.testBit i <;> cases C.testBit i <;> simp <;> omega

/-- Carry-lookahead characterisation of the carry. -/
lemma carry_eq_lookahead (A C i : ℕ) : carry A C i = true ↔
    ∃ k < i, (A.testBit k && C.testBit k) = true ∧
      ∀ l, k < l → l < i → (A.testBit l || C.testBit l) = true := by
  induction i with
  | zero => simp [carry_zero]
  | succ i ih =>
    rw [carry_succ]
    simp only [Bool.or_eq_true, Bool.and_eq_true, ih]
    constructor
    · rintro (h | ⟨hp, k, hk, hg, hprop⟩)
      · exact ⟨i, by omega, by simpa using h, fun l h1 h2 => by omega⟩
      · refine ⟨k, by omega, hg, fun l h1 h2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
        · exact hprop l h1 h2
        · simpa using hp
    · rintro ⟨k, hk, hg, hprop⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · right
        refine ⟨by simpa using hprop i hk (by omega), k, hk, hg, fun l h1 h2 => hprop l h1 (by omega)⟩
      · left; simpa using hg

/-! ### Circuits -/

variable {n : ℕ}

/-- `XOR` of two circuits. -/
def xorC (u v : Circuit n) : Circuit n := orL [andL [u, not v], andL [not u, v]]

@[simp] lemma eval_xorC (L : Lang) (z : Fin n → Bool) (u v : Circuit n) :
    (xorC u v).eval L z = (u.eval L z ^^ v.eval L z) := by
  cases hu : u.eval L z <;> cases hv : v.eval L z <;> simp [xorC, hu, hv]

lemma size_xorC_le (u v : Circuit n) : (xorC u v).size ≤ 4 * (u.size + v.size) + 7 := by
  refine (size_orL_le _ (s := 2 * (u.size + v.size + 1) + 1) ?_).trans (by simp; omega)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · refine (size_andL_le _ (s := u.size + v.size + 1) ?_).trans (by simp)
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> (try simp only [size]) <;> omega
  · refine (size_andL_le _ (s := u.size + v.size + 1) ?_).trans (by simp)
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> (try simp only [size]) <;> omega

lemma depth_xorC_le (u v : Circuit n) {d : ℕ} (hu : u.depth ≤ d) (hv : v.depth ≤ d) :
    (xorC u v).depth ≤ d + 3 := by
  refine (depth_orL_le _ (d := d + 2) ?_)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
  · refine depth_andL_le _ fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> (try simp only [depth]) <;> omega

section adder

variable (a : ℕ → Circuit n) (C : ℕ)

/-- "generate" at position `k`: `Aₖ ∧ Cₖ`. -/
def genC (k : ℕ) : Circuit n := if C.testBit k then a k else const false

/-- "propagate" at position `k`: `Aₖ ∨ Cₖ`. -/
def propC (k : ℕ) : Circuit n := if C.testBit k then const true else a k

/-- Carry into position `i`. -/
def carryC (i : ℕ) : Circuit n :=
  orL ((List.range i).map fun k => andL (genC a C k :: (List.range' (k + 1) (i - k - 1)).map
    (propC a C)))

/-- Bit `i` of `A + C`. -/
def sumBitC (i : ℕ) : Circuit n :=
  xorC (if C.testBit i then not (a i) else a i) (carryC a C i)

variable {a C} {L : Lang} {z : Fin n → Bool} {A : ℕ}

lemma eval_genC (ha : ∀ k, (a k).eval L z = A.testBit k) (k : ℕ) :
    (genC a C k).eval L z = (A.testBit k && C.testBit k) := by
  unfold genC; cases h : C.testBit k <;> simp [ha]

lemma eval_propC (ha : ∀ k, (a k).eval L z = A.testBit k) (k : ℕ) :
    (propC a C k).eval L z = (A.testBit k || C.testBit k) := by
  unfold propC; cases h : C.testBit k <;> simp [ha]

lemma eval_carryC (ha : ∀ k, (a k).eval L z = A.testBit k) (i : ℕ) :
    (carryC a C i).eval L z = carry A C i := by
  rw [Bool.eq_iff_iff, carry_eq_lookahead, carryC, eval_orL, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, hce⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
    rw [eval_andL, decide_eq_true_eq] at hce
    refine ⟨k, List.mem_range.1 hk, ?_, fun l h1 h2 => ?_⟩
    · have := hce _ List.mem_cons_self
      rwa [eval_genC ha] at this
    · have := hce (propC a C l) (List.mem_cons_of_mem _ (List.mem_map.2
        ⟨l, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩))
      rwa [eval_propC ha] at this
  · rintro ⟨k, hk, hg, hprop⟩
    refine ⟨_, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩, ?_⟩
    rw [eval_andL, decide_eq_true_eq]
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rwa [eval_genC ha]
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hc
      rw [List.mem_range'_1] at hl
      rw [eval_propC ha]; exact hprop l (by omega) (by omega)

lemma eval_sumBitC (ha : ∀ k, (a k).eval L z = A.testBit k) (i : ℕ) :
    (sumBitC a C i).eval L z = (A + C).testBit i := by
  rw [sumBitC, eval_xorC, eval_carryC ha, testBit_add_carry]
  cases h : C.testBit i <;> simp [ha]

variable {s d : ℕ}

lemma size_carryC_le (hs : ∀ k, (a k).size ≤ s) (i : ℕ) :
    (carryC a C i).size ≤ (i + 1) ^ 2 * (s + 1) := by
  have hg : ∀ k, (genC a C k).size ≤ s + 1 := fun k => by
    unfold genC; split
    · exact (hs k).trans (by omega)
    · rw [size_const]; omega
  have hp : ∀ k, (propC a C k).size ≤ s + 1 := fun k => by
    unfold propC; split
    · rw [size_const]; omega
    · exact (hs k).trans (by omega)
  refine (size_orL_le _ (s := i * (s + 1) + 1) ?_).trans ?_
  · intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
    refine (size_andL_le _ (s := s + 1) ?_).trans ?_
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hg k
      · obtain ⟨l, -, rfl⟩ := List.mem_map.1 hc; exact hp l
    · simp only [List.length_cons, List.length_map, List.length_range']
      have := List.mem_range.1 hk
      have : (i - k - 1 + 1) ≤ i := by omega
      nlinarith
  · simp only [List.length_map, List.length_range]
    nlinarith

lemma size_sumBitC_le (hs : ∀ k, (a k).size ≤ s) (i : ℕ) :
    (sumBitC a C i).size ≤ 16 * (i + 1) ^ 2 * (s + 1) := by
  have h1 : (if C.testBit i then not (a i) else a i).size ≤ s + 1 := by
    split
    · simp only [size]; have := hs i; omega
    · exact (hs i).trans (by omega)
  have h2 := size_carryC_le (C := C) hs i
  refine (size_xorC_le _ _).trans ?_
  have : 1 ≤ (i + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

lemma depth_sumBitC_le (hd : ∀ k, (a k).depth ≤ d) (i : ℕ) :
    (sumBitC a C i).depth ≤ d + 6 := by
  have hg : ∀ k, (genC a C k).depth ≤ d + 1 := fun k => by
    unfold genC; split
    · exact (hd k).trans (by omega)
    · exact (depth_const _).trans (by omega)
  have hp : ∀ k, (propC a C k).depth ≤ d + 1 := fun k => by
    unfold propC; split
    · exact (depth_const _).trans (by omega)
    · exact (hd k).trans (by omega)
  have hc : (carryC a C i).depth ≤ d + 3 := by
    refine depth_orL_le _ fun c hc => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
    refine depth_andL_le _ fun c hc => ?_
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hg k
    · obtain ⟨l, -, rfl⟩ := List.mem_map.1 hc; exact hp l
  have hu : (if C.testBit i then not (a i) else a i).depth ≤ d + 3 := by
    split
    · simp only [depth]; have := hd i; omega
    · exact (hd i).trans (by omega)
  exact depth_xorC_le _ _ hu hc

end adder

end PLB
