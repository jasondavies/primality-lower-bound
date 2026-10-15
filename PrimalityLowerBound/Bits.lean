import PrimalityLowerBound.Circuit

/-!
# Bit strings and the numbers they represent

A bit string `x = x_{n-1} … x_0` represents `∑ xᵢ 2ⁱ`.
-/

namespace PLB

/-- Bit `i` of a bit string (`false` beyond its length). -/
def getD {n : ℕ} (z : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then z ⟨i, h⟩ else false

lemma getD_of_lt {n : ℕ} (z : Fin n → Bool) {i : ℕ} (h : i < n) : getD z i = z ⟨i, h⟩ := by
  simp [getD, h]

lemma getD_of_ge {n : ℕ} (z : Fin n → Bool) {i : ℕ} (h : n ≤ i) : getD z i = false := by
  simp [getD, show ¬ i < n by omega]

@[simp] lemma getD_fin {n : ℕ} (z : Fin n → Bool) (i : Fin n) : getD z i = z i := by
  simp [getD]

/-- The position `s` as an index into a string of length `n`, if `s < n`. -/
def idx (n s : ℕ) : Option (Fin n) := if h : s < n then some ⟨s, h⟩ else none

@[simp] lemma elim_idx {n : ℕ} (z : Fin n → Bool) (s : ℕ) : (idx n s).elim false z = getD z s := by
  unfold idx getD; split <;> rfl

/-- `bitsVal b len = ∑_{i < len} bᵢ 2ⁱ`. -/
def bitsVal (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | len + 1 => (b 0).toNat + 2 * bitsVal (fun i => b (i + 1)) len

lemma bitsVal_lt (b : ℕ → Bool) (len : ℕ) : bitsVal b len < 2 ^ len := by
  induction len generalizing b with
  | zero => simp [bitsVal]
  | succ len ih =>
    have := ih (fun i => b (i + 1))
    have : (b 0).toNat ≤ 1 := Bool.toNat_le _
    simp only [bitsVal, pow_succ]; omega

lemma testBit_bitsVal (b : ℕ → Bool) (len i : ℕ) :
    (bitsVal b len).testBit i = (decide (i < len) && b i) := by
  induction len generalizing b i with
  | zero => simp [bitsVal]
  | succ len ih =>
    have hb : (b 0).toNat ≤ 1 := Bool.toNat_le _
    cases i with
    | zero =>
      simp only [bitsVal, Nat.testBit_zero]
      cases b 0 <;> simp [Nat.add_mul_mod_self_left]
    | succ i =>
      simp only [bitsVal, Nat.testBit_succ]
      have : ((b 0).toNat + 2 * bitsVal (fun i => b (i + 1)) len) / 2 =
          bitsVal (fun i => b (i + 1)) len := by omega
      rw [this, ih]
      simp

lemma bitsVal_eq_of_testBit {b : ℕ → Bool} {len V : ℕ} (h : ∀ i < len, b i = V.testBit i)
    (hV : V < 2 ^ len) : bitsVal b len = V := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitsVal]
  by_cases hi : i < len
  · simp [hi, h i hi]
  · simp only [hi, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hV
      (Nat.pow_le_pow_right (by omega) (by omega)))).symm

lemma bitsVal_congr {b b' : ℕ → Bool} {len : ℕ} (h : ∀ i < len, b i = b' i) :
    bitsVal b len = bitsVal b' len := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitsVal, testBit_bitsVal]
  by_cases hi : i < len <;> simp [hi, h]

lemma bitsVal_add (b : ℕ → Bool) (a c : ℕ) :
    bitsVal b (a + c) = bitsVal b a + 2 ^ a * bitsVal (fun i => b (a + i)) c := by
  induction a generalizing b with
  | zero => simp [bitsVal]
  | succ a ih =>
    rw [show a + 1 + c = (a + c) + 1 by omega]
    simp only [bitsVal]
    rw [ih]
    have : (fun i => b (a + 1 + i)) = (fun i => (fun j => b (j + 1)) (a + i)) := by
      funext i; congr 1; omega
    rw [this, pow_succ]; ring

lemma bitsVal_blocks (b : ℕ → Bool) (L k : ℕ) :
    bitsVal b (L * k) = ∑ j ∈ Finset.range k, 2 ^ (L * j) * bitsVal (fun s => b (L * j + s)) L := by
  induction k with
  | zero => simp [bitsVal]
  | succ k ih => rw [Nat.mul_succ, bitsVal_add, ih, Finset.sum_range_succ]

lemma bitsVal_eq_sum (b : ℕ → Bool) (len : ℕ) :
    bitsVal b len = ∑ i ∈ Finset.range len, (b i).toNat * 2 ^ i := by
  induction len with
  | zero => simp [bitsVal]
  | succ len ih =>
    have := bitsVal_add b len 1
    rw [this, ih, Finset.sum_range_succ]
    simp [bitsVal]; ring

/-- The number represented by a bit string. -/
def val {n : ℕ} (z : Fin n → Bool) : ℕ := bitsVal (getD z) n

/-- The number represented by the substring of length `len` starting at position `s`. -/
def valFrom {n : ℕ} (z : Fin n → Bool) (s len : ℕ) : ℕ := bitsVal (fun i => getD z (s + i)) len

lemma val_lt {n : ℕ} (z : Fin n → Bool) : val z < 2 ^ n := bitsVal_lt _ _

lemma valFrom_lt {n : ℕ} (z : Fin n → Bool) (s len : ℕ) : valFrom z s len < 2 ^ len :=
  bitsVal_lt _ _

/-- Number of ones in a bit string. -/
def ones {n : ℕ} (z : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => z i = true).card

lemma ones_eq_fin_sum {n : ℕ} (z : Fin n → Bool) : ones z = ∑ i, (z i).toNat := by
  rw [ones, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases z i <;> simp

lemma ones_eq_sum {n : ℕ} (z : Fin n → Bool) :
    ones z = ∑ i ∈ Finset.range n, (getD z i).toNat := by
  rw [ones_eq_fin_sum, ← Fin.sum_univ_eq_sum_range (fun i => (getD z i).toNat)]
  simp

lemma ones_le {n : ℕ} (z : Fin n → Bool) : ones z ≤ n := by
  calc ones z ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

end PLB
