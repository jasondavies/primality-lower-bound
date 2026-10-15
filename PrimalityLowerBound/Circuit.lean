import Mathlib

/-!
# Constant-depth circuits with oracle gates

We model unbounded fan-in circuits built from `AND`, `OR`, `NOT` gates and oracle gates for a
single language `L`.  Circuits are represented as formulas (trees).  For constant depth this is
no loss of generality: a DAG circuit of size `s` (gates plus wires) and depth `d` unfolds to a
formula of size at most `(s + 2) ^ (d + 1)` (see `PrimalityLowerBound/DAG.lean`).
-/

namespace PLB

/-- A Boolean function family ("language"): for every input length `n` a Boolean function on
`n` bits.  Bit `i` of the input has weight `2 ^ i` when the input is read as a number. -/
abbrev Lang := (n : ℕ) → (Fin n → Bool) → Bool

/-- The unbounded fan-in gate types: `AND`, `OR` and oracle gates. -/
inductive Op
  | and | or | oracle

/-- The Boolean function computed by a gate of type `op` on `k` input bits (oracle gates
query `L`). -/
def Op.apply (L : Lang) : Op → (k : ℕ) → (Fin k → Bool) → Bool
  | .and, _, b => decide (∀ i, b i = true)
  | .or, _, b => decide (∃ i, b i = true)
  | .oracle, k, b => L k b

/-- Unbounded fan-in circuits (formulas) on `n` inputs with `AND`, `OR`, `NOT` and oracle gates. -/
inductive Circuit (n : ℕ) : Type where
  | input : Fin n → Circuit n
  | not : Circuit n → Circuit n
  | gate : Op → {k : ℕ} → (Fin k → Circuit n) → Circuit n

namespace Circuit

variable {n m : ℕ}

/-- `AND` gate. -/
abbrev and {k : ℕ} (cs : Fin k → Circuit n) : Circuit n := gate .and cs
/-- `OR` gate. -/
abbrev or {k : ℕ} (cs : Fin k → Circuit n) : Circuit n := gate .or cs
/-- Oracle gate. -/
abbrev oracle {k : ℕ} (cs : Fin k → Circuit n) : Circuit n := gate .oracle cs

/-- Evaluate a circuit whose oracle gates query the language `L`. -/
def eval (L : Lang) (x : Fin n → Bool) : Circuit n → Bool
  | input i => x i
  | not c => !(c.eval L x)
  | gate op cs => op.apply L _ (fun i => (cs i).eval L x)

/-- Number of gates (nodes) of the circuit. -/
def size : Circuit n → ℕ
  | input _ => 1
  | not c => c.size + 1
  | gate _ cs => (∑ i, (cs i).size) + 1

/-- Length of the longest path from an input to the output. -/
def depth : Circuit n → ℕ
  | input _ => 0
  | not c => c.depth + 1
  | gate _ cs => (Finset.univ.sup fun i => (cs i).depth) + 1

@[simp] lemma eval_input (L : Lang) (x : Fin n → Bool) (i : Fin n) :
    (input i).eval L x = x i := rfl
@[simp] lemma eval_not (L : Lang) (x : Fin n → Bool) (c : Circuit n) :
    (not c).eval L x = !(c.eval L x) := rfl
lemma eval_gate (L : Lang) (x : Fin n → Bool) (op : Op) {k : ℕ} (cs : Fin k → Circuit n) :
    (gate op cs).eval L x = op.apply L k (fun i => (cs i).eval L x) := rfl
@[simp] lemma eval_and (L : Lang) (x : Fin n → Bool) {k : ℕ} (cs : Fin k → Circuit n) :
    (and cs).eval L x = decide (∀ i, (cs i).eval L x = true) := rfl
@[simp] lemma eval_or (L : Lang) (x : Fin n → Bool) {k : ℕ} (cs : Fin k → Circuit n) :
    (or cs).eval L x = decide (∃ i, (cs i).eval L x = true) := rfl
@[simp] lemma eval_oracle (L : Lang) (x : Fin n → Bool) {k : ℕ} (cs : Fin k → Circuit n) :
    (oracle cs).eval L x = L k (fun i => (cs i).eval L x) := rfl

lemma size_pos (c : Circuit n) : 1 ≤ c.size := by
  cases c <;> simp [size]

lemma size_child_le {k : ℕ} (cs : Fin k → Circuit n) (i : Fin k) :
    (cs i).size ≤ ∑ j, (cs j).size :=
  Finset.single_le_sum (f := fun j => (cs j).size) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma fanin_le {k : ℕ} (cs : Fin k → Circuit n) : k ≤ ∑ j, (cs j).size := by
  calc k = ∑ _j : Fin k, 1 := by simp
    _ ≤ ∑ j, (cs j).size := Finset.sum_le_sum fun j _ => size_pos (cs j)

lemma depth_child_le {k : ℕ} (cs : Fin k → Circuit n) (i : Fin k) :
    (cs i).depth ≤ Finset.univ.sup fun j => (cs j).depth :=
  Finset.le_sup (f := fun j => (cs j).depth) (Finset.mem_univ i)

/-! ### Size and depth bounds for gates -/

lemma size_gate_le (op : Op) {k : ℕ} (cs : Fin k → Circuit n) {s : ℕ}
    (h : ∀ i, (cs i).size ≤ s) : (gate op cs).size ≤ k * s + 1 := by
  simp only [size]
  have := Finset.sum_le_sum (s := Finset.univ) fun i _ => h i
  simp at this; omega

lemma depth_gate_le (op : Op) {k : ℕ} (cs : Fin k → Circuit n) {d : ℕ}
    (h : ∀ i, (cs i).depth ≤ d) : (gate op cs).depth ≤ d + 1 := by
  simp only [depth]; gcongr; exact Finset.sup_le fun i _ => h i

/-! ### Substitution of circuits for inputs -/

/-- Replace input `i` by the circuit `σ i`. -/
def subst (σ : Fin m → Circuit n) : Circuit m → Circuit n
  | input i => σ i
  | not c => not (c.subst σ)
  | gate op cs => gate op fun i => (cs i).subst σ

lemma eval_subst (L : Lang) (σ : Fin m → Circuit n) (x : Fin n → Bool) (c : Circuit m) :
    (c.subst σ).eval L x = c.eval L (fun i => (σ i).eval L x) := by
  induction c with
  | input i => rfl
  | not c ih => simp [subst, ih]
  | gate op cs ih => simp only [subst, eval_gate, ih]

lemma size_subst_le (σ : Fin m → Circuit n) {s : ℕ} (hσ : ∀ i, (σ i).size ≤ s) (hs : 1 ≤ s)
    (c : Circuit m) : (c.subst σ).size ≤ c.size * s := by
  induction c with
  | input i => simpa [subst, size] using hσ i
  | not c ih => simp only [subst, size]; nlinarith
  | gate op cs ih =>
    simp only [subst, size, add_mul, Finset.sum_mul]
    gcongr with i
    · exact ih i
    · simpa using hs

lemma depth_subst_le (σ : Fin m → Circuit n) {d : ℕ} (hσ : ∀ i, (σ i).depth ≤ d)
    (c : Circuit m) : (c.subst σ).depth ≤ c.depth + d := by
  induction c with
  | input i => simpa [subst, depth] using hσ i
  | not c ih => simp only [subst, depth]; omega
  | gate op cs ih =>
    simp only [subst, depth]
    have : (Finset.univ.sup fun i => ((cs i).subst σ).depth) ≤
        (Finset.univ.sup fun i => (cs i).depth) + d :=
      Finset.sup_le fun i _ => (ih i).trans (by gcongr; exact depth_child_le cs i)
    omega

/-! ### Replacing oracle gates by circuits -/

/-- Replace every oracle gate of fan-in `k` by the circuit `E k`. -/
def compose (E : (k : ℕ) → Circuit k) : Circuit n → Circuit n
  | input i => input i
  | not c => not (c.compose E)
  | gate .and cs => and fun i => (cs i).compose E
  | gate .or cs => or fun i => (cs i).compose E
  | gate .oracle cs => (E _).subst fun i => (cs i).compose E

/-- Composition is correct as long as `E k` is correct for the fan-ins `k` that occur. -/
lemma eval_compose_of_le (L L' : Lang) (E : (k : ℕ) → Circuit k) (x : Fin n → Bool)
    (c : Circuit n) (hE : ∀ k ≤ c.size, ∀ y, (E k).eval L' y = L k y) :
    (c.compose E).eval L' x = c.eval L x := by
  induction c with
  | input i => rfl
  | not c ih => simp only [compose, eval_not, ih fun k hk => hE k (by simp [size]; omega)]
  | @gate op k cs ih =>
    have hc : ∀ i, ((cs i).compose E).eval L' x = (cs i).eval L x := fun i =>
      ih i fun k hk => hE k (by have := size_child_le cs i; simp [size]; omega)
    cases op
    case oracle =>
      simp only [compose, eval_subst, eval_gate, Op.apply, hc]
      exact hE k (by have := fanin_le cs; simp [size]; omega) _
    all_goals simp only [compose, eval_gate, hc]; rfl

lemma eval_compose (L L' : Lang) (E : (k : ℕ) → Circuit k)
    (hE : ∀ k y, (E k).eval L' y = L k y) (x : Fin n → Bool) (c : Circuit n) :
    (c.compose E).eval L' x = c.eval L x :=
  eval_compose_of_le L L' E x c fun k _ => hE k

lemma depth_compose_le (E : (k : ℕ) → Circuit k) {dE : ℕ} (hE : ∀ k, (E k).depth ≤ dE)
    (c : Circuit n) : (c.compose E).depth ≤ c.depth * (dE + 1) := by
  induction c with
  | input i => simp [compose, depth]
  | not c ih => simp only [compose, depth]; nlinarith
  | @gate op k cs ih =>
    have hsup : (Finset.univ.sup fun i => ((cs i).compose E).depth) ≤
        (Finset.univ.sup fun i => (cs i).depth) * (dE + 1) :=
      Finset.sup_le fun i _ => (ih i).trans (by gcongr; exact depth_child_le cs i)
    cases op
    case oracle =>
      simp only [compose]
      have h1 := depth_subst_le (fun i => (cs i).compose E)
        (d := (Finset.univ.sup fun i => (cs i).depth) * (dE + 1))
        (fun i => (ih i).trans (Nat.mul_le_mul_right _ (depth_child_le cs i))) (E _)
      simp only [depth]; nlinarith [hE k]
    all_goals simp only [compose, depth]; nlinarith

lemma size_compose_le (E : (k : ℕ) → Circuit k) {Q : ℕ} (hQ : 1 ≤ Q) (c : Circuit n)
    (hE : ∀ k ≤ c.size, (E k).size ≤ Q) : (c.compose E).size ≤ c.size * Q ^ c.depth := by
  induction c with
  | input i => simp [compose, size, depth]
  | not c ih =>
    simp only [compose, size, depth] at *
    have := ih (fun k hk => hE k (by omega))
    have h1 : Q ^ c.depth ≤ Q ^ (c.depth + 1) := Nat.pow_le_pow_right hQ (by omega)
    have h2 : 1 ≤ Q ^ (c.depth + 1) := Nat.one_le_pow _ _ hQ
    nlinarith
  | @gate op k cs ih =>
    set D := Finset.univ.sup fun i => (cs i).depth
    set T := ∑ i, (cs i).size
    have hE' : ∀ k ≤ T + 1, (E k).size ≤ Q := hE
    clear hE
    show (compose E (gate op cs)).size ≤ (T + 1) * Q ^ (D + 1)
    have hi : ∀ i, ((cs i).compose E).size ≤ (cs i).size * Q ^ D := fun i =>
      (ih i fun k hk => hE' k (by have := size_child_le cs i; omega)).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hQ (depth_child_le cs i)))
    have hQD : Q ^ D ≤ Q ^ (D + 1) := Nat.pow_le_pow_right hQ (by omega)
    have h1 : 1 ≤ Q ^ D := Nat.one_le_pow _ _ hQ
    have hsum : ∑ i, ((cs i).compose E).size ≤ T * Q ^ D := by
      rw [Finset.sum_mul]; exact Finset.sum_le_sum fun i _ => hi i
    cases op
    case oracle =>
      have hs := size_subst_le (fun i => (cs i).compose E) (s := T * Q ^ D + 1)
        (fun i => ((hi i).trans (Nat.mul_le_mul_right _ (size_child_le cs i))).trans
          (Nat.le_succ _)) (by omega) (E k)
      have hEk := hE' k (by have := fanin_le cs; omega)
      have h3 : Q ≤ Q ^ (D + 1) := by
        calc Q = Q ^ 1 := (pow_one Q).symm
          _ ≤ Q ^ (D + 1) := Nat.pow_le_pow_right hQ (by omega)
      calc ((E k).subst fun i => (cs i).compose E).size ≤ (E k).size * (T * Q ^ D + 1) := hs
        _ ≤ Q * (T * Q ^ D + 1) := Nat.mul_le_mul_right _ hEk
        _ = T * Q ^ (D + 1) + Q := by ring
        _ ≤ T * Q ^ (D + 1) + Q ^ (D + 1) := by gcongr
        _ = (T + 1) * Q ^ (D + 1) := by ring
    all_goals
      simp only [compose, size]
      calc (∑ i, ((cs i).compose E).size) + 1 ≤ T * Q ^ D + 1 := by omega
        _ ≤ T * Q ^ (D + 1) + Q ^ (D + 1) := by gcongr; omega
        _ = (T + 1) * Q ^ (D + 1) := by ring

/-! ### Basic gadgets -/

/-- Constant circuit (an empty `AND` is true, an empty `OR` is false). -/
def const (b : Bool) : Circuit n := if b then and (k := 0) Fin.elim0 else or (k := 0) Fin.elim0

@[simp] lemma eval_const (L : Lang) (x : Fin n → Bool) (b : Bool) :
    (const b : Circuit n).eval L x = b := by
  cases b <;> simp [const]

lemma size_const (b : Bool) : (const b : Circuit n).size = 1 := by
  cases b <;> simp [const, size]

lemma depth_const_eq (b : Bool) : (const b : Circuit n).depth = 1 := by
  cases b <;> simp [const, depth]

lemma depth_const (b : Bool) : (const b : Circuit n).depth ≤ 1 := (depth_const_eq b).le

/-- A wire: input `j`, or the constant `false` for `none`. -/
def wire : Option (Fin n) → Circuit n
  | some j => input j
  | none => const false

@[simp] lemma eval_wire (L : Lang) (x : Fin n → Bool) (o : Option (Fin n)) :
    (wire o).eval L x = o.elim false x := by
  cases o <;> simp [wire]

lemma size_wire (o : Option (Fin n)) : (wire o).size = 1 := by
  cases o <;> simp [wire, size, size_const]

lemma depth_wire_le (o : Option (Fin n)) : (wire o).depth ≤ 1 := by
  cases o <;> simp [wire, depth, depth_const]

/-- Literal: input `i` equals `b`. -/
def lit (i : Fin n) (b : Bool) : Circuit n := if b then input i else not (input i)

@[simp] lemma eval_lit (L : Lang) (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    (lit i b).eval L x = decide (x i = b) := by
  cases b <;> cases h : x i <;> simp [lit, h]

lemma size_lit_le (i : Fin n) (b : Bool) : (lit i b).size ≤ 2 := by
  cases b <;> simp [lit, size]

lemma depth_lit_le (i : Fin n) (b : Bool) : (lit i b).depth ≤ 1 := by
  cases b <;> simp [lit, depth]

/-- `AND` of a list of circuits. -/
def andL (l : List (Circuit n)) : Circuit n := and (k := l.length) l.get

/-- `OR` of a list of circuits. -/
def orL (l : List (Circuit n)) : Circuit n := or (k := l.length) l.get

@[simp] lemma eval_andL (L : Lang) (x : Fin n → Bool) (l : List (Circuit n)) :
    (andL l).eval L x = decide (∀ c ∈ l, c.eval L x = true) := by
  simp only [andL, eval_and, decide_eq_decide, List.mem_iff_get]
  constructor
  · rintro h c ⟨i, rfl⟩; exact h i
  · intro h i; exact h _ ⟨i, rfl⟩

@[simp] lemma eval_orL (L : Lang) (x : Fin n → Bool) (l : List (Circuit n)) :
    (orL l).eval L x = decide (∃ c ∈ l, c.eval L x = true) := by
  simp only [orL, eval_or, decide_eq_decide, List.mem_iff_get]
  constructor
  · rintro ⟨i, h⟩; exact ⟨_, ⟨i, rfl⟩, h⟩
  · rintro ⟨c, ⟨i, rfl⟩, h⟩; exact ⟨i, h⟩

lemma size_andL_le (l : List (Circuit n)) {s : ℕ} (h : ∀ c ∈ l, c.size ≤ s) :
    (andL l).size ≤ l.length * s + 1 :=
  size_gate_le _ _ fun _ => h _ (List.get_mem _ _)

lemma size_orL_le (l : List (Circuit n)) {s : ℕ} (h : ∀ c ∈ l, c.size ≤ s) :
    (orL l).size ≤ l.length * s + 1 :=
  size_gate_le _ _ fun _ => h _ (List.get_mem _ _)

lemma depth_andL_le (l : List (Circuit n)) {d : ℕ} (h : ∀ c ∈ l, c.depth ≤ d) :
    (andL l).depth ≤ d + 1 :=
  depth_gate_le _ _ fun _ => h _ (List.get_mem _ _)

lemma depth_orL_le (l : List (Circuit n)) {d : ℕ} (h : ∀ c ∈ l, c.depth ≤ d) :
    (orL l).depth ≤ d + 1 :=
  depth_gate_le _ _ fun _ => h _ (List.get_mem _ _)

/-- Brute-force disjunctive normal form of an arbitrary Boolean function. -/
noncomputable def dnf (f : (Fin n → Bool) → Bool) : Circuit n :=
  orL (((Finset.univ.filter fun a => f a = true).toList).map
    fun a => and fun i => lit i (a i))

@[simp] lemma eval_dnf (L : Lang) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (dnf f).eval L x = f x := by
  rw [dnf, eval_orL]
  cases hfx : f x
  · simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro c hc hce
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    simp only [eval_and, eval_lit, decide_eq_true_eq] at hce
    have : x = a := funext hce
    subst this; simp_all
  · simp only [decide_eq_true_eq]
    refine ⟨and fun i => lit i (x i), ?_, by simp⟩
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hfx, rfl⟩

lemma size_dnf_le (f : (Fin n → Bool) → Bool) : (dnf f).size ≤ 2 ^ n * (2 * n + 1) + 1 := by
  refine (size_orL_le _ (s := 2 * n + 1) ?_).trans ?_
  · simp only [List.mem_map, Finset.mem_toList]
    rintro c ⟨a, -, rfl⟩
    exact (size_gate_le _ _ fun i => size_lit_le i (a i)).trans (by simp; omega)
  · simp only [List.length_map, Finset.length_toList]
    gcongr
    calc _ ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_filter_le _ _
      _ = 2 ^ n := by simp

lemma depth_dnf_le (f : (Fin n → Bool) → Bool) : (dnf f).depth ≤ 3 := by
  refine depth_orL_le _ ?_
  simp only [List.mem_map, Finset.mem_toList]
  rintro c ⟨a, -, rfl⟩
  exact depth_gate_le _ _ fun i => depth_lit_le i (a i)

end Circuit

open Circuit

/-! ## AC⁰ Turing reductions -/

/-- `A ≤ᵀ B`: `A` is recognised by a family of polynomial-size, constant-depth circuits of
`AND`, `OR`, `NOT` and oracle gates for `B` (non-uniform `AC⁰` Turing reducibility). -/
def Reduces (A B : Lang) : Prop :=
  ∃ d c : ℕ, ∀ n, ∃ C : Circuit n, C.depth ≤ d ∧ C.size ≤ (n + 2) ^ c ∧ ∀ x, C.eval B x = A n x

@[inherit_doc] infix:50 " ≤ᵀ " => Reduces

/-- `AC⁰[L]`: the languages `AC⁰`-Turing reducible to `L`. -/
def AC0 (L : Lang) : Set Lang := {A | A ≤ᵀ L}

lemma Reduces.refl (A : Lang) : A ≤ᵀ A := by
  refine ⟨1, 1, fun n => ⟨oracle (k := n) input, ?_, ?_, fun x => rfl⟩⟩
  · exact depth_gate_le _ _ fun _ => by simp [depth]
  · refine (size_gate_le _ _ (s := 1) fun i => by simp [size]).trans ?_
    simp

lemma add_two_le_pow {n a c : ℕ} (h : a ≤ (n + 2) ^ c) : a + 2 ≤ (n + 2) ^ (c + 2) := by
  have h1 : 1 ≤ (n + 2) ^ c := Nat.one_le_pow _ _ (by omega)
  have h2 : 4 ≤ (n + 2) ^ 2 := by rw [sq]; nlinarith
  rw [pow_add]; nlinarith

lemma Reduces.trans {A B D : Lang} (hAB : A ≤ᵀ B) (hBD : B ≤ᵀ D) : A ≤ᵀ D := by
  obtain ⟨d₁, c₁, h₁⟩ := hAB
  obtain ⟨d₂, c₂, h₂⟩ := hBD
  choose E hEd hEs hEe using h₂
  refine ⟨d₁ * (d₂ + 1), c₁ + (c₁ + 2) * c₂ * d₁, fun n => ?_⟩
  obtain ⟨C, hCd, hCs, hCe⟩ := h₁ n
  refine ⟨C.compose E, ?_, ?_, fun x => by rw [eval_compose B D E hEe, hCe]⟩
  · exact (depth_compose_le E hEd C).trans (Nat.mul_le_mul_right _ hCd)
  · have hQ : 1 ≤ (n + 2) ^ ((c₁ + 2) * c₂) := Nat.one_le_pow _ _ (by omega)
    have hE : ∀ k ≤ C.size, (E k).size ≤ (n + 2) ^ ((c₁ + 2) * c₂) := fun k hk =>
      (hEs k).trans <| by
        rw [pow_mul]
        exact Nat.pow_le_pow_left (by have := add_two_le_pow hCs; omega) _
    calc (C.compose E).size ≤ C.size * ((n + 2) ^ ((c₁ + 2) * c₂)) ^ C.depth :=
          size_compose_le E hQ C hE
      _ ≤ (n + 2) ^ c₁ * ((n + 2) ^ ((c₁ + 2) * c₂)) ^ d₁ :=
          Nat.mul_le_mul hCs (Nat.pow_le_pow_right hQ hCd)
      _ = (n + 2) ^ (c₁ + (c₁ + 2) * c₂ * d₁) := by rw [← pow_mul, ← pow_add]

/-- To establish a reduction it suffices to handle all sufficiently long inputs: short inputs are
handled by brute-force DNFs. -/
lemma Reduces.of_eventually {A B : Lang} (d c N : ℕ)
    (h : ∀ n ≥ N, ∃ C : Circuit n, C.depth ≤ d ∧ C.size ≤ (n + 2) ^ c ∧
      ∀ x, C.eval B x = A n x) : A ≤ᵀ B := by
  set S := 2 ^ N * (2 * N + 1) + 1
  refine ⟨max d 3, max c S, fun n => ?_⟩
  by_cases hn : N ≤ n
  · obtain ⟨C, h1, h2, h3⟩ := h n hn
    exact ⟨C, h1.trans (le_max_left _ _),
      h2.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _)), h3⟩
  · refine ⟨dnf (A n), (depth_dnf_le _).trans (le_max_right _ _), ?_, fun x => by simp⟩
    calc (dnf (A n)).size ≤ 2 ^ n * (2 * n + 1) + 1 := size_dnf_le _
      _ ≤ S := by
          have : 2 ^ n ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
          simp only [S]; gcongr; omega
      _ ≤ 2 ^ S := (Nat.lt_two_pow_self).le
      _ ≤ (n + 2) ^ S := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + 2) ^ max c S := Nat.pow_le_pow_right (by omega) (le_max_right _ _)

lemma AC0.subset_of_reduces {A B : Lang} (h : A ≤ᵀ B) : AC0 A ⊆ AC0 B :=
  fun _ hX => Reduces.trans hX h

end PLB
