import PrimalityLowerBound.Circuit

/-!
# Circuits as directed acyclic graphs

The paper defines circuits as DAGs whose size is the number of gates.  Our main development
uses formulas (`Circuit`).  Here we define DAG circuits and show that both models give the same
notion of `AC⁰` Turing reducibility: a formula is a DAG, and a DAG of size `s` and depth `d`
unfolds to a formula of size at most `(s + 2) ^ (d + 1)`, which is polynomial for constant depth.

A DAG is a list of gates evaluated in order; a gate reads input bits (`Sum.inl i`) and earlier
gates (`Sum.inr d` is the gate `d + 1` positions earlier).  The last gate is the output.  The
size counts gates and wires (a fan-in `k` oracle gate needs `k` wires).
-/

namespace PLB

open Circuit

inductive GateKind
  | not | and | or | oracle

/-- A gate: its kind and its ordered list of input wires. -/
structure Gate (n : ℕ) where
  kind : GateKind
  wires : List (Fin n ⊕ ℕ)

variable {n : ℕ}

/-- Run gates in order, storing the results most-recent-first (so `Sum.inr d` is index `d`). -/
def runGates {α : Type} (step : Gate n → List α → α) : List α → List (Gate n) → List α
  | acc, [] => acc
  | acc, g :: gs => runGates step (step g acc :: acc) gs

lemma runGates_append {α : Type} (step : Gate n → List α → α) (acc : List α) (gs gs' : List (Gate n)) :
    runGates step acc (gs ++ gs') = runGates step (runGates step acc gs) gs' := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih => exact ih _

lemma length_runGates {α : Type} (step : Gate n → List α → α) (acc : List α) (gs : List (Gate n)) :
    (runGates step acc gs).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [runGates]
  | cons g gs ih => simp only [runGates, ih, List.length_cons]; omega

/-- Gate `i` of `gs` only reads gates of `gs` before it. -/
def LocalGates (gs : List (Gate n)) : Prop :=
  ∀ i (h : i < gs.length), ∀ d, Sum.inr d ∈ gs[i].wires → d < i

/-- A step function that only reads the referenced entries. -/
def StepLocal {α : Type} (step : Gate n → List α → α) : Prop :=
  ∀ g l₁ l₂, (∀ d, Sum.inr d ∈ g.wires → d < l₁.length) → step g (l₁ ++ l₂) = step g l₁

lemma runGates_prefix {α : Type} {step : Gate n → List α → α} (hs : StepLocal step)
    (gs : List (Gate n)) (acc pre : List α)
    (hloc : ∀ i (h : i < gs.length), ∀ d, Sum.inr d ∈ gs[i].wires → d < acc.length + i) :
    runGates step (acc ++ pre) gs = runGates step acc gs ++ pre := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [runGates]
    rw [hs g acc pre (fun d hd => by simpa using hloc 0 (by simp) d hd)]
    rw [← List.cons_append, ih]
    intro i h d hd
    have := hloc (i + 1) (by simpa using h) d (by simpa using hd)
    simp only [List.length_cons]; omega

lemma runGates_local {α : Type} {step : Gate n → List α → α} (hs : StepLocal step)
    {gs : List (Gate n)} (hloc : LocalGates gs) (pre : List α) :
    runGates step pre gs = runGates step [] gs ++ pre := by
  have := runGates_prefix hs gs [] pre (fun i h d hd => by simpa using hloc i h d hd)
  simpa using this

lemma LocalGates.append {gs gs' : List (Gate n)} (h : LocalGates gs) (h' : LocalGates gs') :
    LocalGates (gs ++ gs') := by
  intro i hi d hd
  by_cases hil : i < gs.length
  · rw [List.getElem_append_left hil] at hd; exact h i hil d hd
  · rw [List.getElem_append_right (by omega)] at hd
    have := h' (i - gs.length) (by simp at hi; omega) d hd
    omega

lemma LocalGates.flatten {bs : List (List (Gate n))} (h : ∀ b ∈ bs, LocalGates b) :
    LocalGates bs.flatten := by
  induction bs with
  | nil => intro i hi; simp at hi
  | cons b bs ih =>
    rw [List.flatten_cons]
    exact (h b (by simp)).append (ih fun b' hb' => h b' (by simp [hb']))

lemma runGates_flatten {α : Type} {step : Gate n → List α → α} (hs : StepLocal step)
    (bs : List (List (Gate n))) (h : ∀ b ∈ bs, LocalGates b) :
    runGates step [] bs.flatten = (bs.map (runGates step [])).reverse.flatten := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.flatten_cons, runGates_append,
      runGates_local hs (LocalGates.flatten fun b' hb' => h b' (by simp [hb'])),
      ih fun b' hb' => h b' (by simp [hb'])]
    simp

lemma getD_reverse_flatten {α : Type} (Rs : List (List α)) (a : α) (i : ℕ) (hi : i < Rs.length)
    (hne : ∀ R ∈ Rs, R ≠ []) :
    Rs.reverse.flatten.getD ((Rs.drop (i + 1)).map List.length).sum a = Rs[i].headD a := by
  induction Rs generalizing i with
  | nil => simp at hi
  | cons R Rs ih =>
    rw [List.reverse_cons, List.flatten_append]
    have hlen : (Rs.reverse.flatten).length = (Rs.map List.length).sum := by
      simp [List.length_flatten, List.map_reverse, List.sum_reverse]
    rcases i with _ | i
    · simp only [zero_add, List.drop_one, List.tail_cons, List.getElem_cons_zero]
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]), hlen, Nat.sub_self]
      simp
      cases R with
      | nil => exact absurd rfl (hne _ (by simp))
      | cons r R => simp
    · simp only [List.drop_succ_cons, List.getElem_cons_succ]
      have hi' : i < Rs.length := by simpa using hi
      have hlt : ((Rs.drop (i + 1)).map List.length).sum < (Rs.reverse.flatten).length := by
        rw [hlen]
        conv_rhs => rw [← List.take_append_drop (i + 1) Rs]
        rw [List.map_append, List.sum_append]
        have : 0 < ((Rs.take (i + 1)).map List.length).sum := by
          have hmem : Rs[i] ∈ Rs.take (i + 1) := by
            rw [List.mem_iff_getElem]
            exact ⟨i, by simp; omega, by simp⟩
          have hpos : 0 < Rs[i].length := List.length_pos_iff.2 (hne _ (by simp))
          exact lt_of_lt_of_le hpos (List.le_sum_of_mem (List.mem_map_of_mem hmem))
        omega
      rw [List.getD_append _ _ _ _ hlt]
      exact ih i hi' fun R hR => hne R (by simp [hR])

/-! ### Gate semantics -/

/-- Uniform shape of the gate functions: `F m args`. -/
lemma ofFn_get_apply {α β : Type} (F : (m : ℕ) → (Fin m → Bool) → β) {k : ℕ} (f : Fin k → α)
    (g : α → Bool) :
    F (List.ofFn f).length (fun i => g ((List.ofFn f).get i)) = F k (fun i => g (f i)) := by
  have h : (List.ofFn f).length = k := List.length_ofFn
  congr 1
  exact (Fin.heq_fun_iff h).2 fun i => by simp

/-- `AND` of `m` bits. -/
def allFin (m : ℕ) (b : Fin m → Bool) : Bool := decide (∀ i, b i = true)
/-- `OR` of `m` bits. -/
def anyFin (m : ℕ) (b : Fin m → Bool) : Bool := decide (∃ i, b i = true)

namespace Gate

/-- Value of a wire. -/
def argVal (x : Fin n → Bool) (prev : List Bool) (w : Fin n ⊕ ℕ) : Bool :=
  Sum.elim x (fun d => prev.getD d false) w

/-- Output of a gate given the input `x` and the values of the previous gates. -/
def apply (L : Lang) (x : Fin n → Bool) (g : Gate n) (prev : List Bool) : Bool :=
  match g.kind with
  | .not => !(if h : 0 < g.wires.length then argVal x prev (g.wires.get ⟨0, h⟩) else false)
  | .and => allFin _ fun i => argVal x prev (g.wires.get i)
  | .or => anyFin _ fun i => argVal x prev (g.wires.get i)
  | .oracle => L _ fun i => argVal x prev (g.wires.get i)

/-- Depth of a wire. -/
def argDepth (prev : List ℕ) (w : Fin n ⊕ ℕ) : ℕ := Sum.elim (fun _ => 0) (fun d => prev.getD d 0) w

/-- Depth of a gate (longest path from an input). -/
def depthStep (g : Gate n) (prev : List ℕ) : ℕ := (g.wires.map (argDepth prev)).foldr max 0 + 1

/-- Formula of a wire. -/
def argCirc (prev : List (Circuit n)) (w : Fin n ⊕ ℕ) : Circuit n :=
  Sum.elim input (fun d => prev.getD d (const false)) w

/-- Formula of a gate given the formulas of the previous gates. -/
def toCircuit (g : Gate n) (prev : List (Circuit n)) : Circuit n :=
  match g.kind with
  | .not => not (if h : 0 < g.wires.length then argCirc prev (g.wires.get ⟨0, h⟩) else const false)
  | .and => and fun i => argCirc prev (g.wires.get i)
  | .or => or fun i => argCirc prev (g.wires.get i)
  | .oracle => oracle fun i => argCirc prev (g.wires.get i)

end Gate

lemma getD_append_of_lt {α : Type} {l₁ l₂ : List α} {d : ℕ} (a : α) (h : d < l₁.length) :
    (l₁ ++ l₂).getD d a = l₁.getD d a := List.getD_append _ _ _ _ h

lemma stepLocal_apply (L : Lang) (x : Fin n → Bool) : StepLocal (Gate.apply L x) := by
  intro g l₁ l₂ h
  have ha : ∀ w ∈ g.wires, Gate.argVal x (l₁ ++ l₂) w = Gate.argVal x l₁ w := by
    rintro (i | d) hw
    · rfl
    · exact getD_append_of_lt false (h d hw)
  unfold Gate.apply
  cases g.kind <;> simp only [ha _ (List.get_mem _ _)]

lemma stepLocal_depth : StepLocal (Gate.depthStep (n := n)) := by
  intro g l₁ l₂ h
  unfold Gate.depthStep
  congr 2
  refine List.map_congr_left fun w hw => ?_
  rcases w with i | d
  · rfl
  · exact getD_append_of_lt 0 (h d hw)

lemma stepLocal_circ : StepLocal (Gate.toCircuit (n := n)) := by
  intro g l₁ l₂ h
  have ha : ∀ w ∈ g.wires, Gate.argCirc (l₁ ++ l₂) w = Gate.argCirc l₁ w := by
    rintro (i | d) hw
    · rfl
    · exact getD_append_of_lt _ (h d hw)
  unfold Gate.toCircuit
  cases g.kind <;> simp only [ha _ (List.get_mem _ _)]

/-! ### DAG circuits -/

/-- A DAG circuit: a list of gates, each reading inputs and earlier gates; the last gate is the
output. -/
structure DAG (n : ℕ) where
  gates : List (Gate n)
  isLocal : LocalGates gates

namespace DAG

/-- Evaluate a DAG circuit with oracle gates for `L`. -/
def eval (D : DAG n) (L : Lang) (x : Fin n → Bool) : Bool :=
  (runGates (Gate.apply L x) [] D.gates).getD 0 false

/-- Depth: the longest path from an input to the output gate. -/
def depth (D : DAG n) : ℕ := (runGates Gate.depthStep [] D.gates).getD 0 0

/-- Size: number of gates plus number of wires. -/
def size (D : DAG n) : ℕ := D.gates.length + (D.gates.map fun g => g.wires.length).sum

/-- The formula obtained by unfolding the DAG. -/
def toCircuit (D : DAG n) : Circuit n := (runGates Gate.toCircuit [] D.gates).getD 0 (const false)

end DAG

/-! ### Unfolding a DAG into a formula -/

lemma getD_map_eval {α β : Type} (f : α → β) (l : List α) (d : ℕ) (a : α) :
    (l.map f).getD d (f a) = f (l.getD d a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[d]? <;> rfl

lemma runGates_toCircuit_eval (L : Lang) (x : Fin n → Bool) (gs : List (Gate n))
    (accF : List (Circuit n)) (accV : List Bool) (hacc : accF.map (Circuit.eval L x) = accV) :
    (runGates Gate.toCircuit accF gs).map (Circuit.eval L x) = runGates (Gate.apply L x) accV gs := by
  induction gs generalizing accF accV with
  | nil => exact hacc
  | cons g gs ih =>
    apply ih
    simp only [List.map_cons, ← hacc]
    congr 1
    have harg : ∀ w, (Gate.argCirc accF w).eval L x = Gate.argVal x (accF.map (Circuit.eval L x)) w := by
      rintro (i | d)
      · rfl
      · simp only [Gate.argCirc, Gate.argVal, Sum.elim_inr]
        rw [← getD_map_eval (Circuit.eval L x) accF d (const false), eval_const]
    unfold Gate.toCircuit Gate.apply
    cases g.kind
    · simp only [eval_not]; split <;> simp [harg]
    · simp [allFin, harg]
    · simp [anyFin, harg]
    · simp [harg]

lemma DAG.eval_toCircuit (D : DAG n) (L : Lang) (x : Fin n → Bool) :
    D.toCircuit.eval L x = D.eval L x := by
  have h := runGates_toCircuit_eval L x D.gates [] [] rfl
  rw [DAG.eval, ← h, DAG.toCircuit, ← eval_const L x false, getD_map_eval, eval_const]

lemma le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- Size/depth invariant for the unfolding: the formula of a gate of depth `δ` has size at most
`B ^ (δ + 1)` and depth at most `δ + 1`, where `B = W + 2` and `W` bounds all fan-ins. -/
def UnfoldInv (B : ℕ) (F : List (Circuit n)) (Dp : List ℕ) : Prop :=
  ∀ d, (F.getD d (const false)).size ≤ B ^ (Dp.getD d 0 + 1) ∧
    (F.getD d (const false)).depth ≤ Dp.getD d 0 + 1

lemma unfoldInv_step {W : ℕ} (g : Gate n) (hg : g.wires.length ≤ W) (F : List (Circuit n))
    (Dp : List ℕ) (hinv : UnfoldInv (W + 2) F Dp) :
    UnfoldInv (W + 2) (g.toCircuit F :: F) (g.depthStep Dp :: Dp) := by
  set B := W + 2
  set δ := g.depthStep Dp
  have hB : 2 ≤ B := by omega
  have hδ : 1 ≤ δ := by simp [δ, Gate.depthStep]
  -- every argument has size `≤ B ^ δ` and depth `≤ δ`
  have harg : ∀ w ∈ g.wires, (Gate.argCirc F w).size ≤ B ^ δ ∧ (Gate.argCirc F w).depth ≤ δ := by
    intro w hw
    have hle : Gate.argDepth Dp w + 1 ≤ δ := by
      have := le_foldr_max (List.mem_map_of_mem (f := Gate.argDepth Dp) hw)
      simp only [δ, Gate.depthStep]; omega
    rcases w with i | d
    · simp only [Gate.argCirc, Sum.elim_inl, size, depth]
      exact ⟨Nat.one_le_pow _ _ (by omega), by omega⟩
    · simp only [Gate.argCirc, Sum.elim_inr]
      simp only [Gate.argDepth, Sum.elim_inr] at hle
      obtain ⟨h1, h2⟩ := hinv d
      exact ⟨h1.trans (Nat.pow_le_pow_right (by omega) hle), by omega⟩
  intro d
  rcases d with _ | d
  · simp only [List.getD_cons_zero]
    have hpow : B ^ δ * B = B ^ (δ + 1) := (pow_succ _ _).symm
    have hW : ∀ k, k ≤ W → k * B ^ δ + 1 ≤ B ^ (δ + 1) := by
      intro k hk
      have : 1 ≤ B ^ δ := Nat.one_le_pow _ _ (by omega)
      have h1 : k * B ^ δ ≤ W * B ^ δ := Nat.mul_le_mul_right _ hk
      have h2 : B ^ δ * B = W * B ^ δ + 2 * B ^ δ := by simp only [B]; ring
      rw [← hpow]; omega
    unfold Gate.toCircuit
    cases g.kind
    · have hc : (if h : 0 < g.wires.length then Gate.argCirc F (g.wires.get ⟨0, h⟩)
          else const false).size ≤ B ^ δ ∧ (if h : 0 < g.wires.length then
          Gate.argCirc F (g.wires.get ⟨0, h⟩) else const false).depth ≤ δ := by
        split
        · exact harg _ (List.get_mem _ _)
        · rw [size_const, depth_const_eq]
          exact ⟨Nat.one_le_pow _ _ (by omega), hδ⟩
      simp only [size, depth]
      have : 1 ≤ B ^ δ := Nat.one_le_pow _ _ (by omega)
      exact ⟨by rw [← hpow]; nlinarith [hc.1], by omega⟩
    · exact ⟨(size_and_le _ fun i => (harg _ (List.get_mem _ _)).1).trans (hW _ hg),
        depth_and_le _ fun i => (harg _ (List.get_mem _ _)).2⟩
    · exact ⟨(size_or_le _ fun i => (harg _ (List.get_mem _ _)).1).trans (hW _ hg),
        depth_or_le _ fun i => (harg _ (List.get_mem _ _)).2⟩
    · exact ⟨(size_oracle_le _ fun i => (harg _ (List.get_mem _ _)).1).trans (hW _ hg),
        depth_oracle_le _ fun i => (harg _ (List.get_mem _ _)).2⟩
  · simpa using hinv d

lemma unfoldInv_run {W : ℕ} (gs : List (Gate n)) (hgs : ∀ g ∈ gs, g.wires.length ≤ W)
    (F : List (Circuit n)) (Dp : List ℕ) (hinv : UnfoldInv (W + 2) F Dp) :
    UnfoldInv (W + 2) (runGates Gate.toCircuit F gs) (runGates Gate.depthStep Dp gs) := by
  induction gs generalizing F Dp with
  | nil => exact hinv
  | cons g gs ih =>
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _ _
      (unfoldInv_step g (hgs g (by simp)) F Dp hinv)

lemma DAG.wires_le_size (D : DAG n) : ∀ g ∈ D.gates, g.wires.length ≤ D.size := by
  intro g hg
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun g : Gate n => g.wires.length) hg)
  simp only [DAG.size]; omega

lemma DAG.toCircuit_bounds (D : DAG n) :
    D.toCircuit.size ≤ (D.size + 2) ^ (D.depth + 1) ∧ D.toCircuit.depth ≤ D.depth + 1 := by
  have := unfoldInv_run D.gates D.wires_le_size [] []
    (fun d => by simp [size_const, depth_const_eq]) 0
  exact this

/-! ### Compiling a formula into a DAG -/

lemma LocalGates.snoc {gs : List (Gate n)} {g : Gate n} (h : LocalGates gs)
    (hg : ∀ d, Sum.inr d ∈ g.wires → d < gs.length) : LocalGates (gs ++ [g]) := by
  intro i hi d hd
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hil : i < gs.length
  · rw [List.getElem_append_left hil] at hd; exact h i hil d hd
  · have hi' : i = gs.length := by omega
    subst hi'
    rw [List.getElem_append_right (by omega)] at hd
    simpa using hg d (by simpa using hd)

/-- Wires of the gate placed after the child blocks `bs`: child `i`'s output is the gate
`∑_{i' > i} |bs i'|` positions back. -/
def topWires (bs : List (List (Gate n))) (k : ℕ) : List (Fin n ⊕ ℕ) :=
  List.ofFn fun i : Fin k => Sum.inr ((bs.drop (i + 1)).map List.length).sum

/-- A formula as a list of gates (one gate per node; an input leaf becomes a one-wire `AND`). -/
def compile : Circuit n → List (Gate n)
  | Circuit.input i => [⟨.and, [Sum.inl i]⟩]
  | Circuit.not c => compile c ++ [⟨.not, [Sum.inr 0]⟩]
  | @Circuit.and _ k cs => (List.ofFn fun i => compile (cs i)).flatten ++
      [⟨.and, topWires (List.ofFn fun i => compile (cs i)) k⟩]
  | @Circuit.or _ k cs => (List.ofFn fun i => compile (cs i)).flatten ++
      [⟨.or, topWires (List.ofFn fun i => compile (cs i)) k⟩]
  | @Circuit.oracle _ k cs => (List.ofFn fun i => compile (cs i)).flatten ++
      [⟨.oracle, topWires (List.ofFn fun i => compile (cs i)) k⟩]

lemma compile_ne_nil (c : Circuit n) : compile c ≠ [] := by
  cases c <;> simp [compile]

lemma sum_drop_lt {α : Type} (bs : List (List α)) (hne : ∀ b ∈ bs, b ≠ []) (i : ℕ)
    (hi : i < bs.length) :
    ((bs.drop (i + 1)).map List.length).sum < bs.flatten.length := by
  rw [List.length_flatten]
  conv_rhs => rw [← List.take_append_drop (i + 1) bs]
  rw [List.map_append, List.sum_append]
  have hmem : bs[i] ∈ bs.take (i + 1) := by
    rw [List.mem_iff_getElem]; exact ⟨i, by simp; omega, by simp⟩
  have hpos : 0 < bs[i].length := List.length_pos_iff.2 (hne _ (by simp))
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hmem)
  omega

lemma topWires_lt (bs : List (List (Gate n))) (k : ℕ) (hk : bs.length = k)
    (hne : ∀ b ∈ bs, b ≠ []) : ∀ d, Sum.inr d ∈ topWires bs k → d < bs.flatten.length := by
  intro d hd
  simp only [topWires, List.mem_ofFn, Sum.inr.injEq] at hd
  obtain ⟨i, rfl⟩ := hd
  exact sum_drop_lt bs hne i (by omega)

lemma mem_ofFn_compile {k : ℕ} {cs : Fin k → Circuit n} {b : List (Gate n)}
    (hb : b ∈ List.ofFn fun i => compile (cs i)) : ∃ i, compile (cs i) = b :=
  List.mem_ofFn.1 hb

lemma compile_local (c : Circuit n) : LocalGates (compile c) := by
  induction c with
  | input i =>
    intro j hj d hd
    simp only [compile, List.length_singleton] at hj
    have : j = 0 := by omega
    subst this
    simp [compile] at hd
  | not c ih =>
    simp only [compile]
    apply ih.snoc
    intro d hd
    simp only [List.mem_singleton, Sum.inr.injEq] at hd
    subst hd
    exact List.length_pos_iff.2 (compile_ne_nil c)
  | @and k cs ih | @or k cs ih | @oracle k cs ih =>
    simp only [compile]
    apply (LocalGates.flatten _).snoc
    · exact topWires_lt _ k (by simp) fun b hb => by
        obtain ⟨i, rfl⟩ := mem_ofFn_compile hb; exact compile_ne_nil _
    · intro b hb; obtain ⟨i, rfl⟩ := mem_ofFn_compile hb; exact ih i

/-- Evaluating the gate after the child blocks. -/
lemma run_blocks {α : Type} {step : Gate n → List α → α} (hs : StepLocal step) {k : ℕ}
    (cs : Fin k → Circuit n) (g : Gate n) (a : α) :
    (runGates step [] ((List.ofFn fun i => compile (cs i)).flatten ++ [g])).getD 0 a =
      step g ((List.ofFn fun i => runGates step [] (compile (cs i)))).reverse.flatten := by
  rw [runGates_append, runGates_flatten hs _ fun b hb => by
    obtain ⟨i, rfl⟩ := mem_ofFn_compile hb; exact compile_local _]
  simp [runGates, List.map_ofFn, Function.comp_def]

lemma getD_blocks {α : Type} {step : Gate n → List α → α} {k : ℕ} (cs : Fin k → Circuit n)
    (i : Fin k) (a : α) :
    ((List.ofFn fun i => runGates step [] (compile (cs i)))).reverse.flatten.getD
      (((List.ofFn fun i => compile (cs i)).drop (i + 1)).map List.length).sum a =
    (runGates step [] (compile (cs i))).getD 0 a := by
  have hlen : ((List.ofFn fun i => compile (cs i)).drop (i + 1)).map List.length =
      ((List.ofFn fun i => runGates step [] (compile (cs i))).drop (i + 1)).map List.length := by
    simp only [List.map_drop, List.map_ofFn, Function.comp_def, length_runGates,
      List.length_nil, zero_add]
  rw [hlen, getD_reverse_flatten _ a i (by simp)]
  · simp [List.headD_eq_head?_getD, List.getD_eq_getElem?_getD]
    cases (runGates step [] (compile (cs i))) <;> simp
  · simp only [List.mem_ofFn]
    rintro _ ⟨j, rfl⟩
    rw [← List.length_pos_iff, length_runGates]
    simpa using List.length_pos_iff.2 (compile_ne_nil (cs j))

lemma compile_eval (L : Lang) (x : Fin n → Bool) (c : Circuit n) :
    (runGates (Gate.apply L x) [] (compile c)).getD 0 false = c.eval L x := by
  induction c with
  | input i => simp [compile, runGates, Gate.apply, allFin, Gate.argVal]
  | not c ih =>
    rw [compile, runGates_append, runGates_local (stepLocal_apply L x) (compile_local c)]
    simp [runGates, Gate.apply, Gate.argVal, ← ih]
  | @and k cs ih =>
    rw [compile, run_blocks (stepLocal_apply L x) cs _ false]
    simp only [Gate.apply, topWires]
    rw [ofFn_get_apply allFin (fun i : Fin k => (Sum.inr _ : Fin n ⊕ ℕ))]
    simp only [Gate.argVal, Sum.elim_inr, getD_blocks, ih, allFin, eval_and]
  | @or k cs ih =>
    rw [compile, run_blocks (stepLocal_apply L x) cs _ false]
    simp only [Gate.apply, topWires]
    rw [ofFn_get_apply anyFin (fun i : Fin k => (Sum.inr _ : Fin n ⊕ ℕ))]
    simp only [Gate.argVal, Sum.elim_inr, getD_blocks, ih, anyFin, eval_or]
  | @oracle k cs ih =>
    rw [compile, run_blocks (stepLocal_apply L x) cs _ false]
    simp only [Gate.apply, topWires]
    rw [ofFn_get_apply L (fun i : Fin k => (Sum.inr _ : Fin n ⊕ ℕ))]
    simp only [Gate.argVal, Sum.elim_inr, getD_blocks, ih, eval_oracle]

lemma foldr_max_le {l : List ℕ} {M : ℕ} (h : ∀ a ∈ l, a ≤ M) : l.foldr max 0 ≤ M := by
  induction l with
  | nil => simp
  | cons b l ih => exact max_le (h b (by simp)) (ih fun a ha => h a (by simp [ha]))

lemma compile_depth (c : Circuit n) :
    (runGates Gate.depthStep [] (compile c)).getD 0 0 ≤ c.depth + 1 := by
  induction c with
  | input i => simp [compile, runGates, Gate.depthStep, Gate.argDepth, depth]
  | not c ih =>
    rw [compile, runGates_append, runGates_local stepLocal_depth (compile_local c)]
    simp only [runGates, List.getD_cons_zero, Gate.depthStep, List.map_cons, List.map_nil,
      Gate.argDepth, Sum.elim_inr, List.foldr_cons, List.foldr_nil, depth]
    have : (runGates Gate.depthStep [] (compile c) ++ []).getD 0 0 =
        (runGates Gate.depthStep [] (compile c)).getD 0 0 := by simp
    rw [this]; omega
  | @and k cs ih | @or k cs ih | @oracle k cs ih =>
    rw [compile, run_blocks stepLocal_depth cs _ 0]
    simp only [Gate.depthStep, depth]
    have : ((topWires (List.ofFn fun i => compile (cs i)) k).map (Gate.argDepth
        ((List.ofFn fun i => runGates Gate.depthStep [] (compile (cs i)))).reverse.flatten)).foldr
          max 0 ≤ (Finset.univ.sup fun i => (cs i).depth) + 1 := by
      apply foldr_max_le
      simp only [List.mem_map, topWires, List.mem_ofFn]
      rintro a ⟨w, ⟨i, rfl⟩, rfl⟩
      simp only [Gate.argDepth, Sum.elim_inr, getD_blocks]
      exact (ih i).trans (by have := depth_child_le cs i; omega)
    omega

lemma length_compile (c : Circuit n) : (compile c).length = c.size := by
  induction c with
  | input i => simp [compile, size]
  | not c ih => simp [compile, size, ih]
  | @and k cs ih | @or k cs ih | @oracle k cs ih =>
    simp [compile, size, List.length_flatten, List.map_ofFn, Function.comp_def, ih,
      List.sum_ofFn]

/-- Total number of wires of a list of gates. -/
def wireCount (gs : List (Gate n)) : ℕ := (gs.map fun g => g.wires.length).sum

lemma wireCount_compile (c : Circuit n) : wireCount (compile c) + 1 ≤ 2 * c.size := by
  induction c with
  | input i => simp [compile, size, wireCount]
  | not c ih =>
    simp only [compile, wireCount, List.map_append, List.sum_append] at ih ⊢
    simp [size]; omega
  | @and k cs ih | @or k cs ih | @oracle k cs ih =>
    simp only [compile, wireCount, List.map_append, List.sum_append, List.map_flatten,
      List.sum_flatten, List.map_ofFn, Function.comp_def, List.sum_ofFn, size] at ih ⊢
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, topWires,
      List.length_ofFn, add_zero]
    have h1 : ∑ i, (List.map (fun g => g.wires.length) (compile (cs i))).sum ≤
        ∑ i, (2 * (cs i).size - 1) := Finset.sum_le_sum fun i _ => by have := ih i; omega
    have h2 : ∑ i, (2 * (cs i).size - 1) + k = 2 * ∑ i, (cs i).size := by
      have : ∀ i, 2 * (cs i).size - 1 + 1 = 2 * (cs i).size := fun i => by
        have := size_pos (cs i); omega
      calc ∑ i, (2 * (cs i).size - 1) + k = ∑ i, (2 * (cs i).size - 1 + 1) := by
            rw [Finset.sum_add_distrib]; simp
        _ = 2 * ∑ i, (cs i).size := by rw [Finset.sum_congr rfl fun i _ => this i, Finset.mul_sum]
    omega

/-- The DAG of a formula. -/
def Circuit.toDAG (c : Circuit n) : DAG n := ⟨compile c, compile_local c⟩

lemma Circuit.toDAG_eval (c : Circuit n) (L : Lang) (x : Fin n → Bool) :
    c.toDAG.eval L x = c.eval L x := compile_eval L x c

lemma Circuit.toDAG_depth (c : Circuit n) : c.toDAG.depth ≤ c.depth + 1 := compile_depth c

lemma Circuit.toDAG_size (c : Circuit n) : c.toDAG.size ≤ 3 * c.size := by
  have h1 := length_compile c
  have h2 := wireCount_compile c
  simp only [DAG.size, Circuit.toDAG, wireCount] at h1 h2 ⊢
  omega

/-! ### The two models give the same reducibility -/

/-- `AC⁰` Turing reducibility in the DAG model of the paper: polynomial size (gates and wires)
and constant depth. -/
def DAGReduces (A B : Lang) : Prop :=
  ∃ d c : ℕ, ∀ n, ∃ D : DAG n, D.depth ≤ d ∧ D.size ≤ (n + 2) ^ c ∧ ∀ x, D.eval B x = A n x

theorem dagReduces_iff {A B : Lang} : DAGReduces A B ↔ A ≤ᵀ B := by
  constructor
  · rintro ⟨d, c, h⟩
    refine ⟨d + 1, (c + 2) * (d + 1), fun n => ?_⟩
    obtain ⟨D, hd, hs, he⟩ := h n
    obtain ⟨h1, h2⟩ := D.toCircuit_bounds
    refine ⟨D.toCircuit, h2.trans (by omega), ?_, fun x => by rw [D.eval_toCircuit, he]⟩
    calc D.toCircuit.size ≤ (D.size + 2) ^ (D.depth + 1) := h1
      _ ≤ ((n + 2) ^ (c + 2)) ^ (D.depth + 1) := Nat.pow_le_pow_left (add_two_le_pow hs) _
      _ ≤ ((n + 2) ^ (c + 2)) ^ (d + 1) :=
          Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) (by omega)
      _ = (n + 2) ^ ((c + 2) * (d + 1)) := by rw [← pow_mul]
  · rintro ⟨d, c, h⟩
    refine ⟨d + 1, c + 2, fun n => ?_⟩
    obtain ⟨C, hd, hs, he⟩ := h n
    refine ⟨C.toDAG, C.toDAG_depth.trans (by omega), ?_, fun x => by rw [C.toDAG_eval, he]⟩
    have h4 : 4 ≤ (n + 2) ^ 2 := by rw [sq]; nlinarith
    calc C.toDAG.size ≤ 3 * C.size := C.toDAG_size
      _ ≤ (n + 2) ^ 2 * (n + 2) ^ c := Nat.mul_le_mul (by omega) hs
      _ = (n + 2) ^ (c + 2) := by ring

/-- `AC⁰[L]` in the DAG model. -/
def AC0DAG (L : Lang) : Set Lang := {A | DAGReduces A L}

theorem AC0DAG_eq (L : Lang) : AC0DAG L = AC0 L := by
  ext A; exact dagReduces_iff

end PLB
