import PrimalityLowerBound.Languages
import PrimalityLowerBound.DAG
import ACC.LowerBounds.Smolensky.Formula

/-!
# Smolensky's theorem in the PLB circuit model

Translate PLB formulas into the ACC formulas of `formalcs/circuit-complexity`, preserving
semantics and node count and bounding depth and input indices. The upstream qualitative
lower bound proves that `Mod_q` is outside AC⁰[Mod_p] for distinct primes `p` and `q`.
See `vendor/circuit-complexity/UPSTREAM.md` for provenance.
-/

namespace PLB

open Circuits.ACC

namespace Circuit

variable {n p : ℕ}

/-- Interpret every oracle gate as a modulo-`p` gate in the upstream formula model. -/
def toACC (p : ℕ) : Circuit n → ACCFormula p
  | input i => .input i false
  | not c => .notGate (c.toACC p)
  | gate .and cs => .andGate (List.ofFn fun i => (cs i).toACC p)
  | gate .or cs => .orGate (List.ofFn fun i => (cs i).toACC p)
  | gate .oracle cs => .modGate (List.ofFn fun i => (cs i).toACC p)

lemma eval_toACC (c : Circuit n) (x : Fin n → Bool) :
    (c.toACC p).eval (List.ofFn x) = c.eval (ModLang p) x := by
  induction c with
  | input i => simp [toACC, ACCFormula.eval, eval]
  | not c ih => simp [toACC, ACCFormula.eval, eval, ih]
  | gate op cs ih =>
    cases op with
    | and => simp [toACC, ACCFormula.eval, eval, Op.apply, List.all_eq_true, ih]
    | or => simp [toACC, ACCFormula.eval, eval, Op.apply, List.any_eq_true, ih]
    | oracle =>
      simp [toACC, ACCFormula.eval, eval, Op.apply, List.map_ofFn, List.sum_ofFn, ih,
        ModLang, ones_eq_fin_sum, Nat.dvd_iff_mod_eq_zero]

lemma nodeCount_toACC (c : Circuit n) : (c.toACC p).nodeCount = c.size := by
  induction c with
  | input i => simp [toACC, ACCFormula.nodeCount, size]
  | not c ih => simp [toACC, ACCFormula.nodeCount, size, ih]
  | gate op cs ih =>
    cases op <;> simp [toACC, ACCFormula.nodeCount, size, List.map_ofFn, List.sum_ofFn, ih, Nat.add_comm]

private lemma gate_numInputs_le (fs : List (ACCFormula p)) (h : ∀ f ∈ fs, f.numInputs ≤ n) :
    (ACCFormula.andGate fs).numInputs ≤ n ∧ (ACCFormula.orGate fs).numInputs ≤ n ∧
      (ACCFormula.modGate fs).numInputs ≤ n := by
  induction fs with
  | nil => simp [ACCFormula.numInputs]
  | cons f fs ih =>
    have hf := h f (by simp)
    obtain ⟨ha, ho, hm⟩ := ih (fun g hg => h g (by simp [hg]))
    simpa only [ACCFormula.numInputs, max_le_iff] using ⟨⟨hf, ha⟩, ⟨hf, ho⟩, ⟨hf, hm⟩⟩

lemma numInputs_toACC (c : Circuit n) : (c.toACC p).numInputs ≤ n := by
  induction c with
  | input i => simp [toACC, ACCFormula.numInputs]
  | not c ih => simpa [toACC, ACCFormula.numInputs] using ih
  | gate op cs ih =>
    have h : ∀ f ∈ List.ofFn (fun i => (cs i).toACC p), f.numInputs ≤ n := by
      simpa using ih
    have hg := gate_numInputs_le _ h
    cases op
    · exact hg.1
    · exact hg.2.1
    · exact hg.2.2

private lemma list_max_le (l : List ℕ) (d : ℕ) (h : ∀ a ∈ l, a ≤ d) :
    l.max?.getD 0 ≤ d := by
  cases he : l.max? with
  | none => simp
  | some a => exact h a (List.max?_mem he)

lemma depth_toACC (c : Circuit n) : (c.toACC p).depth ≤ c.depth := by
  induction c with
  | input i => simp [toACC, ACCFormula.depth, depth]
  | not c ih => simpa [toACC, ACCFormula.depth, depth] using Nat.add_le_add_right ih 1
  | gate op cs ih =>
    have h := list_max_le ((List.ofFn fun i => (cs i).toACC p).map ACCFormula.depth)
      (Finset.univ.sup fun i => (cs i).depth) (by
        intro a ha
        simp only [List.mem_map, List.mem_ofFn] at ha
        obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := ha
        exact (ih i).trans (depth_child_le cs i))
    cases op <;> simp only [toACC, ACCFormula.depth, depth] <;> omega

end Circuit

/-- Qualitative Smolensky separation, stated in the PLB DAG model. -/
def SmolenskyTheorem : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ModLang q ∉ AC0DAG (ModLang p)

/-- Smolensky's theorem, discharged by the upstream formula lower bound. -/
theorem smolenskyTheorem : SmolenskyTheorem := by
  intro p q hp hq hpq hmem
  rw [AC0DAG_eq] at hmem
  obtain ⟨d, c, h⟩ := hmem
  choose C hCd hCs hCe using h
  let family : ACCFormula.ACCFormulaFamily p (3 ^ c) c (d + 1) := fun n =>
    ⟨(C n).toACC p, hp.one_lt, Circuit.numInputs_toACC _,
      (Circuit.depth_toACC _).trans (by have := hCd n; omega), by
        rw [Circuit.nodeCount_toACC]
        calc (C n).size ≤ (n.val + 2) ^ c := hCs n
          _ ≤ (3 * n.val) ^ c := Nat.pow_le_pow_left (by have := n.pos; omega) c
          _ = 3 ^ c * n.val ^ c := Nat.mul_pow _ _ _, by omega⟩
  apply smolensky_mod_lower_bound p q hp hq.one_lt
    ((Nat.coprime_primes hq hp).2 (Ne.symm hpq)) (3 ^ c) c (d + 1) family
  intro n x
  change ((C n).toACC p).eval (List.ofFn x) = modFunction q x
  rw [Circuit.eval_toACC, hCe]
  simp [ModLang, modFunction, ones_eq_fin_sum, Nat.dvd_iff_mod_eq_zero]

end PLB
