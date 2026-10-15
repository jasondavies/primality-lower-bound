import PrimalityLowerBound.Languages
import ACC.Formula.Semantics
import ACC.Functions.Mod

/-!
# Translating PLB circuits to ACC formulas

Translate PLB formulas into the ACC formulas of `formalcs/circuit-complexity`, preserving
semantics and node count and bounding depth. The quantitative Smolensky
proof uses this translation to apply the upstream formula approximation machinery.
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

end PLB
