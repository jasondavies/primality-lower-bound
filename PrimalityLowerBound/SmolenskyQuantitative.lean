import PrimalityLowerBound.Smolensky
import PrimalityLowerBound.Asymptotics
import ACC.LowerBounds.Smolensky.Restriction

/-!
# Quantitative Smolensky lower bounds

The upstream simulation has explicit bounds even for an individual formula. We use a
separate size budget, so the approximation degree is polynomial in the logarithm of that
budget, without assuming that the formula belongs to a polynomial-size family.

The approximation and residue-counting arguments adapt the Apache-2.0 sources recorded in
`vendor/circuit-complexity/UPSTREAM.md`.
-/

namespace PLB
namespace SmolenskyQuantitative

open Circuits.ACC

/-- Degree coefficient for the pointwise approximation. -/
def degreeCoefficient (p d : ℕ) : ℕ := (p - 1) * simulationOrderCoefficient p 1 1 d 1

/-- An individual formula of size at most `B` has a polynomial approximation of degree
`O((log B)^(8d+1))`, erring on at most a `1/n` fraction of its `n`-bit inputs. -/
theorem approximate {p n B d : ℕ} (hp : p.Prime) (hn : 0 < n) (hnB : n ≤ B)
    (C : ACCFormula p) (hCs : C.nodeCount ≤ B) (hCd : C.depth ≤ d) :
    ∃ q : MultilinearPolynomial p n,
      MultilinearPolynomial.DegreeAtMost q
        (degreeCoefficient p d * logInputSize B ^ simulationOrderExponent d) ∧
      ((Finset.univ.filter fun x : Fin n → Bool =>
        MultilinearPolynomial.eval q x ≠ ((C.eval (List.ofFn x)).toNat : ZMod p)).card) * n
          ≤ 2 ^ n := by
  classical
  let I := probabilisticAndModIntermediate C B 1
  have hi := probabilisticAndModIntermediate_bounds C B 1 1 d 1 (by omega)
    (by omega) (by simpa using hCs) hCd
  have hI : I.HasOnlyAndModGates :=
    ACCFormula.probabilisticOrElimination_hasOnlyAndModGates _ _ _
      (ACCFormula.eliminateAndNotGates_hasOnlyOrAndModGates C)
  have hnorm := normalizeAndMod_resource_bounds hp.two_le I B
    (simulationIntermediateNodeCoefficient 1 1 d 1)
    (simulationPreprocessedDepth d + 1)
    (simulationIntermediateOrderCoefficient 1 1 1)
    (4 * simulationPreprocessedDepth d) (by omega) hI hi.1 hi.2.1 hi.2.2.1
  let P := probabilisticModPAndSimulationCircuit C B 1
  let R := probabilisticModPAndSimulationRandomBitCount C B 1
  have horder : P.val.IsOfOrder
      (simulationOrderCoefficient p 1 1 d 1 * logInputSize B ^ simulationOrderExponent d) := by
    simpa [P, probabilisticModPAndSimulationCircuit, probabilisticModPAndSimulationFormula,
      I, simulationOrderCoefficient, simulationOrderExponent] using hnorm.2
  have herr : ∀ x : Fin n → Bool,
      ProbabilisticACCFormula.errorProbability P.val R (List.ofFn x)
        (C.eval (List.ofFn x)) ≤ 1 / (n : ℚ) ^ 1 := by
    intro x
    have he := ACCFormula.probabilisticOrElimination_errorProbability_le hp.one_lt
      (ACCFormula.eliminateAndNotGates C) B 1 (List.ofFn x) (by omega)
      (ACCFormula.eliminateAndNotGates_hasOnlyOrAndModGates C)
    rw [ACCFormula.eliminateAndNotGates_eval hp.one_lt] at he
    have hnrm := ProbabilisticACCFormula.normalizeAndMod_errorProbability_eq hp I R
      (List.ofFn x) (C.eval (List.ofFn x)) hI
    have he' : ProbabilisticACCFormula.errorProbability P.val R (List.ofFn x)
        (C.eval (List.ofFn x)) ≤ 1 / (B : ℚ) ^ 1 := hnrm.trans_le he
    refine he'.trans ?_
    simp only [pow_one]
    exact one_div_le_one_div_of_le (by exact_mod_cast hn) (by exact_mod_cast hnB)
  obtain ⟨seed, hseed⟩ := exists_seed_with_few_disagreements P.val R 1
    (fun x : Fin n → Bool => C.eval (List.ofFn x)) hn herr
  let D : ModPAndCircuit p :=
    ⟨specializeProbabilisticModPAndFormula P.val (List.ofFn seed),
      specializeProbabilisticModPAndFormula_isModPAndCircuit _ _ P.property⟩
  have hD := specializeProbabilisticModPAndFormula_isOfOrder P.val (List.ofFn seed)
    _ P.property horder
  obtain ⟨q, hq, hqe⟩ := ModPAndCircuit.exists_multilinear_polynomial (n := n) hp D hD
  refine ⟨q, by simpa [degreeCoefficient, Nat.mul_assoc] using hq, ?_⟩
  have heq : (Finset.univ.filter fun x : Fin n → Bool =>
      MultilinearPolynomial.eval q x ≠ ((C.eval (List.ofFn x)).toNat : ZMod p)).card =
        fixedSeedDisagreementCount P.val R (fun x : Fin n → Bool => C.eval (List.ofFn x)) seed := by
    unfold fixedSeedDisagreementCount
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hqe]
    have hd := specializeProbabilisticModPAndFormula_eval P.val (List.ofFn seed)
      (List.ofFn x) P.property
    change ((D.val.eval (List.ofFn x)).toNat : ZMod p) ≠ _ ↔ _
    rw [show D.val.eval (List.ofFn x) = P.val.eval (List.ofFn x) (List.ofFn seed) from hd]
    let _ : Fact p.Prime := ⟨hp⟩
    cases P.val.eval (List.ofFn x) (List.ofFn seed) <;>
      cases C.eval (List.ofFn x) <;> simp
  rw [heq]
  simpa using hseed

/-- Low-degree polynomials cannot approximate a modulo function this accurately. -/
theorem obstruction (p r : ℕ) (hp : p.Prime) (hr : 1 < r) (hcop : r.Coprime p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ q : MultilinearPolynomial p (n + r), ∀ k : ℕ,
      q.DegreeAtMost k → (k : ℝ) ≤ Real.sqrt n →
      ((Finset.univ.filter fun x : Fin (n + r) → Bool =>
        q.eval x ≠ ((modFunction r x).toNat : ZMod p)).card) * (n + r) ≤ 2 ^ (n + r) →
      False := by
  classical
  obtain ⟨e, he, ω, hω_ne, hω_pow⟩ :=
    exists_nontrivial_rootOfUnity_galoisField p r hp (by omega) hcop
  obtain ⟨lowerThreshold, hlower⟩ :=
    PolynomialModLowerBound.lowDegree_polynomials_disagree_with_mod
      p r e hp (by omega) hcop he ω hω_ne hω_pow
  refine ⟨lowerThreshold + 20 * r * 2 ^ r + 20, ?_⟩
  intro n hn q k hqdegree hk herror
  let K := @GaloisField p ⟨hp⟩ e
  let F : Fin r → MvPolynomial (Fin n) K := fun i =>
    SmolenskyBridge.restrictedPolynomial p n r (K := K) i q
  have hF : ∀ i, PolynomialModLowerBound.IsMultilinear (F i) ∧
      ((F i).totalDegree : ℝ) ≤ Real.sqrt n := by
    intro i
    refine ⟨SmolenskyBridge.restrictedPolynomial_multilinear p n r i q, ?_⟩
    have ht := SmolenskyBridge.restrictedPolynomial_totalDegree_le (K := K)
      p n r k i q hqdegree
    exact (show ((F i).totalDegree : ℝ) ≤ k by exact_mod_cast ht).trans hk
  have hlowerBound := hlower n (by omega) F hF
  let agreement : Finset (Fin (n + r) → Bool) := Finset.univ.filter fun x =>
    q.eval x = ((modFunction r x).toNat : ZMod p)
  let errors := agreementᶜ
  have herrset : errors = Finset.univ.filter (fun x : Fin (n + r) → Bool =>
      q.eval x ≠ ((modFunction r x).toNat : ZMod p)) := by
    ext x; simp [errors, agreement]
  rw [← herrset] at herror
  let residueErrors (i : Fin r) : Finset (Fin n → Bool) :=
    Finset.univ.filter fun x ↦
      PolynomialModLowerBound.evalBool (F i) x ≠
        PolynomialModLowerBound.modIndicator i x
  have hresidue_card (i : Fin r) :
      (residueErrors i).card ≤ errors.card := by
    apply Finset.card_le_card_of_injOn
      (SmolenskyBridge.residueExtension n r i)
    · intro x hx
      have hxerr : PolynomialModLowerBound.evalBool (F i) x ≠
          PolynomialModLowerBound.modIndicator i x := by
        simpa [residueErrors] using (Finset.mem_filter.mp hx).2
      have hext : SmolenskyBridge.residueExtension n r i x ∉ agreement := by
        intro hagree
        have hagreeEval : q.eval (SmolenskyBridge.residueExtension n r i x) =
            ((modFunction r (SmolenskyBridge.residueExtension n r i x)).toNat : ZMod p) :=
          (Finset.mem_filter.mp hagree).2
        apply hxerr
        dsimp [F]
        rw [SmolenskyBridge.restrictedPolynomial_eval, hagreeEval]
        unfold modFunction PolynomialModLowerBound.modIndicator
        rw [SmolenskyBridge.residueExtension_weight]
        have hiff := SmolenskyBridge.residueExtension_mod_iff r
          (by omega) i (∑ j, (x j).toNat)
        by_cases hmod : (∑ j, (x j).toNat) % r = i.val
        · have hextmod :
              ((∑ j, (x j).toNat) + (r - i.val)) % r = 0 := hiff.mpr hmod
          simp [hmod, hextmod]
        · have hextmod :
              ((∑ j, (x j).toNat) + (r - i.val)) % r ≠ 0 := by
            exact fun h ↦ hmod (hiff.mp h)
          simp [hmod, hextmod]
      change SmolenskyBridge.residueExtension n r i x ∈ agreementᶜ
      exact Finset.mem_compl.mpr hext
    · intro x hx y hy hxy
      funext j
      have hj := congrFun hxy (Fin.castAdd r j)
      simpa using hj
  have hdisagreement :
      PolynomialModLowerBound.disagreementInputs F =
        (Finset.univ : Finset (Fin r)).biUnion residueErrors := by
    ext x
    simp [PolynomialModLowerBound.disagreementInputs, residueErrors]
  have hdisagreement_card :
      (PolynomialModLowerBound.disagreementInputs F).card ≤
        r * errors.card := by
    rw [hdisagreement]
    refine Finset.card_biUnion_le.trans ?_
    calc
      ∑ i : Fin r, (residueErrors i).card ≤
          ∑ _i : Fin r, errors.card :=
        Finset.sum_le_sum fun i _ ↦ hresidue_card i
      _ = r * errors.card := by simp
  have hthreshold : 20 * r * 2 ^ r ≤ n + r := by
    omega
  have hscaled : (20 * r * errors.card) * 2 ^ r ≤
      (2 ^ n) * 2 ^ r := by
    calc
      (20 * r * errors.card) * 2 ^ r =
          errors.card * (20 * r * 2 ^ r) := by ring
      _ ≤ errors.card * (n + r) := Nat.mul_le_mul_left _ hthreshold
      _ ≤ 2 ^ (n + r) := herror
      _ = (2 ^ n) * 2 ^ r := by rw [pow_add]
  have htwenty_errors : 20 * r * errors.card ≤ 2 ^ n := by
    exact Nat.le_of_mul_le_mul_right hscaled (by positivity)
  have htwenty_disagreement :
      20 * (PolynomialModLowerBound.disagreementInputs F).card ≤ 2 ^ n := by
    calc
      20 * (PolynomialModLowerBound.disagreementInputs F).card ≤
          20 * (r * errors.card) := Nat.mul_le_mul_left _ hdisagreement_card
      _ = 20 * r * errors.card := by ring
      _ ≤ 2 ^ n := htwenty_errors
  have hpow_large : 20 ≤ 2 ^ n := by
    have hfive : 5 ≤ n := by
      omega
    calc
      20 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ n := by
        gcongr
  have hupper : (PolynomialModLowerBound.disagreementInputs F).card <
      2 ^ n / 10 := by
    let u := (PolynomialModLowerBound.disagreementInputs F).card
    have huplus : (u + 1) * 10 ≤ 2 ^ n := by
      by_cases hu : u = 0
      · rw [hu]
        norm_num
        exact (by omega : 10 ≤ 20).trans hpow_large
      · calc
          (u + 1) * 10 ≤ 20 * u := by omega
          _ ≤ 2 ^ n := by simpa [u] using htwenty_disagreement
    have : u + 1 ≤ 2 ^ n / 10 :=
      (Nat.le_div_iff_mul_le (by omega)).2 huplus
    omega
  exact (not_lt_of_ge hlowerBound) hupper

private lemma degree_square_bound (K e r t : ℕ) (ht : K ^ 2 + r ≤ t) :
    (K * (t + 1) ^ e) ^ 2 + r ≤ (t + 2) ^ (2 * e + 2) := by
  have hA : 1 ≤ (t + 2) ^ (2 * e) := Nat.one_le_pow _ _ (by omega)
  have hpow : (K * (t + 1) ^ e) ^ 2 ≤ K ^ 2 * (t + 2) ^ (2 * e) := by
    calc
      _ = K ^ 2 * (t + 1) ^ (2 * e) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  calc
    _ ≤ (K ^ 2 + r) * (t + 2) ^ (2 * e) := by nlinarith
    _ ≤ (t + 2) ^ 2 * (t + 2) ^ (2 * e) := by gcongr; nlinarith
    _ = _ := by ring

/-- On a suitable polynomial sequence of input lengths, depth-`d` formulas require
at least `2^t` nodes. All constants are uniform over formulas. -/
theorem power_lower_bound (p r d : ℕ) (hp : p.Prime) (hr : 1 < r)
    (hcop : r.Coprime p) :
    ∃ c : ℕ, 1 ≤ c ∧ ∃ t₀ : ℕ, ∀ t ≥ t₀,
      ∀ C : Circuit ((t + 2) ^ c), C.depth ≤ d →
        (∀ x, C.eval (ModLang p) x = ModLang r _ x) → 2 ^ t ≤ C.size := by
  obtain ⟨n₀, hn₀⟩ := obstruction p r hp hr hcop
  let K := degreeCoefficient p d
  let e := simulationOrderExponent d
  let c := 2 * e + 2
  have hevent : ∀ᶠ t : ℕ in Filter.atTop, (t + 2) ^ c ≤ 2 ^ t := by
    filter_upwards [eventually_pow_add_le_exp c 2 (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)] with t ht
    simp only [Real.rpow_one, one_mul, Real.rpow_natCast] at ht
    exact_mod_cast ht
  obtain ⟨t₁, ht₁⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨c, by omega, max t₁ (n₀ + r + K ^ 2 + r + 1), ?_⟩
  intro t ht C hCd hCe
  by_contra hsmall
  have hCs : C.size ≤ 2 ^ t := by omega
  have hM : (t + 2) ^ c ≤ 2 ^ t := ht₁ t (by omega)
  have hct : t + 2 ≤ (t + 2) ^ c := by
    calc t + 2 = (t + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  let M := (t + 2) ^ c
  let n := M - r
  have hnr : n + r = M := by omega
  have hn : n₀ ≤ n := by omega
  let F := C.toACC p
  obtain ⟨q, hq, herr⟩ := approximate hp (n := n + r) (B := 2 ^ t)
    (by omega) (by omega) F
    (by simpa [F, Circuit.nodeCount_toACC] using hCs)
    ((Circuit.depth_toACC C).trans hCd)
  have hlog : logInputSize (2 ^ t) ≤ t + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := t)
    omega
  have hdeg : degreeCoefficient p d * logInputSize (2 ^ t) ^ simulationOrderExponent d
      ≤ K * (t + 1) ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlog _)
  have hsquare := degree_square_bound K e r t (by omega)
  change (K * (t + 1) ^ e) ^ 2 + r ≤ M at hsquare
  have hsqrt : ((K * (t + 1) ^ e : ℕ) : ℝ) ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (show (K * (t + 1) ^ e) ^ 2 ≤ n by omega)
  apply hn₀ n hn q (K * (t + 1) ^ e)
  · intro term hterm
    exact (hq term hterm).trans hdeg
  · exact hsqrt
  · convert herr using 2
    congr 1
    ext x
    have heval : F.eval (List.ofFn x) = modFunction r x := by
      have he : ∀ x : Fin M → Bool, F.eval (List.ofFn x) = modFunction r x := by
        intro x
        rw [show F = C.toACC p from rfl, Circuit.eval_toACC, hCe]
        simp [ModLang, modFunction, ones_eq_fin_sum, Nat.dvd_iff_mod_eq_zero]
        rfl
      exact (congrArg (fun m => ∀ x : Fin m → Bool,
        F.eval (List.ofFn x) = modFunction r x) hnr).mpr he x
    simp [heval]

end SmolenskyQuantitative
end PLB
