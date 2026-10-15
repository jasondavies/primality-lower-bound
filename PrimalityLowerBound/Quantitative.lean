import PrimalityLowerBound.DAG
import PrimalityLowerBound.Lemma4
import PrimalityLowerBound.GCD
import PrimalityLowerBound.SquareFree
import PrimalityLowerBound.Primes
import PrimalityLowerBound.SmolenskyQuantitative

/-!
# Smolensky lower bounds and quantitative Corollary 2

The explicit formula approximation bounds give `smolenskyExpTheorem`, the quantitative
Smolensky theorem, and its qualitative consequence `smolenskyTheorem`. Transferring the
formula bound along reductions gives size `2^(N^δ)` for some `δ > 0` for bounded-depth
circuits with `Mod_p` gates for `Primes`, `GCD` or `Square-Free` (at valid input lengths).

The argument: a circuit for the language on `N` input bits also decides it on fewer bits (by
padding), so composing the reduction `Mod_q ≤ᵀ mult ≤ᵀ A` with it yields a circuit for `Mod_q`
on about `N^{1/c}` bits whose size is polynomial in the size of the given circuit.
-/

namespace PLB

open Circuit

/-! ### Padding -/

/-- `A` on length `k` is a projection (rewiring with constants `false`) of `A` on length `N`. -/
def Projects (A : Lang) (k N : ℕ) : Prop :=
  ∃ π : Fin N → Option (Fin k), ∀ x : Fin k → Bool, A N (fun i => (π i).elim false x) = A k x

/-- Zero-extension of a bit string. -/
def zeroPad (k N : ℕ) : Fin N → Option (Fin k) := fun i => idx k i

lemma ones_zeroPad {k N : ℕ} (hkN : k ≤ N) (x : Fin k → Bool) :
    ones (fun i => (zeroPad k N i).elim false x) = ones x := by
  rw [ones_eq_sum, ones_eq_sum]
  calc
    _ = ∑ i ∈ Finset.range N, (getD x i).toNat := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [getD_of_lt _ (Finset.mem_range.mp hi)]
      simp [zeroPad]
    _ = ∑ i ∈ Finset.range k, (getD x i).toNat := by
      symm
      apply Finset.sum_subset (Finset.range_mono hkN)
      intro i _ hi
      simp only [Finset.mem_range, not_lt] at hi
      simp [getD_of_ge x hi]

lemma modLang_projects (r : ℕ) {k N : ℕ} (hkN : k ≤ N) : Projects (ModLang r) k N :=
  ⟨zeroPad k N, fun x => by simp only [ModLang, ones_zeroPad hkN]⟩

lemma val_zeroPad {k N : ℕ} (hkN : k ≤ N) (x : Fin k → Bool) :
    val (fun i => (zeroPad k N i).elim false x) = val x := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [val, testBit_bitsVal]
  by_cases hi : i < k
  · rw [getD_of_lt _ (by omega : i < N)]
    simp [zeroPad, hi, show i < N by omega]
  · by_cases hiN : i < N
    · rw [getD_of_lt _ hiN]; simp [zeroPad, hi, hiN, getD_of_ge x (by omega : k ≤ i)]
    · simp [hi, hiN]

lemma primes_projects {k N : ℕ} (hkN : k ≤ N) : Projects Primes k N :=
  ⟨zeroPad k N, fun x => by simp only [Primes, val_zeroPad hkN]⟩

lemma squarefree_projects {k N : ℕ} (hkN : k ≤ N) : Projects SquareFree k N :=
  ⟨zeroPad k N, fun x => by simp only [SquareFree, val_zeroPad hkN]⟩

/-- Rewiring a `GCD` input of length `3a` into length `3b` (each third zero-extended). -/
def gcdPad (a b : ℕ) : Fin (3 * b) → Option (Fin (3 * a)) := fun i =>
  if h : (i : ℕ) % b < a then
    some ⟨(i : ℕ) / b * a + (i : ℕ) % b, by
      have h1 : (i : ℕ) / b < 3 := Nat.div_lt_of_lt_mul (by have := i.2; linarith)
      have : (i : ℕ) / b * a + a ≤ 3 * a := by nlinarith
      omega⟩
  else none

lemma valFrom_gcdPad {a b : ℕ} (hab : a ≤ b) (x : Fin (3 * a) → Bool) (t : ℕ) (ht : t < 3) :
    valFrom (fun i => (gcdPad a b i).elim false x) (t * b) b = valFrom x (t * a) a := by
  apply Nat.eq_of_testBit_eq
  intro s
  simp only [valFrom, testBit_bitsVal]
  by_cases hs : s < a
  · have hlt : t * b + s < 3 * b := by nlinarith
    rw [getD_of_lt _ hlt, getD_of_lt _ (by nlinarith)]
    have hmod : (t * b + s) % b = s := by
      rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    have hdiv : (t * b + s) / b = t := by
      rw [Nat.mul_comm t b, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]; simp
    simp [gcdPad, hmod, hdiv, hs, show s < b by omega]
  · by_cases hsb : s < b
    · have hlt : t * b + s < 3 * b := by nlinarith
      rw [getD_of_lt _ hlt]
      have hmod : (t * b + s) % b = s := by
        rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hsb
      simp [gcdPad, hmod, hs, hsb]
    · simp [hs, hsb]

lemma gcd_projects {a b : ℕ} (hab : a ≤ b) : Projects GCD (3 * a) (3 * b) := by
  refine ⟨gcdPad a b, fun x => ?_⟩
  simp only [GCD, Nat.mul_mod_right, show 3 * b / 3 = b by omega, show 3 * a / 3 = a by omega]
  have h0 := valFrom_gcdPad hab x 0 (by norm_num)
  have h1 := valFrom_gcdPad hab x 1 (by norm_num)
  have h2 := valFrom_gcdPad hab x 2 (by norm_num)
  simp only [zero_mul, one_mul] at h0 h1 h2
  rw [h0, h1, h2]

/-! ### Transfer of circuits along a reduction -/

/-- Compose a reduction `B ≤ᵀ A` (depth `dR`, size `(n+2)^cR`) with a single circuit `C` for `A`
on length `N` (with `L'`-oracle gates).  Valid when every fan-in `k ≤ (n+2)^cR ≤ N` is a
projection of `N` or `A k` is constant. -/
lemma transfer {A B L' : Lang} {dR cR N n : ℕ} (R : Circuit n) (hRd : R.depth ≤ dR)
    (hRs : R.size ≤ (n + 2) ^ cR) (hRe : ∀ x, R.eval A x = B n x)
    (hproj : ∀ k ≤ N, Projects A k N ∨ ∃ b, ∀ x, A k x = b)
    (C : Circuit N) (hC : ∀ x, C.eval L' x = A N x) (hn : (n + 2) ^ cR ≤ N) :
    ∃ C' : Circuit n, C'.depth ≤ dR * (C.depth + 2) ∧ C'.size ≤ (n + 2) ^ cR * C.size ^ dR ∧
      ∀ x, C'.eval L' x = B n x := by
  classical
  let E : (k : ℕ) → Circuit k := fun k =>
    if h : Projects A k N then C.subst fun i => wire (Classical.choose h i)
    else if h' : ∃ b, ∀ x, A k x = b then const (Classical.choose h') else const false
  have hEs : ∀ k, (E k).size ≤ C.size := by
    intro k
    simp only [E]
    split
    · exact (size_subst_le _ (fun i => (size_wire _).le) le_rfl C).trans (by simp)
    · split <;> (rw [size_const]; exact size_pos C)
  have hEd : ∀ k, (E k).depth ≤ C.depth + 1 := by
    intro k
    simp only [E]
    split
    · exact depth_subst_le _ (fun i => depth_wire_le _) C
    · split <;> exact (depth_const _).trans (by omega)
  have hEe : ∀ k ≤ R.size, ∀ y, (E k).eval L' y = A k y := by
    intro k hk y
    have hkN : k ≤ N := by omega
    simp only [E]
    split
    · next h =>
      rw [eval_subst]
      simp only [eval_wire]
      rw [hC]; exact Classical.choose_spec h y
    · next h =>
      have h' : ∃ b, ∀ x, A k x = b := (hproj k hkN).resolve_left h
      rw [dite_eq_left h', eval_const]; exact (Classical.choose_spec h' y).symm
  refine ⟨R.compose E, ?_, ?_, fun x => by rw [eval_compose_of_le A L' E x R hEe, hRe]⟩
  · exact (depth_compose_le E hEd R).trans (Nat.mul_le_mul hRd (by omega))
  · calc (R.compose E).size ≤ R.size * C.size ^ R.depth :=
          size_compose_le E (size_pos C) R fun k _ => hEs k
      _ ≤ (n + 2) ^ cR * C.size ^ dR :=
          Nat.mul_le_mul hRs (Nat.pow_le_pow_right (size_pos C) hRd)

/-! ### Asymptotics -/

/-- Interpolate bounds on polynomially spaced lengths, absorbing a polynomial factor. -/
lemma asymptotic_core_mul (c a E n₀ : ℕ) (hc : 1 ≤ c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : ℕ,
      (∀ n ≥ n₀, (n + 2) ^ c ≤ N → (2 : ℝ) ^ ((n : ℝ) ^ δ) ≤ ((n + 2) ^ a : ℕ) * (S + 2) ^ E) →
      (2 : ℝ) ^ ((N : ℝ) ^ δ') ≤ S := by
  set δ₁ := min δ 1
  have hδ₁ : 0 < δ₁ := lt_min hδ one_pos
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  set γ := δ₁ / c
  have hγ : 0 < γ := div_pos hδ₁ hcr
  set E' := E + 1
  refine ⟨γ / 2, by positivity, ?_⟩
  have hA := (tendsto_rpow_atTop (inv_pos.2 hcr)).eventually_ge_atTop ((n₀ : ℝ) + 6)
  have hC := (tendsto_rpow_atTop (half_pos hγ)).eventually_ge_atTop (4 * (E' : ℝ) + 1)
  have hpoly := eventually_pow_le_exp a hγ (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((tendsto_natCast_atTop_atTop.eventually (hA.and hC)).and hpoly)
  refine ⟨max N₀ 1, fun N hN S hS => ?_⟩
  obtain ⟨⟨hrN, htN⟩, hpolyN⟩ := hN₀ N (le_of_max_le_left hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  set r := (N : ℝ) ^ ((c : ℝ)⁻¹) with hr
  set t := (N : ℝ) ^ (γ / 2) with ht
  -- the auxiliary input length `n = ⌊r⌋ - 2`
  set m := ⌊r⌋₊
  have hm : (n₀ + 6 : ℕ) ≤ m := Nat.le_floor (by push_cast; linarith)
  have hmr : (m : ℝ) ≤ r := Nat.floor_le (by positivity)
  have hrm : r < m + 1 := Nat.lt_floor_add_one r
  set n := m - 2
  have hnm : n + 2 = m := by omega
  have hmc : (m : ℝ) ^ c ≤ N := by
    calc (m : ℝ) ^ c ≤ r ^ c := pow_le_pow_left₀ (by positivity) hmr c
      _ = N := Real.rpow_inv_natCast_pow hN0 (by omega)
  have hmcN : (n + 2) ^ c ≤ N := by
    rw [hnm]; exact_mod_cast hmc
  have key := hS n (by omega) hmcN
  rw [hnm] at key
  push_cast at key
  -- lower bound on `n ^ δ`
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hnr : r / 2 ≤ n := by
    have : (n : ℝ) = m - 2 := by
      rw [show (m : ℝ) = (n + 2 : ℕ) by rw [hnm]]; push_cast; ring
    rw [this]; linarith
  have hnδ : (N : ℝ) ^ γ / 2 ≤ (n : ℝ) ^ δ := by
    have h1 : (n : ℝ) ^ δ₁ ≤ (n : ℝ) ^ δ :=
      Real.rpow_le_rpow_of_exponent_le hn1 (min_le_left _ _)
    have h2 : (r / 2) ^ δ₁ ≤ (n : ℝ) ^ δ₁ :=
      Real.rpow_le_rpow (by positivity) hnr hδ₁.le
    have h3 : (r / 2) ^ δ₁ = (N : ℝ) ^ γ / 2 ^ δ₁ := by
      rw [Real.div_rpow (by positivity) (by norm_num), hr, ← Real.rpow_mul hN0]
      congr 2; simp only [γ]; field_simp
    have h4 : (2 : ℝ) ^ δ₁ ≤ 2 := by
      calc (2 : ℝ) ^ δ₁ ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (min_le_right _ _)
        _ = 2 := Real.rpow_one 2
    have h5 : (N : ℝ) ^ γ / 2 ≤ (N : ℝ) ^ γ / 2 ^ δ₁ :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) h4
    linarith
  -- `(S + 2) ^ E' ≥ 2 ^ (N^γ / 4)`
  have hS2 : (1 : ℝ) ≤ (S : ℝ) + 2 := by
    have : (0 : ℝ) ≤ S := by positivity
    linarith
  have hpowE : ((S : ℝ) + 2) ^ E ≤ ((S : ℝ) + 2) ^ E' := pow_le_pow_right₀ hS2 (by omega)
  have hbig : (2 : ℝ) ^ ((1 / 4 : ℝ) * (N : ℝ) ^ γ) ≤ ((S : ℝ) + 2) ^ E' := by
    have e1 : (2 : ℝ) ^ ((N : ℝ) ^ γ / 2) =
        (2 : ℝ) ^ ((1 / 4 : ℝ) * (N : ℝ) ^ γ) * (2 : ℝ) ^ ((1 / 4 : ℝ) * (N : ℝ) ^ γ) := by
      rw [← Real.rpow_add (by norm_num)]; ring_nf
    have e2 : (2 : ℝ) ^ ((N : ℝ) ^ γ / 2) ≤ (2 : ℝ) ^ ((n : ℝ) ^ δ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hnδ
    have hmN : (m : ℝ) ≤ N := by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      calc (m : ℝ) = (m : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (m : ℝ) ^ c := pow_le_pow_right₀ hm1 hc
        _ ≤ N := hmc
    have e3 : (m : ℝ) ^ a * ((S : ℝ) + 2) ^ E ≤
        (2 : ℝ) ^ ((1 / 4 : ℝ) * (N : ℝ) ^ γ) * ((S : ℝ) + 2) ^ E' := by
      exact mul_le_mul ((pow_le_pow_left₀ (by positivity) hmN a).trans hpolyN)
        hpowE (by positivity) (by positivity)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((1 / 4 : ℝ) * (N : ℝ) ^ γ) := by positivity
    have := e2.trans (key.trans e3)
    rw [e1] at this
    exact le_of_mul_le_mul_left this hpos
  -- `S + 2 ≥ 2 ^ (N^γ / (4 E'))`
  have hE'pos : (0 : ℝ) < E' := by positivity
  have hroot : (2 : ℝ) ^ ((1 / 4 : ℝ) * (N : ℝ) ^ γ / E') ≤ (S : ℝ) + 2 := by
    by_contra hlt
    push Not at hlt
    have : ((S : ℝ) + 2) ^ E' < ((2 : ℝ) ^ ((1 / 4 : ℝ) * (N : ℝ) ^ γ / E')) ^ E' :=
      pow_lt_pow_left₀ hlt (by positivity) (by omega)
    have e : ((2 : ℝ) ^ ((1 / 4 : ℝ) * (N : ℝ) ^ γ / E')) ^ E' = (2 : ℝ) ^ ((1 / 4 : ℝ) * (N : ℝ) ^ γ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hE'pos.ne']
    rw [e] at this
    linarith
  -- `N^γ / (4 E') ≥ t + 1`
  have htt : (N : ℝ) ^ γ = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; congr 1; push_cast; ring
  have ht1 : t + 1 ≤ (1 / 4 : ℝ) * (N : ℝ) ^ γ / E' := by
    rw [htt, le_div_iff₀ (by positivity)]
    nlinarith
  have hfin : (2 : ℝ) ^ (t + 1) ≤ (S : ℝ) + 2 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) ht1).trans hroot
  rw [Real.rpow_add (by norm_num), Real.rpow_one] at hfin
  have h2t : (2 : ℝ) ≤ (2 : ℝ) ^ t := by
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ 2 ^ t := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  show (2 : ℝ) ^ t ≤ S
  linarith

/-- Interpolate bounds on polynomially spaced lengths without a polynomial factor. -/
lemma asymptotic_core (c E n₀ : ℕ) (hc : 1 ≤ c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : ℕ,
      (∀ n ≥ n₀, (n + 2) ^ c ≤ N →
        (2 : ℝ) ^ ((n : ℝ) ^ δ) ≤ (S + 2) ^ E) →
      (2 : ℝ) ^ ((N : ℝ) ^ δ') ≤ S := by
  simpa using asymptotic_core_mul c 0 E n₀ hc hδ

/-- Extend the sequence bound to all large lengths, allowing a polynomial size bound
in an auxiliary parameter `S`. This applies directly to formulas and to unfolded DAGs. -/
theorem smolensky_formula_exp_bound (p q d E : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ C : Circuit N,
      C.depth ≤ d → (∀ x, C.eval (ModLang p) x = ModLang q N x) →
      ∀ S : ℕ, C.size ≤ (S + 2) ^ E → (2 : ℝ) ^ ((N : ℝ) ^ δ) ≤ S := by
  obtain ⟨c, hc, t₀, hlow⟩ := SmolenskyQuantitative.power_lower_bound p q (d + 1)
    hp hq.one_lt ((Nat.coprime_primes hq hp).2 (Ne.symm hpq))
  obtain ⟨δ, hδ, N₀, hN₀⟩ := asymptotic_core c E t₀ hc (δ := 1) (by norm_num)
  refine ⟨δ, hδ, N₀, fun N hN C hCd hCe S hCs => hN₀ N hN S ?_⟩
  intro t ht htN
  obtain ⟨π, hπ⟩ := modLang_projects q htN
  let C' := C.subst fun i => wire (π i)
  have hC'd : C'.depth ≤ d + 1 :=
    (depth_subst_le _ (fun _ => depth_wire_le _) C).trans (by omega)
  have hC's : C'.size ≤ C.size := by
    simpa [C'] using size_subst_le (fun i => wire (π i))
      (fun _ => (size_wire _).le) (by omega : 1 ≤ 1) C
  have hC'e : ∀ x, C'.eval (ModLang p) x = ModLang q ((t + 2) ^ c) x := by
    intro x
    simpa only [C', eval_subst, eval_wire, hCe] using hπ x
  have hsize := (hlow t ht C' hC'd hC'e).trans (hC's.trans hCs)
  simpa only [Real.rpow_one, Real.rpow_natCast] using
    (show (2 : ℝ) ^ t ≤ ((S : ℝ) + 2) ^ E by exact_mod_cast hsize)

/-! ### The quantitative corollary -/

/-- Quantitative Smolensky for DAG circuits: at every fixed depth, circuits with `Mod_p`
gates computing `Mod_q` for distinct primes require size at least `2^(n^δ)` for some
`δ > 0` and all sufficiently large input lengths. -/
theorem smolenskyExpTheorem :
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ∀ d : ℕ,
      ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ D : DAG n, D.depth ≤ d → (∀ x, D.eval (ModLang p) x = ModLang q n x) →
          (2 : ℝ) ^ ((n : ℝ) ^ δ) ≤ D.size := by
  intro p q hp hq hpq d
  obtain ⟨δ, hδ, N₀, hN₀⟩ := smolensky_formula_exp_bound p q (d + 1) (d + 1) hp hq hpq
  refine ⟨δ, hδ, N₀, fun N hN D hDd hDe => ?_⟩
  apply hN₀ N hN D.toCircuit (D.toCircuit_bounds.2.trans (by omega))
    (fun x => by rw [DAG.eval_toCircuit, hDe]) D.size
  exact D.toCircuit_bounds.1.trans (Nat.pow_le_pow_right (by omega) (by omega))

/-- Exponential lower bounds on arbitrarily large valid lengths exclude polynomial-size,
bounded-depth DAG families. -/
theorem not_mem_ac0DAG_of_exp_lower_bound {A L : Lang} (V : ℕ → Prop)
    (hV : ∀ n, ∃ N ≥ n, V N)
    (hbound : ∀ d : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, V N →
      ∀ D : DAG N, D.depth ≤ d → (∀ x, D.eval L x = A N x) →
        (2 : ℝ) ^ ((N : ℝ) ^ δ) ≤ D.size) : A ∉ AC0DAG L := by
  rintro ⟨d, c, h⟩
  obtain ⟨δ, hδ, n₀, hlow⟩ := hbound d
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    (eventually_pow_add_le_exp c 2 hδ (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨n, hn, hvalid⟩ := hV (max (max n₀ n₁) 1)
  obtain ⟨D, hDd, hDs, hDe⟩ := h n
  have hlower := hlow n (by omega) hvalid D hDd hDe
  have hupper : (D.size : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ) ^ δ) :=
    (show (D.size : ℝ) ≤ ((n : ℝ) + 2) ^ c by exact_mod_cast hDs).trans
      (hn₁ n (by omega))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hstrict : (2 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ) ^ δ) <
      (2 : ℝ) ^ ((n : ℝ) ^ δ) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    nlinarith [Real.rpow_pos_of_pos hnpos δ]
  exact (not_lt_of_ge hlower) (hupper.trans_lt hstrict)

/-- Qualitative Smolensky follows because the quantitative lower bound eventually
exceeds every polynomial size bound. -/
theorem smolenskyTheorem (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ModLang q ∉ AC0DAG (ModLang p) := by
  apply not_mem_ac0DAG_of_exp_lower_bound (fun _ => True) (fun n => ⟨n, le_rfl, trivial⟩)
  simpa using smolenskyExpTheorem p q hp hq hpq

/-- If `mult ≤ᵀ A` and `A` on shorter (valid) lengths is a projection of `A` on longer valid
lengths, then bounded-depth `Mod_p` circuits for `A` need size `2^(N^δ)`. -/
theorem exp_lower_bound_of_reduces {A : Lang} (V : ℕ → Prop)
    (hproj : ∀ N, V N → ∀ k ≤ N, Projects A k N ∨ ∃ b, ∀ x, A k x = b)
    (hA : mult ≤ᵀ A) {p : ℕ} (hp : p.Prime) (d : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, V N → ∀ D : DAG N, D.depth ≤ d →
      (∀ x, D.eval (ModLang p) x = A N x) → (2 : ℝ) ^ ((N : ℝ) ^ δ) ≤ D.size := by
  obtain ⟨q, hq, hqp, hqm⟩ := exists_modLang_reduces_mult p
  obtain ⟨dR, cR₀, hR⟩ := hqm.trans hA
  choose R hRd hRs hRe using hR
  set cR := cR₀ + 1
  have hRs' : ∀ n, (R n).size ≤ (n + 2) ^ cR := fun n =>
    (hRs n).trans (Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨δ₀, hδ₀, n₀, hsm⟩ := smolensky_formula_exp_bound p q (dR * (d + 3)) 1 hp hq (Ne.symm hqp)
  set E := (d + 1) * dR
  obtain ⟨δ', hδ', N₀, hN₀⟩ := asymptotic_core_mul cR cR E n₀ (by omega) hδ₀
  refine ⟨δ', hδ', N₀, fun N hN hV D hDd hDe => hN₀ N hN D.size fun n hn hnN => ?_⟩
  obtain ⟨hFs, hFd⟩ := D.toCircuit_bounds
  have hFe : ∀ x, D.toCircuit.eval (ModLang p) x = A N x := fun x => by
    rw [D.eval_toCircuit, hDe]
  obtain ⟨C', hC'd, hC's, hC'e⟩ :=
    transfer (R n) (hRd n) (hRs' n) (hRe n) (hproj N hV) D.toCircuit hFe hnN
  have hdepth : C'.depth ≤ dR * (d + 3) :=
    hC'd.trans (Nat.mul_le_mul_left _ (by omega))
  have hformula := hsm n hn C' hdepth hC'e C'.size (by simp)
  have hsize : C'.size ≤ (n + 2) ^ cR * (D.size + 2) ^ E := by
    calc C'.size ≤ (n + 2) ^ cR * D.toCircuit.size ^ dR := hC's
      _ ≤ (n + 2) ^ cR * ((D.size + 2) ^ (D.depth + 1)) ^ dR := by gcongr
      _ ≤ (n + 2) ^ cR * ((D.size + 2) ^ (d + 1)) ^ dR := by gcongr
      _ = (n + 2) ^ cR * (D.size + 2) ^ E := by rw [← pow_mul]
  exact hformula.trans (by exact_mod_cast hsize)

/-- **Corollary 2** (Primes, quantitative): for
every prime `p` and depth `d`, depth-`d` circuits with `Mod_p` gates for `Primes` on `N` bits
have size `≥ 2^(N^δ)` for some `δ > 0` and all large `N`. -/
theorem primes_exp_lower_bound {p : ℕ}
    (hp : p.Prime) (d : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D : DAG N, D.depth ≤ d →
      (∀ x, D.eval (ModLang p) x = Primes N x) → (2 : ℝ) ^ ((N : ℝ) ^ δ) ≤ D.size := by
  obtain ⟨δ, hδ, N₀, h⟩ := exp_lower_bound_of_reduces (fun _ => True)
    (fun _ _ k hk => Or.inl (primes_projects hk)) mult_reduces_primes hp d
  exact ⟨δ, hδ, N₀, fun N hN => h N hN trivial⟩

/-- **Corollary 2** (Square-Free, quantitative). -/
theorem squarefree_exp_lower_bound {p : ℕ} (hp : p.Prime) (d : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D : DAG N, D.depth ≤ d →
      (∀ x, D.eval (ModLang p) x = SquareFree N x) → (2 : ℝ) ^ ((N : ℝ) ^ δ) ≤ D.size := by
  obtain ⟨δ, hδ, N₀, h⟩ := exp_lower_bound_of_reduces (fun _ => True)
    (fun _ _ k hk => Or.inl (squarefree_projects hk)) mult_reduces_squarefree hp d
  exact ⟨δ, hδ, N₀, fun N hN => h N hN trivial⟩

/-- **Corollary 2** (GCD, quantitative). Only input lengths
divisible by `3` encode triples; on other lengths `GCD` is constant by definition. -/
theorem gcd_exp_lower_bound {p : ℕ} (hp : p.Prime) (d : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 3 ∣ N → ∀ D : DAG N, D.depth ≤ d →
      (∀ x, D.eval (ModLang p) x = GCD N x) → (2 : ℝ) ^ ((N : ℝ) ^ δ) ≤ D.size := by
  refine exp_lower_bound_of_reduces (fun N => 3 ∣ N) ?_ mult_reduces_gcd hp d
  rintro N ⟨b, rfl⟩ k hk
  by_cases h3 : 3 ∣ k
  · obtain ⟨a, rfl⟩ := h3
    exact Or.inl (gcd_projects (by omega))
  · right
    refine ⟨false, fun x => ?_⟩
    simp [GCD, Nat.dvd_iff_mod_eq_zero.not.1 h3]

end PLB
