import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Valuation.ValuationSubring
import Surreal.HahnSeries.ScaleIdeal
import Surreal.HahnSeries.BranchMetric

/-!
# The exact bounded-orbit locus of an expanding polynomial map

This file formalizes `epd:thm:bounded` (with `epd:eq:bounded-formula` and its consequences
(a)–(c)), the escape step `epd:eq:escape-step`, the outside recurrence
`epd:eq:outside-recurrence`, the coarsening subsection `epd:subsec:coarsened` and
`epd:cor:coarsebounded` of `docs/surcomplex/expanding-polynomial-dynamics/article.tex`.
Order units are `Surreal.ScaleIdeal.IsOrderUnit` (`epd:def:orderunit`: `u > 0` and every
`γ ≤ n u` for some `n`).

Generic part: `Γ` is any linearly ordered abelian group (neither `Γ ≠ 0` nor divisibility is
used), `K` any field and `v : AddValuation K (WithTop Γ)` any valuation, so `v(0) = ⊤`.
* `integralLocus v f` is `B_int(f) = {x : v(fⁿ(x)) ≥ 0 for all n}`, `boundedLocus v f` is
  `B_val(f) = {x : ∃ β ∈ Γ, v(fⁿ(x)) ≥ β for all n}`, and `exteriorDepth v x` is
  `α(x) = max(0, -v(x))` with `α(0) = 0`.
* `expandingMap q P` is `F = q⁻¹ P`, and `IsExpanding v q P κ` records the hypotheses of
  `epd:eq:polynomial` that the proof uses: `v(q) = κ > 0`, `v(a_j) ≥ 0` for all coefficients,
  `v(lc P) = 0` and `d = natDegree P ≥ 2`. The simple-reduction hypothesis (distinct `c_i`) is
  not used, as the source's proof shows.
* `escape_step` is `epd:eq:escape-step`: `v(x) = a < 0` gives `v(F(x)) = d a - κ < a < 0`;
  `map_iterate_lt_zero`, `strictAnti_map_iterate` and `iterate_add_ne_of_neg` are the following
  sentence (such a point never returns to `O`, its valuations decrease strictly, and it is not
  preperiodic: `F^{m+p}(x) ≠ F^m(x)` for `p ≥ 1`, which is the last clause of
  `epd:thm:periodic`, no preperiodic points outside `O`); `neg_le_map_expandingMap` is
  `v(F(z)) ≥ -κ` for integral `z`.
* `map_iterate_of_neg` is `epd:eq:outside-recurrence`: from `v(y) = -a < 0`,
  `v(Fⁿ(y)) = -(dⁿ a + (1 + d + ⋯ + d^{n-1}) κ)`. `escapeValue_le` is the source's upper bound
  `dⁿ (a + κ)`; for the lower bound `nsmul_le_escapeValue` uses `n (a + κ)` (from `dⁿ ≥ n` and
  `1 + ⋯ + d^{n-1} ≥ n`), which suffices and replaces the source's `d^{n-1} (a + κ)`.
  `bounded_iff_of_neg` is the resulting criterion: the orbit is valuation-bounded iff `a + κ`
  is not an order unit; `isOrderUnit_add_iff` is the step `κ < a + κ ≤ 2κ`.
* `boundedLocus_eq` is `epd:eq:bounded-formula`,
  `B_val(F) = B_int(F) ∪ {x : κ + α(x) is not an order unit}`. Its consequences are
  `boundedLocus_eq_integralLocus` (a), `boundedLocus_eq_of_not_isOrderUnit`,
  `boundedLocus_eq_boundedLocus` (independence of the map, even of `q` with the same `κ`) and
  `setOf_nonneg_subset_boundedLocus` (`O ⊆ B_val(F)`) for (b), and `boundedLocus_eq_univ` (c).
* `coarseSubgroup hu` is `H = {γ : n |γ| < u for all integers n ≥ 1}` of
  `epd:subsec:coarsened` (for any `u > 0`). `ordConnected_coarseSubgroup` (convexity),
  `coarseSubgroup_ne_top` (properness), `le_coarseSubgroup` and `isGreatest_coarseSubgroup`
  (for an order unit `u`, `H` is the maximal proper convex subgroup), `eq_top_of_isOrderUnit_mem`
  (a convex subgroup containing an order unit is `Γ`) and `mem_coarseSubgroup_iff` (a positive
  `γ` lies in `H` iff it is not an order unit) are its claims; no divisibility is used.
* `coarsenedValuationSubring v H` is the valuation ring of the valuation coarsened by a subgroup
  `H`, the Mathlib `ValuationSubring` of all `x` with `v(x) ≥ h` for some `h ∈ H`;
  `mem_coarsenedValuationSubring_iff_add` restates membership as `v(x) + h ≥ 0` for some
  `h ∈ H`, which is `v(x) + H ≥ 0` in `Γ/H`, and `coarsenedValuation_le_iff` shows that its
  valuation compares values of `v` modulo `H`. Mathlib has no ordered quotient of an ordered
  group by a convex subgroup, so no quotient group is constructed.
* `boundedLocus_eq_coarsenedValuationSubring` is `epd:cor:coarsebounded`, and
  `coarsened_integral` its last sentence: relative to the coarsening, `q ≠ 0` and `q, q⁻¹` are
  integral, `P` and `C q⁻¹ * P` (whose evaluation is `F`, `expandingMap_eq_eval`) have integral
  coefficients, and the leading coefficient of `C q⁻¹ * P` is nonzero and integral with integral
  inverse. By `isUnit_mk_of_inv_mem`, a nonzero `x` with `x, x⁻¹ ∈ R` is a unit of `R`, so `q`
  and that leading coefficient are units of the coarsened valuation ring `R`.

Hahn part: `k` is any field (the source takes `ℝ` or `ℂ`), `K = k⟦Γ⟧` with `v = orderTop`
(`HahnSeries.addVal`), `O = nonnegativeSubring Γ k`, and `F` is
`Surreal.BranchMetric.forwardMap P q = q⁻¹ P` (`forwardMap_eq`). `mem_integralLocus_hahn`
restates `B_int(F)` as `{x : Fⁿ(x) ∈ O for all n}`. `isExpanding_hahn` checks `IsExpanding` for
`P ∈ O[X]` of degree at least two with unit leading coefficient, and
`isExpanding_perturbedPolynomial` for the family `epd:eq:polynomial`,
`P = a ∏ (X - c_i) + ∑_{j ≤ d} e_j X^j` with `a ≠ 0`, `e_j ∈ 𝔪`, `d ≥ 2`, and `v(q) = κ > 0`
(that is, `q ∈ 𝔪 \ {0}`). `bounded` is `epd:thm:bounded` for this family (the formula and
(a)–(c), with `O ⊆ B_val(F)`), `boundedLocus_perturbed_eq` is the independence clause of (b),
and `coarsebounded` is `epd:cor:coarsebounded`.

No hypothesis beyond the source's is added; `d ≥ 2` is used (the formula fails for `d = 1`).
The placement note of `epd:subsec:coarsened` relating `H` to `ent:lem:coarsening` of another
report is not formalized. No clause of `epd:thm:bounded`, `epd:eq:escape-step`,
`epd:subsec:coarsened` or `epd:cor:coarsebounded` is pending.
-/

namespace Surreal.ValuedIteration

open Polynomial
open Surreal.ScaleIdeal (IsOrderUnit not_isOrderUnit_iff)

section Group

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Every element above an order unit is an order unit. -/
theorem isOrderUnit_of_le {u w : Γ} (hu : IsOrderUnit u) (h : u ≤ w) : IsOrderUnit w :=
  ⟨hu.1.trans_le h, fun γ => by
    obtain ⟨n, hn⟩ := hu.2 γ
    exact ⟨n, hn.trans (nsmul_le_nsmul_right h n)⟩⟩

omit [IsOrderedAddMonoid Γ] in
/-- If a multiple of a positive `u` is an order unit, so is `u`. -/
theorem isOrderUnit_of_nsmul {u : Γ} (hu : 0 < u) {m : ℕ} (h : IsOrderUnit (m • u)) :
    IsOrderUnit u :=
  ⟨hu, fun γ => by
    obtain ⟨n, hn⟩ := h.2 γ
    exact ⟨n * m, by rwa [← smul_smul]⟩⟩

/-- For `0 ≤ a ≤ κ`, the element `a + κ` (which lies between `κ` and `2κ`) is an order unit
exactly when `κ` is. -/
theorem isOrderUnit_add_iff {a κ : Γ} (ha : 0 ≤ a) (haκ : a ≤ κ) (hκ : 0 < κ) :
    IsOrderUnit (a + κ) ↔ IsOrderUnit κ :=
  ⟨fun h => isOrderUnit_of_nsmul hκ (m := 2)
      (isOrderUnit_of_le h (by rw [two_nsmul]; exact add_le_add haκ le_rfl)),
    fun h => isOrderUnit_of_le h (le_add_of_nonneg_left ha)⟩

/-- Multiples of a negative element decrease strictly. -/
theorem nsmul_lt_nsmul_of_neg_of_lt {a : Γ} (ha : a < 0) {i d : ℕ} (h : i < d) :
    d • a < i • a := by
  have := nsmul_lt_nsmul_left (neg_pos.mpr ha) h
  rwa [smul_neg, smul_neg, neg_lt_neg_iff] at this

/-- Multiples of a nonpositive element decrease. -/
theorem nsmul_le_nsmul_of_nonpos_of_le {a : Γ} (ha : a ≤ 0) {i d : ℕ} (h : i ≤ d) :
    d • a ≤ i • a := by
  have := nsmul_le_nsmul_left (neg_nonneg.mpr ha) h
  rwa [smul_neg, smul_neg, neg_le_neg_iff] at this

/-- `1 + d + ⋯ + d^{n-1} ≤ dⁿ` for `d ≥ 2`. -/
theorem sum_range_pow_le_pow {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∑ i ∈ Finset.range n, d ^ i ≤ d ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc ∑ i ∈ Finset.range n, d ^ i + d ^ n ≤ d ^ n + d ^ n := Nat.add_le_add_right ih _
      _ = d ^ n * 2 := by ring
      _ ≤ d ^ n * d := Nat.mul_le_mul_left _ hd

/-- `n ≤ 1 + d + ⋯ + d^{n-1}` for `d ≥ 1`. -/
theorem le_sum_range_pow {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : n ≤ ∑ i ∈ Finset.range n, d ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := Nat.one_le_pow n d hd
    omega

/-- The lower bound of the proof of `epd:thm:bounded`:
`n (a + κ) ≤ dⁿ a + (1 + d + ⋯ + d^{n-1}) κ` for `d ≥ 2` and `a, κ ≥ 0`. -/
theorem nsmul_le_escapeValue {d : ℕ} (hd : 2 ≤ d) {a κ : Γ} (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (n : ℕ) : n • (a + κ) ≤ d ^ n • a + (∑ i ∈ Finset.range n, d ^ i) • κ := by
  rw [smul_add]
  exact add_le_add (nsmul_le_nsmul_left ha (Nat.lt_pow_self (by omega)).le)
    (nsmul_le_nsmul_left hκ (le_sum_range_pow (by omega) n))

/-- The upper bound of the proof of `epd:thm:bounded`:
`dⁿ a + (1 + d + ⋯ + d^{n-1}) κ ≤ dⁿ (a + κ)` for `d ≥ 2` and `κ ≥ 0`. -/
theorem escapeValue_le {d : ℕ} (hd : 2 ≤ d) (a : Γ) {κ : Γ} (hκ : 0 ≤ κ) (n : ℕ) :
    d ^ n • a + (∑ i ∈ Finset.range n, d ^ i) • κ ≤ d ^ n • (a + κ) := by
  rw [smul_add]
  exact add_le_add le_rfl (nsmul_le_nsmul_left hκ (sum_range_pow_le_pow hd n))

/-! ### The maximal proper convex subgroup -/

/-- `epd:subsec:coarsened`: for `u > 0`, `H = {γ : n |γ| < u for every integer n ≥ 1}`. -/
def coarseSubgroup {u : Γ} (hu : 0 < u) : AddSubgroup Γ where
  carrier := {γ | ∀ n : ℕ, 0 < n → n • |γ| < u}
  zero_mem' := fun n _ => by simpa using hu
  add_mem' := by
    intro γ δ hγ hδ n hn
    have h2n : 0 < 2 * n := by omega
    have key : n • |γ + δ| ≤ (2 * n) • max |γ| |δ| :=
      calc n • |γ + δ| ≤ n • (|γ| + |δ|) := nsmul_le_nsmul_right (abs_add_le γ δ) n
        _ ≤ n • (max |γ| |δ| + max |γ| |δ|) :=
            nsmul_le_nsmul_right (add_le_add (le_max_left _ _) (le_max_right _ _)) n
        _ = (2 * n) • max |γ| |δ| := by rw [← two_nsmul, smul_smul, mul_comm]
    rcases max_choice |γ| |δ| with h | h <;> rw [h] at key
    · exact key.trans_lt (hγ _ h2n)
    · exact key.trans_lt (hδ _ h2n)
  neg_mem' := by
    intro γ hγ n hn
    rw [abs_neg]
    exact hγ n hn

theorem mem_coarseSubgroup {u : Γ} (hu : 0 < u) {γ : Γ} :
    γ ∈ coarseSubgroup hu ↔ ∀ n : ℕ, 0 < n → n • |γ| < u :=
  Iff.rfl

/-- `epd:subsec:coarsened`: `H` is convex. -/
theorem ordConnected_coarseSubgroup {u : Γ} (hu : 0 < u) :
    (coarseSubgroup hu : Set Γ).OrdConnected := by
  refine ⟨fun a ha b hb x hx => (mem_coarseSubgroup hu).mpr fun n hn => ?_⟩
  have hle : |x| ≤ max |a| |b| := abs_le_max_abs_abs hx.1 hx.2
  rcases max_choice |a| |b| with h | h <;> rw [h] at hle
  · exact (nsmul_le_nsmul_right hle n).trans_lt ((mem_coarseSubgroup hu).mp ha n hn)
  · exact (nsmul_le_nsmul_right hle n).trans_lt ((mem_coarseSubgroup hu).mp hb n hn)

/-- `u ∉ H`. -/
theorem notMem_coarseSubgroup {u : Γ} (hu : 0 < u) : u ∉ coarseSubgroup hu := fun h => by
  have h1 := (mem_coarseSubgroup hu).mp h 1 one_pos
  rw [one_nsmul, abs_of_pos hu] at h1
  exact lt_irrefl u h1

/-- `epd:subsec:coarsened`: `H` is a proper subgroup. -/
theorem coarseSubgroup_ne_top {u : Γ} (hu : 0 < u) : coarseSubgroup hu ≠ ⊤ := fun h =>
  notMem_coarseSubgroup hu (by rw [h]; exact AddSubgroup.mem_top u)

omit [IsOrderedAddMonoid Γ] in
theorem abs_mem_addSubgroup {G : AddSubgroup Γ} {γ : Γ} (h : γ ∈ G) : |γ| ∈ G := by
  rcases abs_choice γ with h' | h' <;> rw [h']
  · exact h
  · exact neg_mem h

/-- `epd:subsec:coarsened`: a convex subgroup containing an order unit is all of `Γ`. -/
theorem eq_top_of_isOrderUnit_mem {G : AddSubgroup Γ} (hG : (G : Set Γ).OrdConnected) {u : Γ}
    (hu : IsOrderUnit u) (huG : u ∈ G) : G = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  intro γ
  obtain ⟨n, hn⟩ := hu.2 |γ|
  have h1 : n • u ∈ G := nsmul_mem huG n
  exact hG.out (neg_mem h1) h1 ⟨(abs_le.mp hn).1, (abs_le.mp hn).2⟩

/-- `epd:subsec:coarsened` (maximality): every proper convex subgroup lies in `H`. -/
theorem le_coarseSubgroup {u : Γ} (hu : IsOrderUnit u) {G : AddSubgroup Γ}
    (hG : (G : Set Γ).OrdConnected) (hne : G ≠ ⊤) : G ≤ coarseSubgroup hu.1 := by
  intro γ hγ
  refine (mem_coarseSubgroup hu.1).mpr fun n _ => ?_
  by_contra hlt
  rw [not_lt] at hlt
  have h1 : n • |γ| ∈ G := nsmul_mem (abs_mem_addSubgroup hγ) n
  exact hne (eq_top_of_isOrderUnit_mem hG hu (hG.out G.zero_mem h1 ⟨hu.1.le, hlt⟩))

/-- `epd:subsec:coarsened`: `H` is the maximal proper convex subgroup of `Γ`. -/
theorem isGreatest_coarseSubgroup {u : Γ} (hu : IsOrderUnit u) :
    IsGreatest {G : AddSubgroup Γ | (G : Set Γ).OrdConnected ∧ G ≠ ⊤} (coarseSubgroup hu.1) :=
  ⟨⟨ordConnected_coarseSubgroup hu.1, coarseSubgroup_ne_top hu.1⟩,
    fun _ hG => le_coarseSubgroup hu hG.1 hG.2⟩

/-- `epd:subsec:coarsened`: a positive `γ` lies in `H` exactly when it is not an order unit.
No divisibility is used. -/
theorem mem_coarseSubgroup_iff {u : Γ} (hu : IsOrderUnit u) {γ : Γ} (hγ : 0 < γ) :
    γ ∈ coarseSubgroup hu.1 ↔ ¬ IsOrderUnit γ := by
  rw [mem_coarseSubgroup, abs_of_pos hγ]
  constructor
  · intro h hγu
    obtain ⟨N, hN⟩ := hγu.2 u
    rcases Nat.eq_zero_or_pos N with rfl | hN0
    · rw [zero_nsmul] at hN
      exact absurd hu.1 (not_lt.mpr hN)
    · exact absurd hN (not_le.mpr (h N hN0))
  · intro h n _
    obtain ⟨η, hη⟩ := (not_isOrderUnit_iff hγ).mp h
    obtain ⟨N, hN⟩ := hu.2 η
    rcases Nat.eq_zero_or_pos N with rfl | _
    · have h0 := hη 0
      rw [zero_nsmul] at h0 hN
      exact absurd (h0.trans_le hN) (lt_irrefl 0)
    · refine lt_of_nsmul_lt_nsmul_right N ?_
      calc N • n • γ = (N * n) • γ := smul_smul N n γ
        _ < η := hη _
        _ ≤ N • u := hN

end Group

section Generic

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable {K : Type*} [Field K] (v : AddValuation K (WithTop Γ))

/-! ### Orbit loci and the exterior depth -/

/-- The integral nonescape locus `B_int(f) = {x : v(fⁿ(x)) ≥ 0 for all n}`. -/
def integralLocus (f : K → K) : Set K :=
  {x | ∀ n : ℕ, 0 ≤ v (f^[n] x)}

/-- The valuation-bounded locus `B_val(f) = {x : ∃ β ∈ Γ, v(fⁿ(x)) ≥ β for all n}`. -/
def boundedLocus (f : K → K) : Set K :=
  {x | ∃ β : Γ, ∀ n : ℕ, (β : WithTop Γ) ≤ v (f^[n] x)}

theorem mem_integralLocus {f : K → K} {x : K} :
    x ∈ integralLocus v f ↔ ∀ n : ℕ, 0 ≤ v (f^[n] x) :=
  Iff.rfl

theorem mem_boundedLocus {f : K → K} {x : K} :
    x ∈ boundedLocus v f ↔ ∃ β : Γ, ∀ n : ℕ, (β : WithTop Γ) ≤ v (f^[n] x) :=
  Iff.rfl

/-- `B_int(f) ⊆ B_val(f)`. -/
theorem integralLocus_subset_boundedLocus (f : K → K) :
    integralLocus v f ⊆ boundedLocus v f :=
  fun _ hx => ⟨0, fun n => by simpa using hx n⟩

/-- The exterior depth `α(x) = max(0, -v(x))` for `x ≠ 0`, and `α(0) = 0`. -/
def exteriorDepth (x : K) : Γ :=
  max 0 (-(v x).untopD 0)

theorem exteriorDepth_nonneg (x : K) : 0 ≤ exteriorDepth v x :=
  le_max_left _ _

theorem exteriorDepth_of_eq {x : K} {g : Γ} (h : v x = g) :
    exteriorDepth v x = max 0 (-g) := by
  rw [exteriorDepth, h, WithTop.untopD_coe]

theorem exteriorDepth_zero : exteriorDepth v 0 = 0 := by
  simp [exteriorDepth]

/-- `α(x) = 0` on the integral disk. -/
theorem exteriorDepth_of_nonneg {x : K} (h : 0 ≤ v x) : exteriorDepth v x = 0 := by
  by_cases hx : x = 0
  · rw [hx, exteriorDepth_zero]
  · obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hx)
    rw [exteriorDepth_of_eq v hg.symm]
    rw [← hg] at h
    exact max_eq_left (neg_nonpos.mpr (by exact_mod_cast h))

/-! ### The expanding map and the escape step -/

/-- The expanding map `F = q⁻¹ P`. -/
def expandingMap (q : K) (P : K[X]) (x : K) : K :=
  q⁻¹ * P.eval x

/-- `F = q⁻¹ P` is evaluation of the polynomial `C q⁻¹ * P`. -/
theorem expandingMap_eq_eval (q : K) (P : K[X]) (x : K) :
    expandingMap q P x = (C q⁻¹ * P).eval x := by
  rw [expandingMap, eval_mul, eval_C]

/-- The hypotheses on `F = q⁻¹ P` in `epd:eq:polynomial` that `epd:thm:bounded` uses:
`v(q) = κ > 0`, integral coefficients, unit leading coefficient and degree `d ≥ 2`. -/
structure IsExpanding (q : K) (P : K[X]) (κ : Γ) : Prop where
  val_q : v q = κ
  pos : 0 < κ
  coeff_nonneg : ∀ j, 0 ≤ v (P.coeff j)
  val_leadingCoeff : v P.leadingCoeff = 0
  two_le_natDegree : 2 ≤ P.natDegree

variable {v}
variable {q : K} {P : K[X]} {κ : Γ}

theorem map_inv_eq_neg (hq : v q = κ) : v q⁻¹ = ((-κ : Γ) : WithTop Γ) := by
  rw [AddValuation.map_inv, hq, WithTop.LinearOrderedAddCommGroup.coe_neg]

/-- On the integral disk an integral polynomial stays integral. -/
theorem map_eval_nonneg (hc : ∀ j, 0 ≤ v (P.coeff j)) {x : K} (hx : 0 ≤ v x) :
    0 ≤ v (P.eval x) := by
  rw [eval_eq_sum_range]
  refine AddValuation.map_le_sum v fun i _ => ?_
  rw [AddValuation.map_mul, AddValuation.map_pow]
  exact add_nonneg (hc i) (nsmul_nonneg hx i)

/-- Outside the integral disk the leading term dominates: `v(x) = a < 0` gives
`v(P(x)) = d a`. -/
theorem map_eval_of_neg (hc : ∀ j, 0 ≤ v (P.coeff j)) (hl : v P.leadingCoeff = 0) {x : K}
    {a : Γ} (hx : v x = a) (ha : a < 0) :
    v (P.eval x) = ((P.natDegree • a : Γ) : WithTop Γ) := by
  rw [eval_eq_sum_range, Finset.sum_range_succ, coeff_natDegree]
  have htop : v (P.leadingCoeff * x ^ P.natDegree) = ((P.natDegree • a : Γ) : WithTop Γ) := by
    rw [AddValuation.map_mul, AddValuation.map_pow, hx, hl, zero_add, WithTop.coe_nsmul]
  have hlow : ((P.natDegree • a : Γ) : WithTop Γ) <
      v (∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i) := by
    refine AddValuation.map_lt_sum v WithTop.coe_ne_top fun i hi => ?_
    rw [AddValuation.map_mul, AddValuation.map_pow, hx, ← WithTop.coe_nsmul]
    have hlt := nsmul_lt_nsmul_of_neg_of_lt ha (Finset.mem_range.mp hi)
    exact (WithTop.coe_lt_coe.mpr hlt).trans_le (le_add_of_nonneg_left (hc i))
  rw [AddValuation.map_add_eq_of_lt_right v (by rw [htop]; exact hlow), htop]

/-- For integral `x`, `v(F(x)) ≥ -κ`. -/
theorem neg_le_map_expandingMap (hE : IsExpanding v q P κ) {x : K} (hx : 0 ≤ v x) :
    ((-κ : Γ) : WithTop Γ) ≤ v (expandingMap q P x) := by
  rw [expandingMap, AddValuation.map_mul, map_inv_eq_neg hE.val_q]
  exact le_add_of_nonneg_right (map_eval_nonneg hE.coeff_nonneg hx)

/-- `epd:eq:escape-step`, the value: `v(x) = a < 0` gives `v(F(x)) = d a - κ`. -/
theorem map_expandingMap_of_neg (hE : IsExpanding v q P κ) {x : K} {a : Γ} (hx : v x = a)
    (ha : a < 0) : v (expandingMap q P x) = ((P.natDegree • a - κ : Γ) : WithTop Γ) := by
  rw [expandingMap, AddValuation.map_mul, map_inv_eq_neg hE.val_q,
    map_eval_of_neg hE.coeff_nonneg hE.val_leadingCoeff hx ha, ← WithTop.coe_add,
    neg_add_eq_sub]

/-- `epd:eq:escape-step`: if `v(x) = a < 0`, then `v(F(x)) = d a - κ < a < 0`. -/
theorem escape_step (hE : IsExpanding v q P κ) {x : K} {a : Γ} (hx : v x = a) (ha : a < 0) :
    v (expandingMap q P x) = ((P.natDegree • a - κ : Γ) : WithTop Γ) ∧
      P.natDegree • a - κ < a ∧ a < 0 := by
  refine ⟨map_expandingMap_of_neg hE hx ha, ?_, ha⟩
  have h1 : 1 ≤ P.natDegree := le_trans (by norm_num) hE.two_le_natDegree
  calc P.natDegree • a - κ < P.natDegree • a := sub_lt_self _ hE.pos
    _ ≤ 1 • a := nsmul_le_nsmul_of_nonpos_of_le ha.le h1
    _ = a := one_nsmul a

/-- `epd:eq:escape-step` in the form `v(F(y)) < v(y)` for `v(y) < 0`. -/
theorem map_expandingMap_lt_of_neg (hE : IsExpanding v q P κ) {y : K} (hy : v y < 0) :
    v (expandingMap q P y) < v y := by
  obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hy)
  have hg0 : g < 0 := by
    rw [← hg] at hy
    exact_mod_cast hy
  obtain ⟨h1, h2, -⟩ := escape_step hE hg.symm hg0
  rw [h1, ← hg]
  exact WithTop.coe_lt_coe.mpr h2

/-- The sentence after `epd:eq:escape-step`: a point with `v(x) < 0` never returns to `O`. -/
theorem map_iterate_lt_zero (hE : IsExpanding v q P κ) {x : K} (hx : v x < 0) (n : ℕ) :
    v ((expandingMap q P)^[n] x) < 0 := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (map_expandingMap_lt_of_neg hE ih).trans ih

/-- The sentence after `epd:eq:escape-step`: for `v(x) < 0` the valuations along the orbit
decrease strictly. -/
theorem strictAnti_map_iterate (hE : IsExpanding v q P κ) {x : K} (hx : v x < 0) :
    StrictAnti fun n => v ((expandingMap q P)^[n] x) :=
  strictAnti_nat_of_succ_lt fun n => by
    show v ((expandingMap q P)^[n + 1] x) < v ((expandingMap q P)^[n] x)
    rw [Function.iterate_succ_apply']
    exact map_expandingMap_lt_of_neg hE (map_iterate_lt_zero hE hx n)

/-- The sentence after `epd:eq:escape-step`, and the last clause of `epd:thm:periodic` (no
preperiodic points outside `O`): a point with `v(x) < 0` is not preperiodic, that is,
`F^{m+p}(x) ≠ F^m(x)` for all `m` and all `p ≥ 1`. -/
theorem iterate_add_ne_of_neg (hE : IsExpanding v q P κ) {x : K} (hx : v x < 0) (m : ℕ)
    {p : ℕ} (hp : 0 < p) : (expandingMap q P)^[m + p] x ≠ (expandingMap q P)^[m] x :=
  fun h => (strictAnti_map_iterate hE hx (Nat.lt_add_of_pos_right hp)).ne (congrArg v h)

/-- `epd:eq:outside-recurrence`: once `v(y) = -a < 0`, after `n` further steps
`v(Fⁿ(y)) = -dⁿ a - (1 + d + ⋯ + d^{n-1}) κ`. -/
theorem map_iterate_of_neg (hE : IsExpanding v q P κ) {y : K} {a : Γ}
    (hy : v y = ((-a : Γ) : WithTop Γ)) (ha : 0 < a) (n : ℕ) :
    v ((expandingMap q P)^[n] y) =
      ((-(P.natDegree ^ n • a + (∑ i ∈ Finset.range n, P.natDegree ^ i) • κ) : Γ) :
        WithTop Γ) := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
    have hd0 : P.natDegree ≠ 0 := by have := hE.two_le_natDegree; omega
    have hpos : 0 < P.natDegree ^ n • a + (∑ i ∈ Finset.range n, P.natDegree ^ i) • κ :=
      add_pos_of_pos_of_nonneg (nsmul_pos ha (pow_ne_zero n hd0)) (nsmul_nonneg hE.pos.le _)
    rw [Function.iterate_succ_apply', map_expandingMap_of_neg hE ih (neg_lt_zero.mpr hpos)]
    congr 1
    rw [geom_sum_succ, pow_succ', smul_neg, smul_add, smul_smul, smul_smul, add_smul, one_smul]
    abel

/-- The orbit of a point with `v(y) = -a < 0` is valuation-bounded exactly when `a + κ` is not
an order unit. This is the core of the proof of `epd:thm:bounded`, and uses `d ≥ 2`. -/
theorem bounded_iff_of_neg (hE : IsExpanding v q P κ) {y : K} {a : Γ}
    (hy : v y = ((-a : Γ) : WithTop Γ)) (ha : 0 < a) :
    (∃ β : Γ, ∀ n : ℕ, (β : WithTop Γ) ≤ v ((expandingMap q P)^[n] y)) ↔
      ¬ IsOrderUnit (a + κ) := by
  have hd := hE.two_le_natDegree
  have hak : 0 < a + κ := add_pos ha hE.pos
  constructor
  · rintro ⟨β, hβ⟩ hu
    obtain ⟨N, hN⟩ := hu.2 (-β)
    have h1 := hβ (N + 1)
    rw [map_iterate_of_neg hE hy ha, WithTop.coe_le_coe, le_neg] at h1
    have h2 := nsmul_le_escapeValue hd ha.le hE.pos.le (N + 1)
    rw [succ_nsmul] at h2
    have h3 : N • (a + κ) < N • (a + κ) + (a + κ) := lt_add_of_pos_right _ hak
    exact lt_irrefl _ (hN.trans_lt (h3.trans_le (h2.trans h1)))
  · intro hu
    obtain ⟨η, hη⟩ := (not_isOrderUnit_iff hak).mp hu
    refine ⟨-η, fun n => ?_⟩
    rw [map_iterate_of_neg hE hy ha, WithTop.coe_le_coe, neg_le_neg_iff]
    exact ((escapeValue_le hd a hE.pos.le n).trans_lt (hη _)).le

/-! ### The bounded-orbit locus -/

/-- `epd:thm:bounded`, `epd:eq:bounded-formula`:
`B_val(F) = B_int(F) ∪ {x : κ + α(x) is not an order unit}`. -/
theorem boundedLocus_eq (hE : IsExpanding v q P κ) :
    boundedLocus v (expandingMap q P) =
      integralLocus v (expandingMap q P) ∪ {x | ¬ IsOrderUnit (κ + exteriorDepth v x)} := by
  ext x
  by_cases hI : x ∈ integralLocus v (expandingMap q P)
  · exact iff_of_true (integralLocus_subset_boundedLocus v _ hI) (Or.inl hI)
  simp only [Set.mem_union, hI, false_or, Set.mem_setOf_eq]
  have hex : ∃ n, v ((expandingMap q P)^[n] x) < 0 := by
    rw [mem_integralLocus] at hI
    simpa only [not_forall, not_le] using hI
  classical
  obtain ⟨n₀, hn₀, hbefore⟩ : ∃ n₀, v ((expandingMap q P)^[n₀] x) < 0 ∧
      ∀ k < n₀, 0 ≤ v ((expandingMap q P)^[k] x) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => not_lt.mp (Nat.find_min hex hk)⟩
  obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hn₀)
  have hg0 : g < 0 := by
    rw [← hg] at hn₀
    exact_mod_cast hn₀
  have hy : v ((expandingMap q P)^[n₀] x) = ((-(-g) : Γ) : WithTop Γ) := by rw [neg_neg, hg]
  have ha : 0 < -g := neg_pos.mpr hg0
  have htail : x ∈ boundedLocus v (expandingMap q P) ↔
      ∃ β : Γ, ∀ n, (β : WithTop Γ) ≤ v ((expandingMap q P)^[n] ((expandingMap q P)^[n₀] x)) := by
    rw [mem_boundedLocus]
    constructor
    · rintro ⟨β, hβ⟩
      exact ⟨β, fun n => by rw [← Function.iterate_add_apply]; exact hβ _⟩
    · rintro ⟨β, hβ⟩
      refine ⟨min β 0, fun n => ?_⟩
      rcases lt_or_ge n n₀ with h | h
      · exact (WithTop.coe_le_coe.mpr (min_le_right _ _)).trans (by simpa using hbefore n h)
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' h
        rw [Function.iterate_add_apply]
        exact (WithTop.coe_le_coe.mpr (min_le_left _ _)).trans (hβ j)
  rw [htail, bounded_iff_of_neg hE hy ha]
  rcases n₀ with _ | m
  · have hx : v x = g := by simpa using hg.symm
    rw [exteriorDepth_of_eq v hx, max_eq_right ha.le, add_comm]
  · have hm := hbefore m (Nat.lt_succ_self m)
    have h0 : 0 ≤ v x := by simpa using hbefore 0 (Nat.succ_pos m)
    have hle : ((-κ : Γ) : WithTop Γ) ≤ g := by
      rw [hg, Function.iterate_succ_apply']
      exact neg_le_map_expandingMap hE hm
    rw [exteriorDepth_of_nonneg v h0, add_zero]
    exact not_congr (isOrderUnit_add_iff ha.le (neg_le.mp (WithTop.coe_le_coe.mp hle)) hE.pos)

/-- `epd:thm:bounded` (a): if `κ` is an order unit, `B_val(F) = B_int(F)`. -/
theorem boundedLocus_eq_integralLocus (hE : IsExpanding v q P κ) (hκ : IsOrderUnit κ) :
    boundedLocus v (expandingMap q P) = integralLocus v (expandingMap q P) := by
  rw [boundedLocus_eq hE]
  have hempty : {x | ¬ IsOrderUnit (κ + exteriorDepth v x)} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact isOrderUnit_of_le hκ (le_add_of_nonneg_right (exteriorDepth_nonneg v x))
  rw [hempty, Set.union_empty]

/-- `epd:thm:bounded` (b): if `κ` is not an order unit,
`B_val(F) = {x : κ + α(x) is not an order unit}`. -/
theorem boundedLocus_eq_of_not_isOrderUnit (hE : IsExpanding v q P κ)
    (hκ : ¬ IsOrderUnit κ) :
    boundedLocus v (expandingMap q P) = {x | ¬ IsOrderUnit (κ + exteriorDepth v x)} := by
  rw [boundedLocus_eq hE, Set.union_eq_right]
  intro x hx
  have h0 : 0 ≤ v x := by simpa using (mem_integralLocus v).mp hx 0
  simp only [Set.mem_setOf_eq, exteriorDepth_of_nonneg v h0, add_zero]
  exact hκ

/-- `epd:thm:bounded` (b): if `κ` is not an order unit, the bounded-orbit locus does not depend
on the map within the family (only on `κ = v(q)`). -/
theorem boundedLocus_eq_boundedLocus {q' : K} {P' : K[X]} (hE : IsExpanding v q P κ)
    (hE' : IsExpanding v q' P' κ) (hκ : ¬ IsOrderUnit κ) :
    boundedLocus v (expandingMap q P) = boundedLocus v (expandingMap q' P') := by
  rw [boundedLocus_eq_of_not_isOrderUnit hE hκ, boundedLocus_eq_of_not_isOrderUnit hE' hκ]

/-- `epd:thm:bounded` (b): if `κ` is not an order unit, `B_val(F)` contains `O`. -/
theorem setOf_nonneg_subset_boundedLocus (hE : IsExpanding v q P κ) (hκ : ¬ IsOrderUnit κ) :
    {x | 0 ≤ v x} ⊆ boundedLocus v (expandingMap q P) := by
  rw [boundedLocus_eq_of_not_isOrderUnit hE hκ]
  intro x hx
  simp only [Set.mem_setOf_eq, exteriorDepth_of_nonneg v hx, add_zero]
  exact hκ

/-- `epd:thm:bounded` (c): if `Γ` has no order unit, `B_val(F) = K`. -/
theorem boundedLocus_eq_univ (hE : IsExpanding v q P κ) (hΓ : ¬ ∃ u : Γ, IsOrderUnit u) :
    boundedLocus v (expandingMap q P) = Set.univ := by
  rw [boundedLocus_eq_of_not_isOrderUnit hE fun h => hΓ ⟨κ, h⟩, Set.eq_univ_iff_forall]
  exact fun _ h => hΓ ⟨_, h⟩

/-! ### The coarsened valuation ring -/

variable (v) in
/-- The valuation ring of the valuation coarsened by a subgroup `H ≤ Γ`: the `x` with
`v(x) ≥ h` for some `h ∈ H`. For convex `H` this is `v(x) + H ≥ 0` in `Γ/H`. -/
def coarsenedValuationSubring (H : AddSubgroup Γ) : ValuationSubring K where
  carrier := {x | ∃ h ∈ H, (h : WithTop Γ) ≤ v x}
  zero_mem' := ⟨0, H.zero_mem, by simp⟩
  one_mem' := ⟨0, H.zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨γ, hγ, ha⟩ ⟨δ, hδ, hb⟩
    refine ⟨min γ δ, ?_, ?_⟩
    · rcases min_choice γ δ with h | h <;> rw [h] <;> assumption
    · exact AddValuation.map_le_add v ((WithTop.coe_le_coe.mpr (min_le_left γ δ)).trans ha)
        ((WithTop.coe_le_coe.mpr (min_le_right γ δ)).trans hb)
  mul_mem' := by
    rintro a b ⟨γ, hγ, ha⟩ ⟨δ, hδ, hb⟩
    refine ⟨γ + δ, add_mem hγ hδ, ?_⟩
    rw [AddValuation.map_mul, WithTop.coe_add]
    exact add_le_add ha hb
  neg_mem' := by
    rintro a ⟨γ, hγ, ha⟩
    exact ⟨γ, hγ, by rwa [AddValuation.map_neg]⟩
  mem_or_inv_mem' := by
    intro x
    by_cases hx : 0 ≤ v x
    · exact Or.inl ⟨0, H.zero_mem, by simpa using hx⟩
    · refine Or.inr ⟨0, H.zero_mem, ?_⟩
      have hlt : v x < 0 := not_le.mp hx
      obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      rw [← hg] at hlt
      have hg0 : g < 0 := by exact_mod_cast hlt
      rw [AddValuation.map_inv, ← hg, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
        WithTop.coe_le_coe]
      exact neg_nonneg.mpr hg0.le

theorem mem_coarsenedValuationSubring {H : AddSubgroup Γ} {x : K} :
    x ∈ coarsenedValuationSubring v H ↔ ∃ h ∈ H, (h : WithTop Γ) ≤ v x :=
  Iff.rfl

/-- The coarsened valuation ring in the source's notation: `v(x) + H ≥ 0` in `Γ/H`, that is,
`v(x) + h ≥ 0` for some `h ∈ H`. -/
theorem mem_coarsenedValuationSubring_iff_add {H : AddSubgroup Γ} {x : K} :
    x ∈ coarsenedValuationSubring v H ↔ ∃ h ∈ H, 0 ≤ v x + (h : WithTop Γ) := by
  rw [mem_coarsenedValuationSubring]
  by_cases hx : x = 0
  · subst hx
    simp only [AddValuation.map_zero, le_top, and_true, top_add]
  · obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hx)
    rw [← hg]
    constructor
    · rintro ⟨h, hH, hle⟩
      refine ⟨-h, neg_mem hH, ?_⟩
      rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe, ← sub_eq_add_neg,
        sub_nonneg]
      exact WithTop.coe_le_coe.mp hle
    · rintro ⟨h, hH, hle⟩
      refine ⟨-h, neg_mem hH, ?_⟩
      rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at hle
      rw [WithTop.coe_le_coe]
      exact neg_le_iff_add_nonneg.mpr hle

/-- The valuation of `coarsenedValuationSubring v H` compares values of `v` modulo `H`: in
Mathlib's multiplicative convention, `w(x) ≤ w(y)` means `v(y) + h ≤ v(x)` for some `h ∈ H`.
So this ring is the valuation ring of the coarsened valuation `K^× → Γ/H` (for convex `H`),
although no quotient group is constructed. -/
theorem coarsenedValuation_le_iff {H : AddSubgroup Γ} {x y : K} (hy : y ≠ 0) :
    (coarsenedValuationSubring v H).valuation x ≤ (coarsenedValuationSubring v H).valuation y ↔
      ∃ h ∈ H, v y + (h : WithTop Γ) ≤ v x := by
  rw [ValuationSubring.valuation_le_iff]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨h, hH, ha⟩ := mem_coarsenedValuationSubring.mp a.2
    refine ⟨h, hH, ?_⟩
    rw [AddValuation.map_mul, add_comm]
    exact add_le_add ha le_rfl
  · rintro ⟨h, hH, hle⟩
    obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hy)
    refine ⟨⟨x * y⁻¹, mem_coarsenedValuationSubring.mpr ⟨h, hH, ?_⟩⟩,
      inv_mul_cancel_right₀ hy x⟩
    rw [AddValuation.map_mul, AddValuation.map_inv, ← hg,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    rw [← hg] at hle
    calc (h : WithTop Γ) = (g : WithTop Γ) + h + ((-g : Γ) : WithTop Γ) := by
          rw [← WithTop.coe_add, ← WithTop.coe_add]
          congr 1
          abel
      _ ≤ v x + ((-g : Γ) : WithTop Γ) := add_le_add hle le_rfl

/-- For a convex subgroup `H`, `α(x) ∈ H` exactly when `x` lies in the coarsened valuation
ring. -/
theorem exteriorDepth_mem_iff {H : AddSubgroup Γ} (hH : (H : Set Γ).OrdConnected) (x : K) :
    exteriorDepth v x ∈ H ↔ x ∈ coarsenedValuationSubring v H := by
  rw [mem_coarsenedValuationSubring]
  by_cases h0 : 0 ≤ v x
  · rw [exteriorDepth_of_nonneg v h0]
    exact iff_of_true H.zero_mem ⟨0, H.zero_mem, by simpa using h0⟩
  · have hlt : v x < 0 := not_le.mp h0
    obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    rw [← hg] at hlt
    have hg0 : g < 0 := by exact_mod_cast hlt
    rw [exteriorDepth_of_eq v hg.symm, max_eq_right (neg_nonneg.mpr hg0.le), neg_mem_iff, ← hg]
    constructor
    · intro hgH
      exact ⟨g, hgH, le_rfl⟩
    · rintro ⟨h, hH', hle⟩
      exact hH.out hH' H.zero_mem ⟨WithTop.coe_le_coe.mp hle, hg0.le⟩

/-- `epd:cor:coarsebounded`: if `Γ` has an order unit `u` but `κ` is not one, then `B_val(F)` is
the valuation ring `{x : v(x) + H ≥ 0 in Γ/H}` of the valuation coarsened by the maximal proper
convex subgroup `H`. -/
theorem boundedLocus_eq_coarsenedValuationSubring (hE : IsExpanding v q P κ) {u : Γ}
    (hu : IsOrderUnit u) (hκ : ¬ IsOrderUnit κ) :
    boundedLocus v (expandingMap q P) = coarsenedValuationSubring v (coarseSubgroup hu.1) := by
  rw [boundedLocus_eq_of_not_isOrderUnit hE hκ]
  ext x
  have hκH : κ ∈ coarseSubgroup hu.1 := (mem_coarseSubgroup_iff hu hE.pos).mpr hκ
  have hpos : 0 < κ + exteriorDepth v x :=
    add_pos_of_pos_of_nonneg hE.pos (exteriorDepth_nonneg v x)
  rw [Set.mem_setOf_eq, ← mem_coarseSubgroup_iff hu hpos,
    AddSubgroup.add_mem_cancel_left _ hκH, SetLike.mem_coe]
  exact exteriorDepth_mem_iff (ordConnected_coarseSubgroup hu.1) x

theorem mem_coarsened_of_eq {H : AddSubgroup Γ} {y : K} {γ : Γ} (hγ : γ ∈ H) (hy : v y = γ) :
    y ∈ coarsenedValuationSubring v H :=
  ⟨γ, hγ, hy.ge⟩

theorem inv_mem_coarsened_of_eq {H : AddSubgroup Γ} {y : K} {γ : Γ} (hγ : γ ∈ H)
    (hy : v y = γ) : y⁻¹ ∈ coarsenedValuationSubring v H :=
  ⟨-γ, neg_mem hγ, by rw [AddValuation.map_inv, hy, WithTop.LinearOrderedAddCommGroup.coe_neg]⟩

/-- An element with a finite value is nonzero. -/
theorem ne_zero_of_map_eq {y : K} {γ : Γ} (hy : v y = γ) : y ≠ 0 :=
  (AddValuation.ne_top_iff v).mp (by rw [hy]; exact WithTop.coe_ne_top)

/-- A nonzero `x` with `x, x⁻¹ ∈ R` is a unit of the valuation subring `R`. -/
theorem isUnit_mk_of_inv_mem {R : ValuationSubring K} {x : K} (hx0 : x ≠ 0) (hx : x ∈ R)
    (hinv : x⁻¹ ∈ R) : IsUnit (⟨x, hx⟩ : R) :=
  IsUnit.of_mul_eq_one ⟨x⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hx0))

/-- `epd:cor:coarsebounded`, last sentence: relative to the coarsened valuation ring `R`,
`q ≠ 0` and `q, q⁻¹ ∈ R`; `P` and the polynomial `C q⁻¹ * P` of `F = q⁻¹ P` have coefficients
in `R`; and the leading coefficient `lc` of `C q⁻¹ * P` satisfies `lc ≠ 0` and `lc, lc⁻¹ ∈ R`.
By `isUnit_mk_of_inv_mem`, `q` and `lc` are therefore units of `R`. -/
theorem coarsened_integral (hE : IsExpanding v q P κ) {u : Γ} (hu : IsOrderUnit u)
    (hκ : ¬ IsOrderUnit κ) :
    (q ≠ 0 ∧ q ∈ coarsenedValuationSubring v (coarseSubgroup hu.1) ∧
        q⁻¹ ∈ coarsenedValuationSubring v (coarseSubgroup hu.1)) ∧
      (∀ j, P.coeff j ∈ coarsenedValuationSubring v (coarseSubgroup hu.1)) ∧
      (∀ j, (C q⁻¹ * P).coeff j ∈ coarsenedValuationSubring v (coarseSubgroup hu.1)) ∧
      ((C q⁻¹ * P).leadingCoeff ≠ 0 ∧
        (C q⁻¹ * P).leadingCoeff ∈ coarsenedValuationSubring v (coarseSubgroup hu.1) ∧
        (C q⁻¹ * P).leadingCoeff⁻¹ ∈ coarsenedValuationSubring v (coarseSubgroup hu.1)) := by
  have hκH : κ ∈ coarseSubgroup hu.1 := (mem_coarseSubgroup_iff hu hE.pos).mpr hκ
  have hlead : v (C q⁻¹ * P).leadingCoeff = ((-κ : Γ) : WithTop Γ) := by
    rw [leadingCoeff_mul, leadingCoeff_C, AddValuation.map_mul, map_inv_eq_neg hE.val_q,
      hE.val_leadingCoeff, add_zero]
  refine ⟨⟨ne_zero_of_map_eq hE.val_q, mem_coarsened_of_eq hκH hE.val_q,
      inv_mem_coarsened_of_eq hκH hE.val_q⟩,
    fun j => ⟨0, zero_mem _, by simpa using hE.coeff_nonneg j⟩,
    fun j => ⟨-κ, neg_mem hκH, ?_⟩,
    ne_zero_of_map_eq hlead, mem_coarsened_of_eq (neg_mem hκH) hlead,
    inv_mem_coarsened_of_eq (neg_mem hκH) hlead⟩
  rw [coeff_C_mul, AddValuation.map_mul, map_inv_eq_neg hE.val_q]
  exact le_add_of_nonneg_right (hE.coeff_nonneg j)

end Generic

section Hahn

open _root_.HahnSeries Surreal.HahnSeries
open Surreal.BranchMetric (forwardMap perturbedPolynomial natDegree_perturbedPolynomial
  isUnit_leadingCoeff_perturbedPolynomial orderTop_eq_zero_of_standardPart_ne_zero)

variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

local notation "𝒪" => nonnegativeSubring Γ k

/-- The map `F = q⁻¹ P` of `Surreal.BranchMetric.forwardMap`, for `P ∈ O[X]`, is
`expandingMap` for the image of `P` in `K[X]`. -/
theorem forwardMap_eq (P : Polynomial 𝒪) (q : k⟦Γ⟧) :
    forwardMap P q = expandingMap q (P.map (nonnegativeSubring Γ k).subtype) :=
  rfl

/-- In `K = k⟦Γ⟧`, `B_int(f)` is the source's `{x : fⁿ(x) ∈ O for all n}`. -/
theorem mem_integralLocus_hahn {f : k⟦Γ⟧ → k⟦Γ⟧} {x : k⟦Γ⟧} :
    x ∈ integralLocus (addVal Γ k) f ↔ ∀ n : ℕ, f^[n] x ∈ 𝒪 := by
  simp only [mem_integralLocus, addVal_apply, mem_nonnegativeSubring]

/-- A polynomial over `O` of degree at least two with unit leading coefficient, and `q` with
`v(q) = κ > 0`, satisfy the hypotheses `IsExpanding` in `K = k⟦Γ⟧`. -/
theorem isExpanding_hahn {P : Polynomial 𝒪} (hdeg : 2 ≤ P.natDegree)
    (hlead : IsUnit P.leadingCoeff) {q : k⟦Γ⟧} {κ : Γ} (hq : q.orderTop = κ) (hκ : 0 < κ) :
    IsExpanding (addVal Γ k) q (P.map (nonnegativeSubring Γ k).subtype) κ where
  val_q := by rw [addVal_apply, hq]
  pos := hκ
  coeff_nonneg j := by
    rw [coeff_map, addVal_apply]
    exact (mem_nonnegativeSubring _).mp (P.coeff j).2
  val_leadingCoeff := by
    rw [leadingCoeff_map_of_injective Subtype.val_injective, addVal_apply]
    exact orderTop_eq_zero_of_standardPart_ne_zero
      ((isUnit_iff_standardPart_ne_zero _).mp hlead)
  two_le_natDegree := by rwa [natDegree_map_eq_of_injective Subtype.val_injective]

/-- The family `epd:eq:polynomial`, `P = a ∏ (X - c_i) + ∑_{j ≤ d} e_j X^j` with `a ≠ 0`,
`e_j ∈ 𝔪` and `d ≥ 2`, together with `v(q) = κ > 0`, satisfies `IsExpanding`. The
distinctness of the `c_i` (simple reduction) is not needed. -/
theorem isExpanding_perturbedPolynomial {d : ℕ} (hd : 2 ≤ d) {a : k} (ha : a ≠ 0)
    (c : Fin d → k) {e : Fin (d + 1) → 𝒪} (he : ∀ j, 0 < ((e j : 𝒪) : k⟦Γ⟧).orderTop)
    {q : k⟦Γ⟧} {κ : Γ} (hq : q.orderTop = κ) (hκ : 0 < κ) :
    IsExpanding (addVal Γ k) q
      ((perturbedPolynomial a c e).map (nonnegativeSubring Γ k).subtype) κ :=
  isExpanding_hahn (by rwa [natDegree_perturbedPolynomial ha c he])
    (isUnit_leadingCoeff_perturbedPolynomial ha c he) hq hκ

/-- `epd:thm:bounded` for `F = q⁻¹ P` with `P` in the family `epd:eq:polynomial` over
`K = k⟦Γ⟧`, `q ∈ 𝔪 \ {0}` and `κ = v(q)`: `epd:eq:bounded-formula`
`B_val(F) = B_int(F) ∪ {x : κ + α(x) is not an order unit}`, and its consequences
(a) if `κ` is an order unit, `B_val(F) = B_int(F)`; (b) otherwise
`B_val(F) = {x : κ + α(x) is not an order unit}` and `O ⊆ B_val(F)`; (c) if `Γ` has no order
unit, `B_val(F) = K`. The independence of `P` in (b) is `boundedLocus_perturbed_eq`. -/
theorem bounded {d : ℕ} (hd : 2 ≤ d) {a : k} (ha : a ≠ 0) (c : Fin d → k)
    {e : Fin (d + 1) → 𝒪} (he : ∀ j, 0 < ((e j : 𝒪) : k⟦Γ⟧).orderTop)
    {q : k⟦Γ⟧} {κ : Γ} (hq : q.orderTop = κ) (hκ : 0 < κ) :
    boundedLocus (addVal Γ k) (forwardMap (perturbedPolynomial a c e) q) =
        integralLocus (addVal Γ k) (forwardMap (perturbedPolynomial a c e) q) ∪
          {x | ¬ IsOrderUnit (κ + exteriorDepth (addVal Γ k) x)} ∧
      (IsOrderUnit κ → boundedLocus (addVal Γ k) (forwardMap (perturbedPolynomial a c e) q) =
        integralLocus (addVal Γ k) (forwardMap (perturbedPolynomial a c e) q)) ∧
      (¬ IsOrderUnit κ →
        boundedLocus (addVal Γ k) (forwardMap (perturbedPolynomial a c e) q) =
            {x | ¬ IsOrderUnit (κ + exteriorDepth (addVal Γ k) x)} ∧
          (𝒪 : Set k⟦Γ⟧) ⊆ boundedLocus (addVal Γ k) (forwardMap (perturbedPolynomial a c e) q)) ∧
      ((¬ ∃ u : Γ, IsOrderUnit u) →
        boundedLocus (addVal Γ k) (forwardMap (perturbedPolynomial a c e) q) = Set.univ) := by
  have hE := isExpanding_perturbedPolynomial hd ha c he hq hκ
  rw [forwardMap_eq]
  refine ⟨boundedLocus_eq hE, boundedLocus_eq_integralLocus hE, fun hκu =>
    ⟨boundedLocus_eq_of_not_isOrderUnit hE hκu, fun x hx => ?_⟩, boundedLocus_eq_univ hE⟩
  exact setOf_nonneg_subset_boundedLocus hE hκu (by
    rw [Set.mem_setOf_eq, addVal_apply]
    exact (mem_nonnegativeSubring x).mp hx)

/-- `epd:thm:bounded` (b): if `κ` is not an order unit, the bounded-orbit locus is the same for
all members of the family `epd:eq:polynomial` (and all `q` with `v(q) = κ`). -/
theorem boundedLocus_perturbed_eq {d d' : ℕ} (hd : 2 ≤ d) (hd' : 2 ≤ d') {a a' : k}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (c : Fin d → k) (c' : Fin d' → k) {e : Fin (d + 1) → 𝒪}
    {e' : Fin (d' + 1) → 𝒪} (he : ∀ j, 0 < ((e j : 𝒪) : k⟦Γ⟧).orderTop)
    (he' : ∀ j, 0 < ((e' j : 𝒪) : k⟦Γ⟧).orderTop) {q q' : k⟦Γ⟧} {κ : Γ} (hq : q.orderTop = κ)
    (hq' : q'.orderTop = κ) (hκ : 0 < κ) (hκu : ¬ IsOrderUnit κ) :
    boundedLocus (addVal Γ k) (forwardMap (perturbedPolynomial a c e) q) =
      boundedLocus (addVal Γ k) (forwardMap (perturbedPolynomial a' c' e') q') := by
  rw [forwardMap_eq, forwardMap_eq]
  exact boundedLocus_eq_boundedLocus (isExpanding_perturbedPolynomial hd ha c he hq hκ)
    (isExpanding_perturbedPolynomial hd' ha' c' he' hq' hκ) hκu

/-- `epd:cor:coarsebounded` for the family `epd:eq:polynomial` over `K = k⟦Γ⟧`: if `Γ` has an
order unit `u` but `κ = v(q)` is not one, then `B_val(F)` is the valuation ring
`{x : v(x) + H ≥ 0 in Γ/H}` of the valuation coarsened by the maximal proper convex subgroup
`H = coarseSubgroup`. Relative to that ring `R`: `q ≠ 0` and `q, q⁻¹ ∈ R`; `P` and `C q⁻¹ * P`
have coefficients in `R`; and the leading coefficient `lc` of `C q⁻¹ * P` satisfies `lc ≠ 0`
and `lc, lc⁻¹ ∈ R`. So `q` and `lc` are units of `R` (`isUnit_mk_of_inv_mem`). -/
theorem coarsebounded {d : ℕ} (hd : 2 ≤ d) {a : k} (ha : a ≠ 0) (c : Fin d → k)
    {e : Fin (d + 1) → 𝒪} (he : ∀ j, 0 < ((e j : 𝒪) : k⟦Γ⟧).orderTop)
    {q : k⟦Γ⟧} {κ : Γ} (hq : q.orderTop = κ) (hκ : 0 < κ) {u : Γ} (hu : IsOrderUnit u)
    (hκu : ¬ IsOrderUnit κ) :
    boundedLocus (addVal Γ k) (forwardMap (perturbedPolynomial a c e) q) =
        coarsenedValuationSubring (addVal Γ k) (coarseSubgroup hu.1) ∧
      let R := coarsenedValuationSubring (addVal Γ k) (coarseSubgroup hu.1)
      let P := (perturbedPolynomial a c e).map (nonnegativeSubring Γ k).subtype
      (q ≠ 0 ∧ q ∈ R ∧ q⁻¹ ∈ R) ∧ (∀ j, P.coeff j ∈ R) ∧ (∀ j, (C q⁻¹ * P).coeff j ∈ R) ∧
        ((C q⁻¹ * P).leadingCoeff ≠ 0 ∧ (C q⁻¹ * P).leadingCoeff ∈ R ∧
          (C q⁻¹ * P).leadingCoeff⁻¹ ∈ R) := by
  have hE := isExpanding_perturbedPolynomial hd ha c he hq hκ
  rw [forwardMap_eq]
  exact ⟨boundedLocus_eq_coarsenedValuationSubring hE hu hκu, coarsened_integral hE hu hκu⟩

end Hahn

end Surreal.ValuedIteration
