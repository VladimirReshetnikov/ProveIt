import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.TFAE
import Surreal.HahnSeries.StrongMeasure

/-!
# The null-ideal positivity criterion for coefficientwise Hahn measures

This file formalizes the transfinite null-ideal positivity criterion, which appears as
`meas:thm:nullideal` in `docs/surreal/hahn-valued-measures-and-probability/article.tex` and as
`herg:thm:nullideal` in `docs/surcomplex/hahn-herglotz-positivity/article.tex`, together with
its corollaries `meas:cor:dominated` and `herg:cor:twoscale`.

Everything is proved on an arbitrary measurable space `X` and for an arbitrary linearly ordered
exponent set `Γ`: no topology on `X`, no countability of the support and no group structure on
`Γ` is used. A family `ν : Γ → SignedMeasure X` of finite real signed measures and a well-ordered
set `W ⊆ Γ` define the coefficientwise set function `coefSeries W hW ν`, namely
`A ↦ ∑_{γ ∈ W} ν_γ(A) t^γ` of `meas:eq:coef-measure` and `herg:def:measure`.

* `nullIdeal W ν γ` is the ideal `J_{<γ}` of `meas:eq:nullideal` and `herg:eq:nullideal`; it is a
  σ-ideal of measurable sets, equal to all measurable sets below the least exponent.
* `tfae_nonneg` is the equivalence (a) ⇔ (b) ⇔ (c) of `meas:thm:nullideal`, and
  `nonneg_iff_negPart` is the main equivalence of `herg:thm:nullideal`. The per-exponent
  translation between (b) and (c) is `criterion_at_iff`.
* `control ν β w` is the control measure of `meas:eq:control` and `herg:eq:control`, for an
  arbitrary family of exponents `β` and arbitrary nonzero weights `w`. Its null sets are the
  common null sets of the total variations, so the condition at `γ` is the absolute continuity
  `herg:eq:ACcriterion` (`negPart_null_iff_absolutelyContinuous`). With the source weights
  `2^{-j}` its mass is at most `1` (`control_univ_le_one`), and `exists_control` packages the
  countable-predecessor clause (the empty predecessor set gives the zero measure).
* `dominated`, `coefSeries_univ_eq_one` and `dominated_probability` are `meas:cor:dominated`.
* `twoScale` and `twoScale_measure` are `herg:cor:twoscale`, for an arbitrary finite measure in
  place of Haar measure on the circle. The two-scale measure is written
  `single 0 (ν₀ E) + single η (ν₁ E)`, so only `0 < η` in a linear order with zero is needed.

All clauses of the four source statements are proved. Not formalized here is the report's
separate Example `herg:ex:uncountable`, which shows that for uncountable predecessor sets no
countable control measure can replace the null ideal.
-/

namespace Surreal.NullIdeal

open MeasureTheory _root_.HahnSeries
open scoped ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X]

section SignedMeasure

variable (s : SignedMeasure X) {A : Set X}

/-- The Jordan identity `s(A) = s⁺(A) - s⁻(A)` on a measurable set. -/
theorem apply_eq_posPart_sub_negPart (hA : MeasurableSet A) :
    s A = s.toJordanDecomposition.posPart.real A - s.toJordanDecomposition.negPart.real A := by
  conv_lhs => rw [← s.toSignedMeasure_toJordanDecomposition]
  exact Measure.toSignedMeasure_sub_apply hA

/-- A signed measure that is nonnegative on all measurable subsets of `A` has negative part
zero on `A`. -/
theorem negPart_eq_zero_of_nonneg (hA : MeasurableSet A)
    (h : ∀ B, MeasurableSet B → B ⊆ A → 0 ≤ s B) : s.toJordanDecomposition.negPart A = 0 := by
  obtain ⟨i, hi, -, hi₃, -, hneg⟩ := s.toJordanDecomposition_spec
  have hle : s (iᶜ ∩ A) ≤ 0 := by
    simpa using VectorMeasure.subset_le_of_restrict_le_restrict s 0 hi.compl hi₃
      Set.inter_subset_left
  have hge : 0 ≤ s (iᶜ ∩ A) := h _ (hi.compl.inter hA) Set.inter_subset_right
  rw [← measureReal_eq_zero_iff, hneg,
    SignedMeasure.toMeasureOfLEZero_real_apply _ hi₃ hi.compl hA]
  linarith

/-- The negative part vanishes on a measurable set exactly when the signed measure is
nonnegative on all its measurable subsets. -/
theorem negPart_eq_zero_iff (hA : MeasurableSet A) :
    s.toJordanDecomposition.negPart A = 0 ↔ ∀ B, MeasurableSet B → B ⊆ A → 0 ≤ s B := by
  refine ⟨fun h B hB hBA => ?_, negPart_eq_zero_of_nonneg s hA⟩
  have hB0 : s.toJordanDecomposition.negPart.real B = 0 := by
    simp [measureReal_def, measure_mono_null hBA h]
  rw [apply_eq_posPart_sub_negPart s hB, hB0, sub_zero]
  exact measureReal_nonneg

/-- A signed measure that is nonnegative on the measurable subsets of `A` and has mass zero on
`A` has total variation zero on `A`. -/
theorem totalVariation_eq_zero_of_nonneg (hA : MeasurableSet A)
    (h : ∀ B, MeasurableSet B → B ⊆ A → 0 ≤ s B) (h0 : s A = 0) :
    s.totalVariation A = 0 := by
  have hneg := negPart_eq_zero_of_nonneg s hA h
  have hnegR : s.toJordanDecomposition.negPart.real A = 0 := by simp [measureReal_def, hneg]
  have hposR : s.toJordanDecomposition.posPart.real A = 0 := by
    have := apply_eq_posPart_sub_negPart s hA
    rw [h0, hnegR, sub_zero] at this
    exact this.symm
  rw [SignedMeasure.totalVariation, Measure.add_apply, hneg, add_zero]
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hposR

/-- The total variation of a signed measure is a finite measure. -/
instance isFiniteMeasure_totalVariation : IsFiniteMeasure s.totalVariation := by
  rw [SignedMeasure.totalVariation]
  infer_instance

/-- A signed measure is nonnegative exactly when its negative part is zero. -/
theorem nonneg_iff_negPart_eq_zero : 0 ≤ s ↔ s.toJordanDecomposition.negPart = 0 := by
  rw [← Measure.measure_univ_eq_zero, negPart_eq_zero_iff s MeasurableSet.univ,
    VectorMeasure.le_iff]
  exact ⟨fun h B hB _ => h B hB, fun h B hB => h B hB (Set.subset_univ B)⟩

/-- The total variation of an ordinary finite measure is the measure itself. -/
theorem totalVariation_toSignedMeasure (m : Measure X) [IsFiniteMeasure m] :
    m.toSignedMeasure.totalVariation = m := by
  let j : JordanDecomposition X :=
    { posPart := m, negPart := 0, mutuallySingular := Measure.MutuallySingular.zero_right }
  have hj : m.toSignedMeasure.toJordanDecomposition = j := by
    apply SignedMeasure.toJordanDecomposition_eq
    simp [j, JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_zero]
  rw [SignedMeasure.totalVariation, hj]
  simp [j]

end SignedMeasure

section Criterion

variable {Γ : Type*} [LinearOrder Γ]

open scoped Classical in
/-- `meas:eq:coef-measure` and `herg:def:measure`: the coefficientwise Hahn measure
`A ↦ ∑_{γ ∈ W} ν_γ(A) t^γ` of a family of finite signed measures indexed by a well-ordered set
`W`. The measures at exponents outside `W` are ignored. -/
def coefSeries (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure X) (A : Set X) : ℝ⟦Γ⟧ where
  coeff γ := if γ ∈ W then ν γ A else 0
  isPWO_support' := hW.isPWO.mono fun γ hγ => by
    by_contra h
    exact hγ (if_neg h)

/-- `meas:eq:nullideal` and `herg:eq:nullideal`: the ideal `J_{<γ}` of measurable sets that are
null for the total variation of every earlier coefficient measure. -/
def nullIdeal (W : Set Γ) (ν : Γ → SignedMeasure X) (γ : Γ) : Set (Set X) :=
  {A | MeasurableSet A ∧ ∀ δ ∈ W, δ < γ → (ν δ).totalVariation A = 0}

variable {W : Set Γ} (hW : W.IsWF) {ν : Γ → SignedMeasure X} {γ : Γ} {A B : Set X}

open scoped Classical in
theorem coeff_coefSeries (γ : Γ) :
    (coefSeries W hW ν A).coeff γ = if γ ∈ W then ν γ A else 0 :=
  rfl

theorem coeff_coefSeries_of_mem (h : γ ∈ W) : (coefSeries W hW ν A).coeff γ = ν γ A :=
  if_pos h

theorem coeff_coefSeries_of_notMem (h : γ ∉ W) : (coefSeries W hW ν A).coeff γ = 0 :=
  if_neg h

theorem empty_mem_nullIdeal : ∅ ∈ nullIdeal W ν γ :=
  ⟨MeasurableSet.empty, fun _ _ _ => measure_empty⟩

/-- `J_{<γ}` is closed under measurable subsets. -/
theorem mem_nullIdeal_of_subset (hA : A ∈ nullIdeal W ν γ) (hB : MeasurableSet B)
    (hBA : B ⊆ A) : B ∈ nullIdeal W ν γ :=
  ⟨hB, fun δ hδ hlt => measure_mono_null hBA (hA.2 δ hδ hlt)⟩

/-- `J_{<γ}` is closed under countable unions, hence is a σ-ideal of measurable sets. -/
theorem iUnion_mem_nullIdeal {ι : Type*} [Countable ι] {A : ι → Set X}
    (h : ∀ i, A i ∈ nullIdeal W ν γ) : (⋃ i, A i) ∈ nullIdeal W ν γ :=
  ⟨MeasurableSet.iUnion fun i => (h i).1,
    fun δ hδ hlt => measure_iUnion_null fun i => (h i).2 δ hδ hlt⟩

/-- Below every exponent of `W`, in particular at `min W`, the null ideal is all of `Σ`. -/
theorem nullIdeal_eq_of_forall_not_lt (h : ∀ δ ∈ W, ¬δ < γ) :
    nullIdeal W ν γ = {A | MeasurableSet A} := by
  ext A
  exact ⟨fun hA => hA.1, fun hA => ⟨hA, fun δ hδ hlt => absurd hlt (h δ hδ)⟩⟩

/-- `J_{<min W} = Σ`. -/
theorem nullIdeal_min (hne : W.Nonempty) :
    nullIdeal W ν (hW.min hne) = {A | MeasurableSet A} :=
  nullIdeal_eq_of_forall_not_lt fun _ hδ => hW.not_lt_min hne hδ

/-- The two forms of the condition at a single exponent `γ`: nonnegativity on measurable sets
null for all earlier total variations (`meas:eq:null-criterion`, the (b)-form) is equivalent to
the vanishing of the negative part on `J_{<γ}` (`herg:eq:nullcriterion`, the (c)-form). -/
theorem criterion_at_iff :
    (∀ A, MeasurableSet A → (∀ δ ∈ W, δ < γ → (ν δ).totalVariation A = 0) → 0 ≤ ν γ A) ↔
      ∀ A ∈ nullIdeal W ν γ, (ν γ).toJordanDecomposition.negPart A = 0 := by
  constructor
  · rintro h A ⟨hA, hnull⟩
    refine negPart_eq_zero_of_nonneg (ν γ) hA fun B hB hBA => h B hB fun δ hδW hδ => ?_
    exact measure_mono_null hBA (hnull δ hδW hδ)
  · intro h A hA hnull
    exact (negPart_eq_zero_iff (ν γ) hA).mp (h A ⟨hA, hnull⟩) A hA subset_rfl

/-- `meas:thm:nullideal`, (a) ⇒ (b): if an event is null for all total variations before `γ`,
every earlier coefficient of its mass vanishes, so a negative `ν_γ`-mass would be a negative
leading coefficient. -/
theorem criterion_of_nonneg (h : ∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries W hW ν A))
    (hγ : γ ∈ W) (hA : MeasurableSet A)
    (hnull : ∀ δ ∈ W, δ < γ → (ν δ).totalVariation A = 0) : 0 ≤ ν γ A := by
  by_contra hneg
  push Not at hneg
  have hlt : toLex (coefSeries W hW ν A) < 0 := by
    rw [_root_.HahnSeries.lt_iff]
    refine ⟨γ, fun δ hδ => ?_, ?_⟩
    · by_cases hδW : δ ∈ W
      · simpa [coeff_coefSeries_of_mem hW hδW] using
          (ν δ).null_of_totalVariation_zero (hnull δ hδW hδ)
      · simpa using coeff_coefSeries_of_notMem hW (A := A) hδW
    · simpa [coeff_coefSeries_of_mem hW hγ] using hneg
  exact absurd (h A hA) (not_le.mpr hlt)

/-- `meas:thm:nullideal`, (b) ⇒ (a): at the least exponent `γ` with `ν_γ(A) ≠ 0`, a
well-founded induction over the earlier exponents of `W` shows that `A` is null for every
earlier total variation; then (b) at `γ` makes the leading coefficient positive. -/
theorem nonneg_of_criterion
    (h : ∀ γ ∈ W, ∀ A, MeasurableSet A → (∀ δ ∈ W, δ < γ → (ν δ).totalVariation A = 0) →
      0 ≤ ν γ A) (hA : MeasurableSet A) : 0 ≤ toLex (coefSeries W hW ν A) := by
  by_cases hx : coefSeries W hW ν A = 0
  · rw [hx]
    exact le_rfl
  have hne : (coefSeries W hW ν A).support.Nonempty := support_nonempty_iff.mpr hx
  have hwf := (coefSeries W hW ν A).isWF_support
  set γ := hwf.min hne
  have hγ : (coefSeries W hW ν A).coeff γ ≠ 0 := hwf.min_mem hne
  have hγW : γ ∈ W := by
    by_contra h'
    exact hγ (coeff_coefSeries_of_notMem hW h')
  have hbelow : ∀ δ < γ, (coefSeries W hW ν A).coeff δ = 0 := fun δ hδ => by
    by_contra h'
    exact hwf.not_lt_min hne h' hδ
  have hnull : ∀ δ ∈ W, δ < γ → (ν δ).totalVariation A = 0 := by
    intro δ hδW
    refine Set.WellFoundedOn.induction hW hδW
      (P := fun δ => δ < γ → (ν δ).totalVariation A = 0) ?_
    intro δ hδW ih hδγ
    refine totalVariation_eq_zero_of_nonneg (ν δ) hA (fun B hB hBA => ?_) ?_
    · refine h δ hδW B hB fun δ' hδ'W hδ'δ => ?_
      exact measure_mono_null hBA (ih δ' hδ'W hδ'δ (hδ'δ.trans hδγ))
    · rw [← coeff_coefSeries_of_mem hW hδW]
      exact hbelow δ hδγ
  have hγA : (coefSeries W hW ν A).coeff γ = ν γ A := coeff_coefSeries_of_mem hW hγW
  have hpos : 0 < ν γ A :=
    lt_of_le_of_ne (h γ hγW A hA hnull) fun h0 => hγ (hγA.trans h0.symm)
  exact (Surreal.HahnSeries.pos_of_coeff hbelow (hγA ▸ hpos)).le

/-- `meas:thm:nullideal`: for a well-ordered `W` of any cardinality on an arbitrary measurable
space, the following are equivalent:
(a) `μ(A) ≥ 0` for every measurable `A`;
(b) for every `γ ∈ W` and measurable `A`, if `|ν_δ|(A) = 0` for all `δ < γ` in `W`, then
`ν_γ(A) ≥ 0`;
(c) `ν_γ⁻(A) = 0` for every `γ ∈ W` and every `A ∈ J_{<γ}`. -/
theorem tfae_nonneg :
    List.TFAE [∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries W hW ν A),
      ∀ γ ∈ W, ∀ A, MeasurableSet A → (∀ δ ∈ W, δ < γ → (ν δ).totalVariation A = 0) →
        0 ≤ ν γ A,
      ∀ γ ∈ W, ∀ A ∈ nullIdeal W ν γ, (ν γ).toJordanDecomposition.negPart A = 0] := by
  tfae_have 1 → 2 := fun h _ hγ _ hA hnull => criterion_of_nonneg hW h hγ hA hnull
  tfae_have 2 → 1 := fun h _ hA => nonneg_of_criterion hW h hA
  tfae_have 2 ↔ 3 := forall₂_congr fun _ _ => criterion_at_iff
  tfae_finish

/-- `herg:thm:nullideal` (`herg:eq:nullcriterion`), equivalently (a) ⇔ (c) of
`meas:thm:nullideal`: the coefficientwise Hahn measure is positive exactly when every negative
coefficient part vanishes on the null ideal of the earlier coefficients. -/
theorem nonneg_iff_negPart :
    (∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries W hW ν A)) ↔
      ∀ γ ∈ W, ∀ A ∈ nullIdeal W ν γ, (ν γ).toJordanDecomposition.negPart A = 0 :=
  (tfae_nonneg hW).out 0 2

/-- (a) ⇔ (b) of `meas:thm:nullideal`, the form of the criterion in the source of the
measures report. -/
theorem nonneg_iff_criterion :
    (∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries W hW ν A)) ↔
      ∀ γ ∈ W, ∀ A, MeasurableSet A → (∀ δ ∈ W, δ < γ → (ν δ).totalVariation A = 0) →
        0 ≤ ν γ A :=
  (tfae_nonneg hW).out 0 1

end Criterion

section Control

variable {Γ : Type*} {ι : Type*}

/-- `meas:eq:control` and `herg:eq:control` with arbitrary weights: the control measure
`∑_i w_i |ν_{β_i}| / (1 + ‖ν_{β_i}‖_TV)` of a family of exponents `β`. The source takes an
enumeration `β_j` of the predecessors of `γ` and `w_j = 2^{-j}`. -/
def control (ν : Γ → SignedMeasure X) (β : ι → Γ) (w : ι → ℝ≥0∞) : Measure X :=
  Measure.sum fun i =>
    (w i / (1 + (ν (β i)).totalVariation Set.univ)) • (ν (β i)).totalVariation

variable {ν : Γ → SignedMeasure X} {β : ι → Γ} {w : ι → ℝ≥0∞} {A : Set X}

/-- The null sets of the control measure are the common null sets of the total variations,
since every weight is strictly positive. -/
theorem control_apply_eq_zero_iff (hw : ∀ i, w i ≠ 0) (hA : MeasurableSet A) :
    control ν β w A = 0 ↔ ∀ i, (ν (β i)).totalVariation A = 0 := by
  rw [control, Measure.sum_apply_eq_zero' hA]
  refine forall_congr' fun i => ?_
  have hfin : 1 + (ν (β i)).totalVariation Set.univ ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, measure_ne_top _ _⟩
  rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero, ENNReal.div_eq_zero_iff]
  simp [hw i, hfin]

/-- The mass of the control measure is at most the total weight. -/
theorem control_univ_le : control ν β w Set.univ ≤ ∑' i, w i := by
  rw [control, Measure.sum_apply _ MeasurableSet.univ]
  refine ENNReal.tsum_le_tsum fun i => ?_
  set t := (ν (β i)).totalVariation Set.univ
  have h0 : 1 + t ≠ 0 := (zero_lt_one.trans_le le_self_add).ne'
  have htop : 1 + t ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, measure_ne_top _ _⟩
  rw [Measure.smul_apply, smul_eq_mul]
  calc w i / (1 + t) * t ≤ w i / (1 + t) * (1 + t) := by gcongr; exact le_add_self
    _ = w i := ENNReal.div_mul_cancel h0 htop

/-- The geometric weights `2^{-(e i + 1)}` along an injective numbering have total mass at
most `1`. -/
theorem tsum_geometric_le_one {e : ι → ℕ} (he : Function.Injective e) :
    ∑' i, (2⁻¹ : ℝ≥0∞) ^ (e i + 1) ≤ 1 := by
  refine (ENNReal.tsum_comp_le_tsum_of_injective he fun n => (2⁻¹ : ℝ≥0∞) ^ (n + 1)).trans_eq ?_
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- With the weights `2^{-j}` of `meas:eq:control`, the control measure has mass at most `1`. -/
theorem control_univ_le_one {e : ι → ℕ} (he : Function.Injective e) :
    control ν β (fun i => (2⁻¹ : ℝ≥0∞) ^ (e i + 1)) Set.univ ≤ 1 :=
  control_univ_le.trans (tsum_geometric_le_one he)

/-- A control measure of finite total weight is a finite measure. -/
theorem isFiniteMeasure_control (hw : ∑' i, w i ≠ ∞) : IsFiniteMeasure (control ν β w) :=
  ⟨control_univ_le.trans_lt hw.lt_top⟩

/-- An empty family of exponents gives the zero control measure. -/
theorem control_of_isEmpty [IsEmpty ι] : control ν β w = 0 := by
  rw [control]
  exact Measure.sum_eq_zero.mpr fun i => isEmptyElim i

variable [LinearOrder Γ] {W : Set Γ} {γ : Γ}

/-- When `β` enumerates the predecessors of `γ` in `W`, the null sets of the control measure
are exactly the members of `J_{<γ}`. -/
theorem mem_nullIdeal_iff_control (hβ : Set.range β = {δ | δ ∈ W ∧ δ < γ})
    (hw : ∀ i, w i ≠ 0) (hA : MeasurableSet A) :
    A ∈ nullIdeal W ν γ ↔ control ν β w A = 0 := by
  rw [control_apply_eq_zero_iff hw hA]
  constructor
  · intro h i
    have hi : β i ∈ {δ | δ ∈ W ∧ δ < γ} := hβ ▸ Set.mem_range_self i
    exact h.2 _ hi.1 hi.2
  · intro h
    refine ⟨hA, fun δ hδ hlt => ?_⟩
    obtain ⟨i, rfl⟩ : δ ∈ Set.range β := hβ ▸ ⟨hδ, hlt⟩
    exact h i

/-- `herg:eq:ACcriterion` and the control-measure clause of `meas:thm:nullideal`: when `β`
enumerates the predecessors of `γ` in `W` (with any nonzero weights), the condition at `γ` is
the absolute continuity `ν_γ⁻ ≪ λ_{<γ}`. No countability is needed for this equivalence. -/
theorem negPart_null_iff_absolutelyContinuous (hβ : Set.range β = {δ | δ ∈ W ∧ δ < γ})
    (hw : ∀ i, w i ≠ 0) :
    (∀ A ∈ nullIdeal W ν γ, (ν γ).toJordanDecomposition.negPart A = 0) ↔
      (ν γ).toJordanDecomposition.negPart ≪ control ν β w := by
  constructor
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
    exact h A ((mem_nullIdeal_iff_control hβ hw hA).mpr hA0)
  · intro h A hA
    exact h (((mem_nullIdeal_iff_control hβ hw hA.1).mp hA))

/-- The countable-predecessor clause of `meas:thm:nullideal` and `herg:thm:nullideal`: if the
predecessors of `γ` in `W` form a countable set, then the control measure of `meas:eq:control`
built from an enumeration of them (the zero measure if there are none) is a finite measure of
mass at most `1` whose null measurable sets are exactly `J_{<γ}`, and the condition at `γ` is
`ν_γ⁻ ≪ λ_{<γ}`. -/
theorem exists_control (hc : {δ | δ ∈ W ∧ δ < γ}.Countable) :
    ∃ l : Measure X, IsFiniteMeasure l ∧ l Set.univ ≤ 1 ∧
      (∀ A, MeasurableSet A → (A ∈ nullIdeal W ν γ ↔ l A = 0)) ∧
      ((∀ A ∈ nullIdeal W ν γ, (ν γ).toJordanDecomposition.negPart A = 0) ↔
        (ν γ).toJordanDecomposition.negPart ≪ l) := by
  have : Countable {δ | δ ∈ W ∧ δ < γ} := hc.to_subtype
  obtain ⟨e, he⟩ := Countable.exists_injective_nat {δ | δ ∈ W ∧ δ < γ}
  have hβ : Set.range (Subtype.val : {δ | δ ∈ W ∧ δ < γ} → Γ) = {δ | δ ∈ W ∧ δ < γ} :=
    Subtype.range_coe
  have hw : ∀ i : {δ | δ ∈ W ∧ δ < γ}, (2⁻¹ : ℝ≥0∞) ^ (e i + 1) ≠ 0 := fun i =>
    pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
  have hle := control_univ_le_one (ν := ν) (β := Subtype.val) he
  refine ⟨control ν Subtype.val fun i => (2⁻¹ : ℝ≥0∞) ^ (e i + 1),
    ⟨hle.trans_lt ENNReal.one_lt_top⟩, hle,
    fun A hA => mem_nullIdeal_iff_control hβ hw hA,
    negPart_null_iff_absolutelyContinuous hβ hw⟩

end Control

section Dominated

variable {Γ : Type*} [LinearOrder Γ] [Zero Γ] {W : Set Γ} (hW : W.IsWF)
  {ν : Γ → SignedMeasure X}

/-- `meas:cor:dominated`: if `0 ∈ W ⊆ Γ_{≥0}`, `ν_0` is an ordinary probability `P` and every
later coefficient measure is absolutely continuous with respect to `P`, then every event has
nonnegative mass, and the mass vanishes exactly on the `P`-null events. -/
theorem dominated (hW0 : ∀ γ ∈ W, 0 ≤ γ) (h0W : (0 : Γ) ∈ W) (P : Measure X)
    [IsProbabilityMeasure P] (h0 : ν 0 = P.toSignedMeasure)
    (hac : ∀ γ ∈ W, 0 < γ → ν γ ≪ᵥ P.toENNRealVectorMeasure) {A : Set X}
    (hA : MeasurableSet A) :
    0 ≤ toLex (coefSeries W hW ν A) ∧ (coefSeries W hW ν A = 0 ↔ P A = 0) := by
  have hcoeff0 : (coefSeries W hW ν A).coeff 0 = P.real A := by
    rw [coeff_coefSeries_of_mem hW h0W, h0, Measure.toSignedMeasure_apply_measurable hA]
  by_cases hPA : P A = 0
  · have hx : coefSeries W hW ν A = 0 := by
      ext γ
      rw [coeff_zero]
      by_cases hγW : γ ∈ W
      · rw [coeff_coefSeries_of_mem hW hγW]
        rcases (hW0 γ hγW).lt_or_eq with hγ | rfl
        · exact hac γ hγW hγ (by rwa [Measure.toENNRealVectorMeasure_apply_measurable hA])
        · rw [h0, Measure.toSignedMeasure_apply_measurable hA, measureReal_def, hPA,
            ENNReal.toReal_zero]
      · exact coeff_coefSeries_of_notMem hW hγW
    rw [hx]
    exact ⟨le_rfl, iff_of_true rfl hPA⟩
  · have hpos : 0 < P.real A := ENNReal.toReal_pos hPA (measure_ne_top _ _)
    have hbelow : ∀ δ < (0 : Γ), (coefSeries W hW ν A).coeff δ = 0 := fun δ hδ =>
      coeff_coefSeries_of_notMem hW fun hδW => (hW0 δ hδW).not_gt hδ
    have hlt := Surreal.HahnSeries.pos_of_coeff hbelow (hcoeff0 ▸ hpos)
    refine ⟨hlt.le, iff_of_false (fun hx => ?_) hPA⟩
    rw [hx] at hlt
    exact lt_irrefl _ hlt

/-- `meas:cor:dominated`, normalization: if moreover `ν_γ(X) = 0` for every `γ > 0` in `W`, then
`μ(X) = 1`, so `μ` is a coefficientwise Hahn probability. -/
theorem coefSeries_univ_eq_one (hW0 : ∀ γ ∈ W, 0 ≤ γ) (h0W : (0 : Γ) ∈ W) (P : Measure X)
    [IsProbabilityMeasure P] (h0 : ν 0 = P.toSignedMeasure)
    (hnorm : ∀ γ ∈ W, 0 < γ → ν γ Set.univ = 0) : coefSeries W hW ν Set.univ = 1 := by
  ext γ
  rw [← single_zero_one, coeff_single]
  by_cases hγW : γ ∈ W
  · rw [coeff_coefSeries_of_mem hW hγW]
    rcases (hW0 γ hγW).lt_or_eq with hγ | rfl
    · rw [if_neg hγ.ne', hnorm γ hγW hγ]
    · rw [if_pos rfl, h0, Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
        probReal_univ]
  · rw [coeff_coefSeries_of_notMem hW hγW, if_neg]
    rintro rfl
    exact hγW h0W

/-- `meas:cor:dominated`, last clause: under the hypotheses of `dominated` and the normalization
`ν_γ(X) = 0` for `γ > 0`, `μ` is a coefficientwise Hahn probability (`meas:def:positive`): it is
positive on every event and `μ(X) = 1`. -/
theorem dominated_probability (hW0 : ∀ γ ∈ W, 0 ≤ γ) (h0W : (0 : Γ) ∈ W) (P : Measure X)
    [IsProbabilityMeasure P] (h0 : ν 0 = P.toSignedMeasure)
    (hac : ∀ γ ∈ W, 0 < γ → ν γ ≪ᵥ P.toENNRealVectorMeasure)
    (hnorm : ∀ γ ∈ W, 0 < γ → ν γ Set.univ = 0) :
    (∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries W hW ν A)) ∧
      coefSeries W hW ν Set.univ = 1 :=
  ⟨fun _ hA => (dominated hW hW0 h0W P h0 hac hA).1,
    coefSeries_univ_eq_one hW hW0 h0W P h0 hnorm⟩

end Dominated

section TwoScale

variable {Γ : Type*} [LinearOrder Γ] [Zero Γ]

/-- `herg:cor:twoscale`: for `η > 0` and finite signed measures `ν₀, ν₁`, the two-scale measure
`ν₀ + t^η ν₁` is positive exactly when `ν₀ ≥ 0` and `ν₁⁻ ≪ |ν₀|`; once `ν₀ ≥ 0`, the total
variation `|ν₀|` is `ν₀` itself (`totalVariation_toSignedMeasure`). -/
theorem twoScale {η : Γ} (hη : 0 < η) (ν₀ ν₁ : SignedMeasure X) :
    (∀ E, MeasurableSet E → 0 ≤ toLex (single 0 (ν₀ E) + single η (ν₁ E))) ↔
      0 ≤ ν₀ ∧ ν₁.toJordanDecomposition.negPart ≪ ν₀.totalVariation := by
  classical
  obtain ⟨ν, hν0, hνη⟩ : ∃ ν : Γ → SignedMeasure X, ν 0 = ν₀ ∧ ν η = ν₁ :=
    ⟨fun γ => if γ = 0 then ν₀ else ν₁, if_pos rfl, if_neg hη.ne'⟩
  have hW : ({0, η} : Set Γ).IsWF := (Set.toFinite _).isWF
  have hser : ∀ E, coefSeries {0, η} hW ν E = single 0 (ν₀ E) + single η (ν₁ E) := by
    intro E
    ext γ
    rw [coeff_coefSeries, coeff_add, coeff_single, coeff_single]
    by_cases h0 : γ = 0
    · subst h0
      simp [hν0, hη.ne]
    · by_cases h1 : γ = η
      · subst h1
        simp [hνη, h0]
      · simp [h0, h1]
  simp_rw [← hser]
  rw [nonneg_iff_negPart hW]
  constructor
  · intro h
    refine ⟨?_, Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_⟩
    · rw [nonneg_iff_negPart_eq_zero, ← Measure.measure_univ_eq_zero, ← hν0]
      refine h 0 (by simp) Set.univ ⟨MeasurableSet.univ, fun δ hδ hlt => ?_⟩
      rcases hδ with rfl | rfl
      · exact absurd hlt (lt_irrefl _)
      · exact absurd hlt hη.not_gt
    · rw [← hνη]
      refine h η (by simp) A ⟨hA, fun δ hδ hlt => ?_⟩
      rcases hδ with rfl | rfl
      · rwa [hν0]
      · exact absurd hlt (lt_irrefl _)
  · rintro ⟨hnn, hac⟩ γ hγ A ⟨hA, hnull⟩
    rcases hγ with rfl | rfl
    · rw [hν0, (nonneg_iff_negPart_eq_zero ν₀).mp hnn]
      rfl
    · rw [hνη]
      refine hac ?_
      have := hnull 0 (by simp) hη
      rwa [hν0] at this

/-- `herg:cor:twoscale`, second form: for a finite measure `m` (Haar measure on the circle in
the source) and a finite signed measure `ν`, `m + t^η ν ≥ 0` exactly when `ν⁻ ≪ m`. -/
theorem twoScale_measure {η : Γ} (hη : 0 < η) (m : Measure X) [IsFiniteMeasure m]
    (ν : SignedMeasure X) :
    (∀ E, MeasurableSet E → 0 ≤ toLex (single 0 (m.real E) + single η (ν E))) ↔
      ν.toJordanDecomposition.negPart ≪ m := by
  calc (∀ E, MeasurableSet E → 0 ≤ toLex (single 0 (m.real E) + single η (ν E)))
      ↔ ∀ E, MeasurableSet E → 0 ≤ toLex (single 0 (m.toSignedMeasure E) + single η (ν E)) :=
        forall₂_congr fun E hE => by rw [Measure.toSignedMeasure_apply_measurable hE]
    _ ↔ _ := twoScale hη _ _
    _ ↔ _ := by
        rw [totalVariation_toSignedMeasure, and_iff_right (Measure.zero_le_toSignedMeasure m)]

end TwoScale

end

end Surreal.NullIdeal
