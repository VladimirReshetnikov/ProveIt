import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.MeasureTheory.Measure.Dirac
import Surreal.HahnSeries.MeasureAtomicity

/-!
# Finite real shadow, atom cardinality and the power-set extension

This file completes the classification of strong Hahn measures in
`docs/surreal/hahn-valued-measures-and-probability/article.tex` on top of
`StrongMeasure.lean`, `ScalarAtomicity.lean` and `MeasureAtomicity.lean`.

* `meas:thm:atomic`(iv): a strong Hahn measure on a countably separated space extends
  uniquely to a strong Hahn measure on the power set (the σ-algebra `⊤`), namely by the
  strong sum `A ↦ ∑ˢ_{x ∈ A} w_x` of `meas:eq:atomic`, and this extension is additive on every
  set-indexed disjoint family (`existsUnique_isStrongHahnMeasure_top`,
  `iUnion_of_isStrongHahnMeasure_top`). Uniqueness is proved more generally: a strong
  extension to any finer σ-algebra is given by `meas:eq:atomic` on its events
  (`eq_atomicMeasure_of_le`).
* `meas:prop:integration`(i) for arbitrary strong Hahn measures: the pushforward
  `B ↦ μ(f⁻¹ B)` along a measurable map is a strong Hahn measure, with no separation
  hypothesis (`IsStrongHahnMeasure.preimage`); on a countably separated space it is the
  atomic measure of the fibre masses (`preimage_eq_atomicMeasure_regroup`).
* `meas:cor:cardinality`: `W_μ = {x | w_x ≠ 0}` is the union over `γ ∈ S(μ)` of the finite
  sets `{x | coeff_γ w_x ≠ 0}`; hence `W_μ` is countable when `S(μ)` is, and
  `|W_μ| ≤ max(ℵ₀, |S(μ)|)`, with universe lifts when `X` and `Γ` live in different
  universes.
* `meas:cor:shadow`, for strong Hahn probabilities (`meas:def:positive`) over any linearly
  ordered additive group of coefficients with a `1`: every event mass lies in `[0, 1]`,
  no event mass (in particular no point weight) has a negative exponent, and the constant
  coefficient is a finite point-supported probability
  `coeff₀ μ(A) = ∑_{x ∈ A ∩ F₀} c_{0,x}` with `F₀ = {x | c_{0,x} ≠ 0}` finite,
  `c_{0,x} > 0` on `F₀` and `∑_{x ∈ F₀} c_{0,x} = 1` (`IsStrongHahnProbability.shadow`).
  For real coefficients the standard part is the ordinary probability measure
  `∑_{x ∈ F₀} c_{0,x} δ_x` (`IsStrongHahnProbability.exists_isProbabilityMeasure`).

The bounds `0 ≤ μ(A) ≤ 1` and the absence of negative exponents in event masses use only
finite additivity, not countable separation. The standard part `st` of the source is
represented by the coefficient at exponent `0`, which is its definition on the
nonnegative-valuation ring.
-/

universe u v

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

section Separation

variable {X : Type*}

/-- Countable separation passes to every finer σ-algebra, in particular to the power set;
this is the step `(X, 𝒫(X))` is still countably separated in `meas:thm:atomic`(iv). -/
theorem isCountablySeparated_of_le {m m' : MeasurableSpace X} (hm : m ≤ m')
    (hX : @IsCountablySeparated X m) : @IsCountablySeparated X m' := by
  obtain ⟨E, hE, hsep⟩ := hX
  exact ⟨E, fun n => hm _ (hE n), hsep⟩

/-- Singletons of a countably separated space are measurable. -/
theorem IsCountablySeparated.measurableSet_singleton {mX : MeasurableSpace X}
    (hX : IsCountablySeparated X) (x : X) : MeasurableSet ({x} : Set X) := by
  obtain ⟨E, hE, hsep⟩ := hX
  exact measurableSet_singleton_of_separated hE hsep x

end Separation

section Pushforward

variable {Γ R X Y : Type*} [PartialOrder Γ] [AddCommMonoid R] [MeasurableSpace X]
  [MeasurableSpace Y] {μ : Set X → R⟦Γ⟧}

/-- `meas:prop:integration`(i) for arbitrary strong Hahn measures: inverse images preserve
disjoint unions, so the pushforward `B ↦ μ(f⁻¹ B)` along a measurable map is a strong Hahn
measure. No countable separation and no atomic representation is needed. -/
theorem IsStrongHahnMeasure.preimage (hμ : IsStrongHahnMeasure μ) {f : X → Y}
    (hf : Measurable f) : IsStrongHahnMeasure fun B => μ (f ⁻¹' B) where
  empty := by simpa only [Set.preimage_empty] using hμ.empty
  iUnion A hA hdisj := by
    obtain ⟨s, hs, hsum⟩ := hμ.iUnion (fun n => f ⁻¹' A n) (fun n => hf (hA n))
      fun m n hmn => Disjoint.preimage f (hdisj hmn)
    exact ⟨s, hs, by simpa only [Set.preimage_iUnion] using hsum⟩

end Pushforward

section Additivity

variable {Γ R X : Type*} [PartialOrder Γ] [AddCommGroup R] [MeasurableSpace X]
  {μ : Set X → R⟦Γ⟧}

/-- Finite additivity of a strong Hahn measure, read off coefficientwise. -/
theorem IsStrongHahnMeasure.union (hμ : IsStrongHahnMeasure μ) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    μ (A ∪ B) = μ A + μ B := by
  ext γ
  rw [coeff_add]
  exact (isFinsumAdditive_coeff hμ γ).union hA hB hAB

end Additivity

section Weights

variable {Γ R X Y : Type*} [LinearOrder Γ] [AddCommGroup R] {mX : MeasurableSpace X}
  {μ : Set X → R⟦Γ⟧}

/-- `meas:thm:atomic`(i): the strongly summable family of point weights `w_x = μ({x})` of a
strong Hahn measure on a countably separated space. -/
def strongWeights (hμ : IsStrongHahnMeasure μ) (hX : IsCountablySeparated X) :
    SummableFamily Γ R X :=
  atomFamily (hasAtomicCoefficients_of_isStrongHahnMeasure hμ hX) hX

@[simp]
theorem strongWeights_apply (hμ : IsStrongHahnMeasure μ) (hX : IsCountablySeparated X)
    (x : X) : strongWeights hμ hX x = μ {x} :=
  rfl

/-- `meas:thm:atomic`(ii): every event mass is the strong sum of its point weights. -/
theorem eq_atomicMeasure_strongWeights (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X) {A : Set X} (hA : MeasurableSet A) :
    μ A = atomicMeasure (strongWeights hμ hX) A :=
  eq_atomicMeasure _ hX hA

/-- `meas:prop:integration`(i), representation: on a countably separated space the
pushforward of a strong Hahn measure along a measurable map is the atomic measure whose
weights are the fibre masses of the point weights. -/
theorem preimage_eq_atomicMeasure_regroup [MeasurableSpace Y] (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X) {f : X → Y} (hf : Measurable f) {B : Set Y}
    (hB : MeasurableSet B) :
    μ (f ⁻¹' B) = atomicMeasure (regroup (strongWeights hμ hX) f) B := by
  rw [atomicMeasure_regroup, ← eq_atomicMeasure_strongWeights hμ hX (hf hB)]

end Weights

section Extension

open MeasureTheory

variable {Γ R X : Type*} [LinearOrder Γ] [AddCommGroup R] {m m' : MeasurableSpace X}
  {μ ν : Set X → R⟦Γ⟧}

/-- `meas:thm:atomic`(iv), uniqueness, for any finer σ-algebra: a strong Hahn measure on a
finer σ-algebra that agrees with `μ` on the events of `μ` is given by `meas:eq:atomic` on all
of its events. -/
theorem eq_atomicMeasure_of_le (hm : m ≤ m') (hμ : @IsStrongHahnMeasure Γ R X _ _ m μ)
    (hX : @IsCountablySeparated X m) (hν : @IsStrongHahnMeasure Γ R X _ _ m' ν)
    (hνμ : ∀ A, MeasurableSet[m] A → ν A = μ A) {A : Set X} (hA : MeasurableSet[m'] A) :
    ν A = atomicMeasure (strongWeights hμ hX) A := by
  rw [eq_atomicMeasure_strongWeights hν (isCountablySeparated_of_le hm hX) hA]
  congr 1
  ext x : 1
  simp only [strongWeights_apply]
  exact hνμ _ (hX.measurableSet_singleton x)

/-- `meas:thm:atomic`(iv): a strong Hahn measure on a countably separated space extends
uniquely to a strong Hahn measure on the power set `𝒫(X)`, the σ-algebra `⊤`. The
extension is `A ↦ ∑ˢ_{x ∈ A} w_x`, by `eq_atomicMeasure_of_le`. -/
theorem existsUnique_isStrongHahnMeasure_top (hμ : @IsStrongHahnMeasure Γ R X _ _ m μ)
    (hX : @IsCountablySeparated X m) :
    ∃! ν : Set X → R⟦Γ⟧, @IsStrongHahnMeasure Γ R X _ _ ⊤ ν ∧
      ∀ A, MeasurableSet[m] A → ν A = μ A := by
  refine ⟨atomicMeasure (strongWeights hμ hX),
    ⟨@isStrongHahnMeasure_atomicMeasure Γ R X _ _ ⊤ _,
      fun A hA => (eq_atomicMeasure_strongWeights hμ hX hA).symm⟩, ?_⟩
  rintro ν ⟨hν, hνμ⟩
  funext A
  exact eq_atomicMeasure_of_le le_top hμ hX hν hνμ MeasurableSpace.measurableSet_top

/-- `meas:thm:atomic`(iv), arbitrary additivity: the strong extension to the power set is
additive on every set-indexed pairwise disjoint family, the sum being strong. -/
theorem iUnion_of_isStrongHahnMeasure_top {ι : Type*}
    (hμ : @IsStrongHahnMeasure Γ R X _ _ m μ) (hX : @IsCountablySeparated X m)
    (hν : @IsStrongHahnMeasure Γ R X _ _ ⊤ ν)
    (hνμ : ∀ A, MeasurableSet[m] A → ν A = μ A) {A : ι → Set X}
    (hA : Pairwise (Function.onFun Disjoint A)) :
    ∃ s : SummableFamily Γ R ι, (∀ i, s i = ν (A i)) ∧ ν (⋃ i, A i) = s.hsum := by
  have hν' : ν = atomicMeasure (strongWeights hμ hX) := funext fun B =>
    eq_atomicMeasure_of_le le_top hμ hX hν hνμ MeasurableSpace.measurableSet_top
  rw [hν']
  exact atomicMeasure_iUnion _ hA

end Extension

section Cardinality

open Cardinal

variable {X : Type u} {Γ : Type v} {R : Type*} [LinearOrder Γ] [AddCommGroup R]
  {mX : MeasurableSpace X} {μ : Set X → R⟦Γ⟧}

/-- `meas:cor:cardinality`, first clause: the atomic set `W_μ = {x | w_x ≠ 0}` is the union,
over the exponents of the global support, of the sets of points with a nonzero
coefficient there. Only measurability of singletons is used. -/
theorem setOf_singleton_ne_zero_eq_biUnion (hX : IsCountablySeparated X) :
    {x | μ {x} ≠ 0} = ⋃ γ ∈ globalSupport μ, {x | (μ {x}).coeff γ ≠ 0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro hx
    obtain ⟨γ, hγ⟩ : ∃ γ, (μ {x}).coeff γ ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (HahnSeries.ext (funext h))
    exact ⟨γ, ⟨{x}, hX.measurableSet_singleton x, hγ⟩, hγ⟩
  · rintro ⟨γ, -, hγ⟩ hx
    simp [hx] at hγ

/-- `meas:cor:cardinality`: each set `{x | coeff_γ w_x ≠ 0}` is finite. -/
theorem finite_setOf_singleton_coeff_ne_zero (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X) (γ : Γ) : {x | (μ {x}).coeff γ ≠ 0}.Finite :=
  finite_setOf_coeff_ne_zero (strongWeights hμ hX) γ

/-- `meas:cor:cardinality`: the atomic set is at most countable when the global support is. -/
theorem countable_setOf_singleton_ne_zero (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X) (hS : (globalSupport μ).Countable) :
    {x | μ {x} ≠ 0}.Countable := by
  rw [setOf_singleton_ne_zero_eq_biUnion hX]
  exact hS.biUnion fun γ _ => (finite_setOf_singleton_coeff_ne_zero hμ hX γ).countable

/-- `meas:cor:cardinality`: the atomic set has cardinality at most `max(ℵ₀, |S(μ)|)`, with
universe lifts since the space and the exponent group may live in different universes. -/
theorem lift_mk_setOf_singleton_ne_zero_le (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X) :
    lift.{v} #{x | μ {x} ≠ 0} ≤ max ℵ₀ (lift.{u} #(globalSupport μ)) := by
  rw [setOf_singleton_ne_zero_eq_biUnion hX]
  refine (mk_biUnion_le_lift (fun γ => {x : X | (μ {x}).coeff γ ≠ 0})
    (globalSupport μ)).trans ?_
  have hfin : ⨆ γ : globalSupport μ, lift.{v} #{x : X | (μ {x}).coeff γ.1 ≠ 0} ≤ ℵ₀ := by
    refine ciSup_le' fun γ => ?_
    rw [lift_le_aleph0]
    exact (lt_aleph0_iff_set_finite.mpr
      (finite_setOf_singleton_coeff_ne_zero hμ hX γ.1)).le
  calc lift.{u} #(globalSupport μ) * ⨆ γ : globalSupport μ,
          lift.{v} #{x : X | (μ {x}).coeff γ.1 ≠ 0}
      ≤ lift.{u} #(globalSupport μ) * ℵ₀ := by gcongr
    _ ≤ max (max (lift.{u} #(globalSupport μ)) ℵ₀) ℵ₀ := mul_le_max _ _
    _ = max ℵ₀ (lift.{u} #(globalSupport μ)) := by rw [max_assoc, max_self, max_comm]

/-- `meas:cor:cardinality` when the space and the exponent group share a universe:
`|W_μ| ≤ max(ℵ₀, |S(μ)|)`. -/
theorem mk_setOf_singleton_ne_zero_le {X Γ : Type u} [LinearOrder Γ]
    {mX : MeasurableSpace X} {μ : Set X → R⟦Γ⟧} (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X) : #{x | μ {x} ≠ 0} ≤ max ℵ₀ #(globalSupport μ) := by
  simpa only [lift_id] using lift_mk_setOf_singleton_ne_zero_le hμ hX

end Cardinality

section Probability

variable {Γ R X : Type*} [LinearOrder Γ] [Zero Γ] [AddCommGroup R] [One R] [LinearOrder R]
  [MeasurableSpace X]

/-- `meas:def:positive`: a strong Hahn probability is a strong Hahn measure whose event
masses are nonnegative and whose total mass is `1`. -/
structure IsStrongHahnProbability (μ : Set X → R⟦Γ⟧) : Prop
    extends IsStrongHahnMeasure μ where
  nonneg : ∀ A, MeasurableSet A → 0 ≤ toLex (μ A)
  univ : μ Set.univ = 1

/-- A Hahn series between `0` and `1` has no negative exponent: its first nonzero
coefficient would make it larger than `1`. -/
theorem coeff_eq_zero_of_neg_of_le_one {x : R⟦Γ⟧} (h0 : 0 ≤ toLex x)
    (h1 : toLex x ≤ toLex (1 : R⟦Γ⟧)) {g : Γ} (hg : g < 0) : x.coeff g = 0 := by
  by_contra hne
  have hpos : 0 < toLex x := by
    refine lt_of_le_of_ne h0 fun h => hne ?_
    rw [show x = ofLex (toLex x) from rfl, ← h]
    simp
  obtain ⟨i, hi, hipos⟩ := exists_coeff_pos_of_pos hpos
  have hi0 : i < 0 := by
    refine lt_of_le_of_lt ?_ hg
    by_contra hlt
    exact hne (hi g (lt_of_not_ge hlt))
  refine absurd h1 (not_le.mpr ((lt_iff _ _).mpr ⟨i, fun j hj => ?_, ?_⟩))
  · simp [hi j hj, (hj.trans hi0).ne]
  · simpa [hi0.ne] using hipos

namespace IsStrongHahnProbability

variable [IsOrderedAddMonoid R] {μ : Set X → R⟦Γ⟧}

/-- `meas:cor:shadow`: every event mass is at most `1`, by finite additivity and
positivity. -/
theorem le_one (hμ : IsStrongHahnProbability μ) {A : Set X} (hA : MeasurableSet A) :
    toLex (μ A) ≤ toLex (1 : R⟦Γ⟧) := by
  rw [← hμ.univ, ← Set.union_compl_self A,
    hμ.toIsStrongHahnMeasure.union hA hA.compl disjoint_compl_right, toLex_add]
  exact le_add_of_nonneg_right (hμ.nonneg _ hA.compl)

/-- `meas:cor:shadow`: every event mass lies in `[0, 1]`. -/
theorem mem_Icc (hμ : IsStrongHahnProbability μ) {A : Set X} (hA : MeasurableSet A) :
    toLex (μ A) ∈ Set.Icc 0 (toLex (1 : R⟦Γ⟧)) :=
  ⟨hμ.nonneg A hA, hμ.le_one hA⟩

/-- `meas:cor:shadow` and `meas:rem:probability-exponents`: no event mass has a negative
exponent. -/
theorem coeff_eq_zero_of_neg (hμ : IsStrongHahnProbability μ) {A : Set X}
    (hA : MeasurableSet A) {g : Γ} (hg : g < 0) : (μ A).coeff g = 0 :=
  coeff_eq_zero_of_neg_of_le_one (hμ.nonneg A hA) (hμ.le_one hA) hg

/-- `meas:cor:shadow`: every event mass has valuation at least `0`. -/
theorem zero_le_orderTop (hμ : IsStrongHahnProbability μ) {A : Set X}
    (hA : MeasurableSet A) : 0 ≤ (μ A).orderTop := by
  rw [le_orderTop_iff_forall]
  intro j hj
  exact hμ.coeff_eq_zero_of_neg hA (by exact_mod_cast hj)

variable (hμ : IsStrongHahnProbability μ) (hX : IsCountablySeparated X)
include hμ hX

/-- `meas:cor:shadow`: every point weight `w_x = μ({x})` has valuation at least `0`. -/
theorem zero_le_orderTop_singleton (x : X) : 0 ≤ (μ {x}).orderTop :=
  hμ.zero_le_orderTop (hX.measurableSet_singleton x)

open Classical in
/-- `meas:cor:shadow`, finite real shadow: the constant coefficients of the point weights
vanish outside a finite set `F₀`, are positive on `F₀` and sum to `1`, and the constant
coefficient of every event mass is the sum of the constant coefficients of its points
in `F₀`. -/
theorem exists_finset_coeff_zero :
    ∃ F : Finset X, (∀ x, x ∈ F ↔ (μ {x}).coeff 0 ≠ 0) ∧
      (∀ x ∈ F, 0 < (μ {x}).coeff 0) ∧ ∑ x ∈ F, (μ {x}).coeff 0 = 1 ∧
      ∀ A, MeasurableSet A → (μ A).coeff 0 = ∑ x ∈ F with x ∈ A, (μ {x}).coeff 0 := by
  obtain ⟨F, hF, hrep⟩ := coeff_eq_finiteAtomic hμ.toIsStrongHahnMeasure hX 0
  have hsing := hX.measurableSet_singleton
  refine ⟨F, fun x => ⟨hF x, fun hx => ?_⟩, fun x hx => ?_, ?_, fun A hA => ?_⟩
  · by_contra hxF
    exact hx (by rw [hrep _ (hsing x), finiteAtomic_singleton, if_neg hxF])
  · have hne : (μ {x}).coeff 0 ≠ 0 := hF x hx
    have hpos : 0 < toLex (μ {x}) := by
      refine lt_of_le_of_ne (hμ.nonneg _ (hsing x)) fun h => hne ?_
      rw [show μ {x} = ofLex (toLex (μ {x})) from rfl, ← h]
      simp
    obtain ⟨i, hi, hipos⟩ := exists_coeff_pos_of_pos hpos
    rcases lt_trichotomy i 0 with h | h | h
    · exact absurd (hμ.coeff_eq_zero_of_neg (hsing x) h) hipos.ne'
    · exact h ▸ hipos
    · exact absurd (hi 0 h) hne
  · have h1 := hrep Set.univ MeasurableSet.univ
    rw [hμ.univ, coeff_one, if_pos rfl, finiteAtomic] at h1
    rw [h1]
    simp
  · rw [hrep A hA, finiteAtomic]

open Classical in
/-- `meas:cor:shadow`: a strong Hahn probability on a countably separated space has event
masses in `[0, 1]`, point weights of valuation at least `0`, and a finite real shadow
`coeff₀ μ(A) = ∑_{x ∈ A ∩ F₀} c_{0,x}` with `F₀ = {x | c_{0,x} ≠ 0}`, `c_{0,x} > 0` on `F₀`
and `∑_{x ∈ F₀} c_{0,x} = 1`. -/
theorem shadow :
    (∀ A, MeasurableSet A → toLex (μ A) ∈ Set.Icc 0 (toLex (1 : R⟦Γ⟧))) ∧
    (∀ x, 0 ≤ (μ {x}).orderTop) ∧
    ∃ F : Finset X, (∀ x, x ∈ F ↔ (μ {x}).coeff 0 ≠ 0) ∧
      (∀ x ∈ F, 0 < (μ {x}).coeff 0) ∧ ∑ x ∈ F, (μ {x}).coeff 0 = 1 ∧
      ∀ A, MeasurableSet A → (μ A).coeff 0 = ∑ x ∈ F with x ∈ A, (μ {x}).coeff 0 :=
  ⟨fun _ hA => hμ.mem_Icc hA, hμ.zero_le_orderTop_singleton hX,
    hμ.exists_finset_coeff_zero hX⟩

end IsStrongHahnProbability

end Probability

section RealShadow

open MeasureTheory

variable {Γ X : Type*} [LinearOrder Γ] [Zero Γ] [MeasurableSpace X] {μ : Set X → ℝ⟦Γ⟧}

/-- `meas:cor:shadow` for real coefficients: the standard part of a strong Hahn probability
on a countably separated space is the ordinary probability measure
`∑_{x ∈ F₀} c_{0,x} δ_x` with finite point support and positive weights. -/
theorem IsStrongHahnProbability.exists_isProbabilityMeasure (hμ : IsStrongHahnProbability μ)
    (hX : IsCountablySeparated X) :
    ∃ F : Finset X, (∀ x, x ∈ F ↔ (μ {x}).coeff 0 ≠ 0) ∧ (∀ x ∈ F, 0 < (μ {x}).coeff 0) ∧
      IsProbabilityMeasure (∑ x ∈ F, ENNReal.ofReal ((μ {x}).coeff 0) • Measure.dirac x) ∧
      ∀ A, MeasurableSet A → (μ A).coeff 0 =
        (∑ x ∈ F, ENNReal.ofReal ((μ {x}).coeff 0) • Measure.dirac x).real A := by
  classical
  obtain ⟨F, hmem, hpos, hsum, hcoeff⟩ := hμ.exists_finset_coeff_zero hX
  have hP : ∀ A, MeasurableSet A →
      (∑ x ∈ F, ENNReal.ofReal ((μ {x}).coeff 0) • Measure.dirac x) A =
        ENNReal.ofReal (∑ x ∈ F with x ∈ A, (μ {x}).coeff 0) := by
    intro A hA
    rw [Measure.finsetSum_apply, ENNReal.ofReal_sum_of_nonneg
      fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' x hA, smul_eq_mul]
    by_cases hx : x ∈ A <;> simp [hx]
  refine ⟨F, hmem, hpos, ⟨?_⟩, fun A hA => ?_⟩
  · rw [hP _ MeasurableSet.univ]
    simp [hsum]
  · rw [Measure.real, hP A hA, ENNReal.toReal_ofReal
      (Finset.sum_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le), hcoeff A hA]

end RealShadow

end

end Surreal.HahnSeries
