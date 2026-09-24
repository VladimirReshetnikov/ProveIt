import Mathlib.MeasureTheory.Measure.Dirac
import Surreal.HahnSeries.StrongMeasureShadow
import Surreal.Foundations.SignSequenceStrongRegroup
import Surreal.Foundations.SignSequenceStandardPart
import Surreal.Foundations.SmallNormalFormLeading
import Surreal.Surcomplex.StrongRegroup
import Surreal.Surcomplex.StrongConstants

/-!
# Strong measures with actual surreal and surcomplex values

This file proves `meas:cor:actual` in
`docs/surreal/hahn-valued-measures-and-probability/article.tex` by instantiating the generic
strong Hahn measure theory of `StrongMeasure.lean`, `ScalarAtomicity.lean`,
`MeasureAtomicity.lean` and `StrongMeasureShadow.lean` at the canonical normal forms of the
actual surreal field `No = SignSequence` and of the actual surcomplex numbers `No[i]`.

An `No`-valued set function `μ` on a measurable space is *countably additive by canonical
strong normal-form sums* (`IsStrongSurrealMeasure`) when `μ(∅) = 0` and the masses of every
pairwise disjoint measurable sequence are actually strongly summable
(`SignSequence.StronglySummable`), with actual strong sum (`SignSequence.strongSum`) the
mass of the union; `IsStrongSurcomplexMeasure` is the `No[i]`-valued analogue. The masses of
the sets that are not events play no role.

* Transfer: such a `μ` is exactly a set function whose canonical normal forms
  `A ↦ rawNormalForm (μ A)`, Hahn series over the exponents `Surreal.{u}ᵒᵈ` with real (resp.
  complex) coefficients, form a strong Hahn measure (`isStrongSurrealMeasure_iff`,
  `isStrongSurcomplexMeasure_iff`). No common support is assumed.
* `meas:cor:actual`, atomicity: on a countably separated space the singleton masses are
  actually strongly summable, and on a countably separated *set-sized* space
  (`Small.{u} X`) every event mass is the actual strong sum of its singleton masses,
  `μ(A) = ∑ˢ_{x ∈ A} μ({x})` (`IsStrongSurrealMeasure.eq_strongSum_singleton`,
  `IsStrongSurcomplexMeasure.eq_strongSum_singleton`, and the existential forms
  `IsStrongSurrealMeasure.exists_strongSum_singleton`,
  `IsStrongSurcomplexMeasure.exists_strongSum_singleton`). Conversely every strongly summable
  `No`-valued family indexed by a set-sized space defines such a measure
  (`isStrongSurrealMeasure_atomicSurrealMeasure`), which gives the actual form of the atomic
  classification for `No` (`isStrongSurrealMeasure_iff_exists`).
* `meas:cor:actual`, coefficients: on a countably separated space, for every exponent `γ` the
  points whose singleton mass has nonzero coefficient at `γ` form a finite set `F_γ`, and the
  `γ`-coefficient of every event mass is the sum of those of its points in `F_γ`
  (`IsStrongSurrealMeasure.exists_finset_coeff`,
  `IsStrongSurcomplexMeasure.exists_finset_coeff`).
* `meas:cor:actual`, common support: on a countably separated space, the union of the
  normal-form supports of all event masses is well ordered in `Surreal.{u}ᵒᵈ` (reverse well
  ordered in `No`), and on a set-sized space it is `u`-small, so it is an admissible support
  of an actual surreal
  (`IsStrongSurrealMeasure.exists_common_support`,
  `IsStrongSurcomplexMeasure.exists_common_support`).
* `meas:cor:actual`, real shadow: a positive normalized `No`-valued measure has canonical
  normal forms forming a strong Hahn probability. Every event mass lies in `[0, 1]`, is finite,
  and its actual standard part (`SignSequence.standardPart`, Mathlib's `stdPart`) is the
  constant normal-form coefficient (`IsStrongSurrealMeasure.mem_Icc_and_standardPart`). The
  standard part is a finitely supported ordinary probability on a countably separated space:
  `st μ(A) = ∑_{x ∈ A ∩ F} st μ({x})` with a finite set `F` of points of positive standard
  mass summing to `1` (`IsStrongSurrealMeasure.exists_finset_standardPart`), and it is the
  Mathlib probability measure `∑_{x ∈ F} st μ({x}) δ_x`
  (`IsStrongSurrealMeasure.exists_isProbabilityMeasure_standardPart`).

The atomicity, coefficient and common-support clauses are proved for both `No` and `No[i]`,
the latter under `IsStrongSurcomplexMeasure` via `isStrongSurcomplexMeasure_iff`; the converse
atomic classification and the real shadow are stated for `No` only (the source states the real
shadow for `No` only). Two auxiliary facts about actual surreals are proved on the way:
canonical normal forms reflect the order (`le_iff_toLex_rawNormalForm`,
`lt_iff_toLex_rawNormalForm`), and a surreal whose normal form has no negative exponent in
`Surreal.{u}ᵒᵈ` is finite with standard part its constant coefficient
(`isFinite_and_standardPart_eq_coeff_zero`). Nothing is asserted about measures on the full
power class of `No`.
-/

universe u v

namespace Surreal.ActualStrongMeasures

open _root_.HahnSeries Surreal.HahnSeries Foundations Foundations.SignSequence

noncomputable section

section Order

/-- Canonical normal forms reflect nonnegativity of actual surreals. -/
theorem nonneg_iff_toLex_rawNormalForm (x : SignSequence.{u}) :
    0 ≤ x ↔ 0 ≤ toLex (rawNormalForm x) := by
  conv_lhs => rw [← SmallNormalForm.cutEvaluation_normalForm x]
  rw [SmallNormalForm.cutEvaluation_nonneg_iff]
  exact Iff.rfl

/-- The canonical normal form is an order embedding into the lexicographic Hahn field. -/
theorem le_iff_toLex_rawNormalForm (x y : SignSequence.{u}) :
    x ≤ y ↔ toLex (rawNormalForm x) ≤ toLex (rawNormalForm y) := by
  rw [← sub_nonneg, nonneg_iff_toLex_rawNormalForm, rawNormalForm_sub, toLex_sub, sub_nonneg]

/-- The canonical normal form reflects the strict order of actual surreals. -/
theorem lt_iff_toLex_rawNormalForm (x y : SignSequence.{u}) :
    x < y ↔ toLex (rawNormalForm x) < toLex (rawNormalForm y) := by
  rw [← not_le, ← not_le, le_iff_toLex_rawNormalForm]

/-- An actual surreal whose normal form has no negative exponent in `Surreal.{u}ᵒᵈ`, that is no
infinite term, is finite, and its standard part is its constant normal-form coefficient. -/
theorem isFinite_and_standardPart_eq_coeff_zero {x : SignSequence.{u}}
    (hx : ∀ g : _root_.Surreal.{u}ᵒᵈ, g < 0 → (rawNormalForm x).coeff g = 0) :
    SignSequence.IsFinite x ∧ SignSequence.standardPart x = (rawNormalForm x).coeff 0 := by
  have hinf : SignSequence.IsInfinitesimal
      (x - SignSequence.ofReal ((rawNormalForm x).coeff 0)) := by
    rw [isInfinitesimal_iff_forall_real_abs_lt]
    intro r hr
    rw [abs_lt, lt_iff_toLex_rawNormalForm, lt_iff_toLex_rawNormalForm, rawNormalForm_neg,
      rawNormalForm_ofReal]
    constructor
    · refine (_root_.HahnSeries.lt_iff _ _).mpr ⟨0, fun j hj => ?_, ?_⟩
      · simp [hx j hj, coeff_single_of_ne hj.ne]
      · simp [hr]
    · refine (_root_.HahnSeries.lt_iff _ _).mpr ⟨0, fun j hj => ?_, ?_⟩
      · simp [hx j hj, coeff_single_of_ne hj.ne]
      · simp [hr]
  have hfin : SignSequence.IsFinite x := by
    simpa using finite_add (finite_of_infinitesimal hinf)
      (finite_ofReal ((rawNormalForm x).coeff 0))
  exact ⟨hfin, (infinitesimal_sub_ofReal_iff hfin).mp hinf⟩

end Order

section Real

variable {X : Type v} [MeasurableSpace X]

/-- `meas:cor:actual`: an `No`-valued set function countably additive by canonical strong
normal-form sums. The empty set has mass zero, and the masses of every pairwise disjoint
measurable sequence are actually strongly summable, with strong sum the mass of the union. -/
structure IsStrongSurrealMeasure (μ : Set X → SignSequence.{u}) : Prop where
  empty : μ ∅ = 0
  iUnion : ∀ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) →
    Pairwise (Function.onFun Disjoint A) →
    ∃ h : SignSequence.StronglySummable (fun n => μ (A n)),
      μ (⋃ n, A n) = SignSequence.strongSum (fun n => μ (A n)) h

variable {μ : Set X → SignSequence.{u}}

/-- Actual strong additivity is exactly strong additivity of the canonical normal forms, so
the generic theory applies with exponents `Surreal.{u}ᵒᵈ` and real coefficients. -/
theorem isStrongSurrealMeasure_iff :
    IsStrongSurrealMeasure μ ↔ IsStrongHahnMeasure (fun A => rawNormalForm (μ A)) := by
  constructor
  · intro hμ
    refine ⟨by simp [hμ.empty], fun A hA hdisj => ?_⟩
    obtain ⟨h, hsum⟩ := hμ.iUnion A hA hdisj
    refine ⟨h.toHahnFamily, fun n => rfl, ?_⟩
    show rawNormalForm (μ (⋃ n, A n)) = h.toHahnFamily.hsum
    rw [hsum, rawNormalForm_strongSum]
  · intro hμ
    refine ⟨rawNormalForm_injective (by simpa using hμ.empty), fun A hA hdisj => ?_⟩
    obtain ⟨s, hs, hsum⟩ := hμ.iUnion A hA hdisj
    have h : SignSequence.StronglySummable (fun n => μ (A n)) :=
      stronglySummable_of_hahnFamily s hs
    refine ⟨h, rawNormalForm_injective ?_⟩
    have hst : h.toHahnFamily = s := SummableFamily.ext fun n => (hs n).symm
    rw [rawNormalForm_strongSum, hst]
    exact hsum

namespace IsStrongSurrealMeasure

/-- `meas:cor:actual`: the singleton masses of an actual strong measure on a countably
separated space are actually strongly summable. -/
theorem stronglySummable_singleton (hμ : IsStrongSurrealMeasure μ)
    (hX : IsCountablySeparated X) : SignSequence.StronglySummable (fun x : X => μ {x}) :=
  stronglySummable_of_hahnFamily (strongWeights (isStrongSurrealMeasure_iff.mp hμ) hX)
    fun _ => rfl

/-- The normal-form family of the singleton masses is the generic family of strong weights of
the normal-form measure. -/
theorem toHahnFamily_stronglySummable_singleton (hμ : IsStrongSurrealMeasure μ)
    (hX : IsCountablySeparated X) :
    (hμ.stronglySummable_singleton hX).toHahnFamily =
      strongWeights (isStrongSurrealMeasure_iff.mp hμ) hX :=
  SummableFamily.ext fun _ => rfl

/-- `meas:cor:actual`: on a countably separated set-sized space, every event mass of an
actual strong measure is the actual strong sum of its singleton masses. -/
theorem eq_strongSum_singleton [Small.{u} X] (hμ : IsStrongSurrealMeasure μ)
    (hX : IsCountablySeparated X) {A : Set X} (hA : MeasurableSet A) :
    μ A = SignSequence.strongSum (fun x : A => μ {x.1})
      ((hμ.stronglySummable_singleton hX).restrict A) := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, toHahnFamily_restrict (hμ.stronglySummable_singleton hX) A,
    toHahnFamily_stronglySummable_singleton hμ hX]
  exact eq_atomicMeasure_strongWeights (isStrongSurrealMeasure_iff.mp hμ) hX hA

/-- `meas:cor:actual`, existential form: every event mass is a strong sum of its singleton
masses. -/
theorem exists_strongSum_singleton [Small.{u} X] (hμ : IsStrongSurrealMeasure μ)
    (hX : IsCountablySeparated X) {A : Set X} (hA : MeasurableSet A) :
    ∃ h : SignSequence.StronglySummable (fun x : A => μ {x.1}),
      μ A = SignSequence.strongSum (fun x : A => μ {x.1}) h :=
  ⟨_, hμ.eq_strongSum_singleton hX hA⟩

open Classical in
/-- `meas:cor:actual`: every normal-form coefficient is carried by finitely many points. For
each exponent `γ` there is a finite set `F_γ` whose points are exactly those whose singleton
mass has nonzero coefficient at `γ`, and the `γ`-coefficient of every event mass is the sum of
the coefficients of its points in `F_γ`. -/
theorem exists_finset_coeff (hμ : IsStrongSurrealMeasure μ) (hX : IsCountablySeparated X)
    (γ : _root_.Surreal.{u}ᵒᵈ) :
    ∃ F : Finset X, (∀ x, x ∈ F ↔ (rawNormalForm (μ {x})).coeff γ ≠ 0) ∧
      ∀ A, MeasurableSet A → (rawNormalForm (μ A)).coeff γ =
        ∑ x ∈ F with x ∈ A, (rawNormalForm (μ {x})).coeff γ := by
  obtain ⟨F, hF, hrep⟩ := coeff_eq_finiteAtomic (isStrongSurrealMeasure_iff.mp hμ) hX γ
  refine ⟨F, fun x => ⟨hF x, fun hx => ?_⟩, fun A hA => ?_⟩
  · by_contra hxF
    exact hx (by rw [hrep _ (hX.measurableSet_singleton x), finiteAtomic_singleton,
      if_neg hxF])
  · rw [hrep A hA, finiteAtomic]

/-- `meas:cor:actual`: at each exponent only finitely many singleton masses have a nonzero
normal-form coefficient. -/
theorem finite_setOf_rawNormalForm_coeff_ne_zero (hμ : IsStrongSurrealMeasure μ)
    (hX : IsCountablySeparated X) (γ : _root_.Surreal.{u}ᵒᵈ) :
    {x | (rawNormalForm (μ {x})).coeff γ ≠ 0}.Finite :=
  finite_setOf_singleton_coeff_ne_zero (isStrongSurrealMeasure_iff.mp hμ) hX γ

/-- `meas:cor:actual`: the union of the normal-form supports of all event masses is well
ordered, without any common-support assumption. -/
theorem isWF_globalSupport (hμ : IsStrongSurrealMeasure μ) (hX : IsCountablySeparated X) :
    (globalSupport fun A => rawNormalForm (μ A)).IsWF :=
  Surreal.HahnSeries.isWF_globalSupport
    (hasAtomicCoefficients_of_isStrongHahnMeasure (isStrongSurrealMeasure_iff.mp hμ) hX) hX

/-- `meas:cor:actual`: on a countably separated set-sized space the global support is the
union of the supports of the singleton masses, hence `u`-small. -/
theorem small_globalSupport [Small.{u} X] (hμ : IsStrongSurrealMeasure μ)
    (hX : IsCountablySeparated X) : Small.{u} (globalSupport fun A => rawNormalForm (μ A)) := by
  rw [globalSupport_eq_iUnion
    (hasAtomicCoefficients_of_isStrongHahnMeasure (isStrongSurrealMeasure_iff.mp hμ) hX) hX]
  infer_instance

/-- `meas:cor:actual`: all event masses of an actual strong measure on a countably separated
set-sized space have a common admissible support, a `u`-small subset of `Surreal.{u}ᵒᵈ` that
is well ordered, that is reverse well ordered in `No`. -/
theorem exists_common_support [Small.{u} X] (hμ : IsStrongSurrealMeasure μ)
    (hX : IsCountablySeparated X) :
    ∃ S : Set _root_.Surreal.{u}ᵒᵈ, S.IsWF ∧ Small.{u} S ∧
      ∀ A, MeasurableSet A → (rawNormalForm (μ A)).support ⊆ S :=
  ⟨_, hμ.isWF_globalSupport hX, hμ.small_globalSupport hX, fun A hA _ hγ => ⟨A, hA, hγ⟩⟩

section Probability

/-- A positive normalized actual strong measure has normal forms forming a strong Hahn
probability. -/
theorem isStrongHahnProbability (hμ : IsStrongSurrealMeasure μ)
    (hpos : ∀ A, MeasurableSet A → 0 ≤ μ A) (hone : μ Set.univ = 1) :
    IsStrongHahnProbability (fun A => rawNormalForm (μ A)) where
  toIsStrongHahnMeasure := isStrongSurrealMeasure_iff.mp hμ
  nonneg A hA := (nonneg_iff_toLex_rawNormalForm _).mp (hpos A hA)
  univ := by simp [hone]

/-- `meas:cor:actual`: every event mass of a positive normalized actual strong measure lies in
`[0, 1]`, is finite, and has standard part equal to its constant normal-form coefficient. -/
theorem mem_Icc_and_standardPart (hμ : IsStrongSurrealMeasure μ)
    (hpos : ∀ A, MeasurableSet A → 0 ≤ μ A) (hone : μ Set.univ = 1) {A : Set X}
    (hA : MeasurableSet A) :
    μ A ∈ Set.Icc 0 1 ∧ SignSequence.IsFinite (μ A) ∧
      SignSequence.standardPart (μ A) = (rawNormalForm (μ A)).coeff 0 := by
  have hP := hμ.isStrongHahnProbability hpos hone
  refine ⟨⟨hpos A hA, ?_⟩, isFinite_and_standardPart_eq_coeff_zero
    fun _ hg => hP.coeff_eq_zero_of_neg hA hg⟩
  rw [le_iff_toLex_rawNormalForm, rawNormalForm_one]
  exact hP.le_one hA

open Classical in
/-- `meas:cor:actual`, finite real shadow: the standard parts of the point masses of a positive
normalized actual strong measure on a countably separated space vanish outside a finite set
`F`, are positive on `F` and sum to `1`, and the standard part of every event mass is the sum
of the standard parts of its points in `F`. -/
theorem exists_finset_standardPart (hμ : IsStrongSurrealMeasure μ)
    (hX : IsCountablySeparated X) (hpos : ∀ A, MeasurableSet A → 0 ≤ μ A)
    (hone : μ Set.univ = 1) :
    ∃ F : Finset X, (∀ x, x ∈ F ↔ SignSequence.standardPart (μ {x}) ≠ 0) ∧
      (∀ x ∈ F, 0 < SignSequence.standardPart (μ {x})) ∧
      ∑ x ∈ F, SignSequence.standardPart (μ {x}) = 1 ∧
      ∀ A, MeasurableSet A → SignSequence.standardPart (μ A) =
        ∑ x ∈ F with x ∈ A, SignSequence.standardPart (μ {x}) := by
  have hst : ∀ A, MeasurableSet A →
      SignSequence.standardPart (μ A) = (rawNormalForm (μ A)).coeff 0 :=
    fun A hA => (hμ.mem_Icc_and_standardPart hpos hone hA).2.2
  have hsing : ∀ x : X, SignSequence.standardPart (μ {x}) = (rawNormalForm (μ {x})).coeff 0 :=
    fun x => hst _ (hX.measurableSet_singleton x)
  obtain ⟨F, h1, h2, h3, h4⟩ := (hμ.isStrongHahnProbability hpos hone).exists_finset_coeff_zero hX
  refine ⟨F, fun x => ?_, fun x hx => ?_, ?_, fun A hA => ?_⟩
  · rw [hsing]
    exact h1 x
  · rw [hsing]
    exact h2 x hx
  · simp only [hsing]
    exact h3
  · rw [hst A hA, h4 A hA]
    simp only [hsing]

open MeasureTheory in
/-- `meas:cor:actual`: the real standard part of a positive normalized actual strong measure
on a countably separated space is the ordinary probability measure `∑_{x ∈ F} st μ({x}) δ_x`
with finite point support and positive weights. -/
theorem exists_isProbabilityMeasure_standardPart (hμ : IsStrongSurrealMeasure μ)
    (hX : IsCountablySeparated X) (hpos : ∀ A, MeasurableSet A → 0 ≤ μ A)
    (hone : μ Set.univ = 1) :
    ∃ F : Finset X, (∀ x, x ∈ F ↔ SignSequence.standardPart (μ {x}) ≠ 0) ∧
      (∀ x ∈ F, 0 < SignSequence.standardPart (μ {x})) ∧
      IsProbabilityMeasure
        (∑ x ∈ F, ENNReal.ofReal (SignSequence.standardPart (μ {x})) • Measure.dirac x) ∧
      ∀ A, MeasurableSet A → SignSequence.standardPart (μ A) =
        (∑ x ∈ F, ENNReal.ofReal (SignSequence.standardPart (μ {x})) • Measure.dirac x).real
          A := by
  have hst : ∀ A, MeasurableSet A →
      SignSequence.standardPart (μ A) = (rawNormalForm (μ A)).coeff 0 :=
    fun A hA => (hμ.mem_Icc_and_standardPart hpos hone hA).2.2
  have hsing : ∀ x : X, SignSequence.standardPart (μ {x}) = (rawNormalForm (μ {x})).coeff 0 :=
    fun x => hst _ (hX.measurableSet_singleton x)
  obtain ⟨F, h1, h2, h3, h4⟩ :=
    (hμ.isStrongHahnProbability hpos hone).exists_isProbabilityMeasure hX
  refine ⟨F, fun x => ?_, fun x hx => ?_, ?_, fun A hA => ?_⟩
  · rw [hsing]
    exact h1 x
  · rw [hsing]
    exact h2 x hx
  · simp only [hsing]
    exact h3
  · rw [hst A hA, h4 A hA]
    simp only [hsing]

end Probability

end IsStrongSurrealMeasure

section Atomic

variable [Small.{u} X]

/-- The actual atomic set function `A ↦ ∑ˢ_{x ∈ A} w_x` of a strongly summable family indexed
by a set-sized space, defined on all subsets. -/
def atomicSurrealMeasure {w : X → SignSequence.{u}} (hw : SignSequence.StronglySummable w)
    (A : Set X) : SignSequence.{u} :=
  SignSequence.strongSum (fun x : A => w x.1) (hw.restrict A)

omit [MeasurableSpace X] in
/-- The canonical normal form of the actual atomic set function is the generic atomic set
function of the normal-form family. -/
theorem rawNormalForm_atomicSurrealMeasure {w : X → SignSequence.{u}}
    (hw : SignSequence.StronglySummable w) (A : Set X) :
    rawNormalForm (atomicSurrealMeasure hw A) = atomicMeasure hw.toHahnFamily A := by
  rw [atomicSurrealMeasure, rawNormalForm_strongSum, toHahnFamily_restrict]
  rfl

/-- The converse half of the actual atomic classification: the atomic set function of a
strongly summable family is an actual strong measure, for every measurable structure. -/
theorem isStrongSurrealMeasure_atomicSurrealMeasure {w : X → SignSequence.{u}}
    (hw : SignSequence.StronglySummable w) :
    IsStrongSurrealMeasure (atomicSurrealMeasure hw) := by
  rw [isStrongSurrealMeasure_iff]
  simp only [rawNormalForm_atomicSurrealMeasure]
  exact isStrongHahnMeasure_atomicMeasure _

/-- The actual atomic classification behind `meas:cor:actual`: on a countably separated
set-sized space, a set function is an actual strong measure exactly when it agrees on events
with the strong sums `A ↦ ∑ˢ_{x ∈ A} w_x` of some strongly summable family. -/
theorem isStrongSurrealMeasure_iff_exists (hX : IsCountablySeparated X) :
    IsStrongSurrealMeasure μ ↔ ∃ (w : X → SignSequence.{u})
      (hw : SignSequence.StronglySummable w),
      ∀ A, MeasurableSet A → μ A = atomicSurrealMeasure hw A := by
  constructor
  · intro hμ
    exact ⟨_, hμ.stronglySummable_singleton hX, fun A hA => hμ.eq_strongSum_singleton hX hA⟩
  · rintro ⟨w, hw, hμw⟩
    have hν := isStrongSurrealMeasure_iff.mp (isStrongSurrealMeasure_atomicSurrealMeasure
      (X := X) hw)
    rw [isStrongSurrealMeasure_iff]
    refine ⟨by simpa [hμw ∅ MeasurableSet.empty] using hν.empty, fun A hA hdisj => ?_⟩
    obtain ⟨s, hs, hsum⟩ := hν.iUnion A hA hdisj
    refine ⟨s, fun n => by rw [hs n, hμw _ (hA n)], ?_⟩
    show rawNormalForm (μ (⋃ n, A n)) = s.hsum
    rw [hμw _ (MeasurableSet.iUnion hA)]
    exact hsum

end Atomic

end Real

section Complex

variable {X : Type v} [MeasurableSpace X]

/-- `meas:cor:actual`: an `No[i]`-valued set function countably additive by canonical strong
normal-form sums. -/
structure IsStrongSurcomplexMeasure (μ : Set X → Surcomplex.{u}) : Prop where
  empty : μ ∅ = 0
  iUnion : ∀ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) →
    Pairwise (Function.onFun Disjoint A) →
    ∃ h : Surcomplex.StronglySummable (fun n => μ (A n)),
      μ (⋃ n, A n) = Surcomplex.strongSum (fun n => μ (A n)) h

variable {μ : Set X → Surcomplex.{u}}

/-- Actual complex strong additivity is exactly strong additivity of the canonical complex
normal forms, with exponents `Surreal.{u}ᵒᵈ` and complex coefficients. -/
theorem isStrongSurcomplexMeasure_iff :
    IsStrongSurcomplexMeasure μ ↔
      IsStrongHahnMeasure (fun A => Surcomplex.rawNormalForm (μ A)) := by
  constructor
  · intro hμ
    refine ⟨by simp [hμ.empty], fun A hA hdisj => ?_⟩
    obtain ⟨h, hsum⟩ := hμ.iUnion A hA hdisj
    refine ⟨h.toHahnFamily, fun n => rfl, ?_⟩
    show Surcomplex.rawNormalForm (μ (⋃ n, A n)) = h.toHahnFamily.hsum
    rw [hsum, Surcomplex.rawNormalForm_strongSum]
  · intro hμ
    refine ⟨Surcomplex.rawNormalForm_injective (by simpa using hμ.empty),
      fun A hA hdisj => ?_⟩
    obtain ⟨s, hs, hsum⟩ := hμ.iUnion A hA hdisj
    have h : Surcomplex.StronglySummable (fun n => μ (A n)) :=
      Surcomplex.stronglySummable_of_hahnFamily s hs
    refine ⟨h, Surcomplex.rawNormalForm_injective ?_⟩
    have hst : h.toHahnFamily = s := SummableFamily.ext fun n => (hs n).symm
    rw [Surcomplex.rawNormalForm_strongSum, hst]
    exact hsum

namespace IsStrongSurcomplexMeasure

/-- `meas:cor:actual`: the singleton masses of an actual complex strong measure on a countably
separated space are actually strongly summable. -/
theorem stronglySummable_singleton (hμ : IsStrongSurcomplexMeasure μ)
    (hX : IsCountablySeparated X) : Surcomplex.StronglySummable (fun x : X => μ {x}) :=
  Surcomplex.stronglySummable_of_hahnFamily
    (strongWeights (isStrongSurcomplexMeasure_iff.mp hμ) hX) fun _ => rfl

/-- The complex normal-form family of the singleton masses is the generic family of strong
weights of the normal-form measure. -/
theorem toHahnFamily_stronglySummable_singleton (hμ : IsStrongSurcomplexMeasure μ)
    (hX : IsCountablySeparated X) :
    (hμ.stronglySummable_singleton hX).toHahnFamily =
      strongWeights (isStrongSurcomplexMeasure_iff.mp hμ) hX :=
  SummableFamily.ext fun _ => rfl

/-- `meas:cor:actual`: on a countably separated set-sized space, every event mass of an actual
complex strong measure is the actual strong sum of its singleton masses. -/
theorem eq_strongSum_singleton [Small.{u} X] (hμ : IsStrongSurcomplexMeasure μ)
    (hX : IsCountablySeparated X) {A : Set X} (hA : MeasurableSet A) :
    μ A = Surcomplex.strongSum (fun x : A => μ {x.1})
      ((hμ.stronglySummable_singleton hX).restrict A) := by
  apply Surcomplex.rawNormalForm_injective
  rw [Surcomplex.rawNormalForm_strongSum,
    Surcomplex.toHahnFamily_restrict (hμ.stronglySummable_singleton hX) A,
    toHahnFamily_stronglySummable_singleton hμ hX]
  exact eq_atomicMeasure_strongWeights (isStrongSurcomplexMeasure_iff.mp hμ) hX hA

/-- `meas:cor:actual`, existential form: every event mass of an actual complex strong measure
is a strong sum of its singleton masses. -/
theorem exists_strongSum_singleton [Small.{u} X] (hμ : IsStrongSurcomplexMeasure μ)
    (hX : IsCountablySeparated X) {A : Set X} (hA : MeasurableSet A) :
    ∃ h : Surcomplex.StronglySummable (fun x : A => μ {x.1}),
      μ A = Surcomplex.strongSum (fun x : A => μ {x.1}) h :=
  ⟨_, hμ.eq_strongSum_singleton hX hA⟩

open Classical in
/-- `meas:cor:actual`: every complex normal-form coefficient is carried by finitely many
points. For each exponent `γ` there is a finite set `F_γ` whose points are exactly those whose
singleton mass has nonzero complex coefficient at `γ`, and the `γ`-coefficient of every event
mass is the sum of the coefficients of its points in `F_γ`. -/
theorem exists_finset_coeff (hμ : IsStrongSurcomplexMeasure μ) (hX : IsCountablySeparated X)
    (γ : _root_.Surreal.{u}ᵒᵈ) :
    ∃ F : Finset X, (∀ x, x ∈ F ↔ (Surcomplex.rawNormalForm (μ {x})).coeff γ ≠ 0) ∧
      ∀ A, MeasurableSet A → (Surcomplex.rawNormalForm (μ A)).coeff γ =
        ∑ x ∈ F with x ∈ A, (Surcomplex.rawNormalForm (μ {x})).coeff γ := by
  obtain ⟨F, hF, hrep⟩ := coeff_eq_finiteAtomic (isStrongSurcomplexMeasure_iff.mp hμ) hX γ
  refine ⟨F, fun x => ⟨hF x, fun hx => ?_⟩, fun A hA => ?_⟩
  · by_contra hxF
    exact hx (by rw [hrep _ (hX.measurableSet_singleton x), finiteAtomic_singleton,
      if_neg hxF])
  · rw [hrep A hA, finiteAtomic]

/-- `meas:cor:actual`: at each exponent only finitely many singleton masses have a nonzero
complex normal-form coefficient. -/
theorem finite_setOf_rawNormalForm_coeff_ne_zero (hμ : IsStrongSurcomplexMeasure μ)
    (hX : IsCountablySeparated X) (γ : _root_.Surreal.{u}ᵒᵈ) :
    {x | (Surcomplex.rawNormalForm (μ {x})).coeff γ ≠ 0}.Finite :=
  finite_setOf_singleton_coeff_ne_zero (isStrongSurcomplexMeasure_iff.mp hμ) hX γ

/-- `meas:cor:actual`: the union of the complex normal-form supports of all event masses is
well ordered. -/
theorem isWF_globalSupport (hμ : IsStrongSurcomplexMeasure μ) (hX : IsCountablySeparated X) :
    (globalSupport fun A => Surcomplex.rawNormalForm (μ A)).IsWF :=
  Surreal.HahnSeries.isWF_globalSupport
    (hasAtomicCoefficients_of_isStrongHahnMeasure (isStrongSurcomplexMeasure_iff.mp hμ) hX) hX

/-- `meas:cor:actual`: on a countably separated set-sized space the complex global support is
the union of the supports of the singleton masses, hence `u`-small. -/
theorem small_globalSupport [Small.{u} X] (hμ : IsStrongSurcomplexMeasure μ)
    (hX : IsCountablySeparated X) :
    Small.{u} (globalSupport fun A => Surcomplex.rawNormalForm (μ A)) := by
  rw [globalSupport_eq_iUnion
    (hasAtomicCoefficients_of_isStrongHahnMeasure (isStrongSurcomplexMeasure_iff.mp hμ) hX) hX]
  infer_instance

/-- `meas:cor:actual`: all event masses of an actual complex strong measure on a countably
separated set-sized space have a common admissible support, a `u`-small subset of
`Surreal.{u}ᵒᵈ` that is well ordered, that is reverse well ordered in `No`. -/
theorem exists_common_support [Small.{u} X] (hμ : IsStrongSurcomplexMeasure μ)
    (hX : IsCountablySeparated X) :
    ∃ S : Set _root_.Surreal.{u}ᵒᵈ, S.IsWF ∧ Small.{u} S ∧
      ∀ A, MeasurableSet A → (Surcomplex.rawNormalForm (μ A)).support ⊆ S :=
  ⟨_, hμ.isWF_globalSupport hX, hμ.small_globalSupport hX, fun A hA _ hγ => ⟨A, hA, hγ⟩⟩

end IsStrongSurcomplexMeasure

end Complex

end

end Surreal.ActualStrongMeasures
