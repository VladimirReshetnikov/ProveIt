import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Finsupp.Lex
import Mathlib.SetTheory.Ordinal.Basic
import Surreal.HahnSeries.NullIdealPositivity
import Surreal.HahnSeries.NegativeAtomMeasure
import Surreal.Algebra.HerglotzHierarchy
import Surreal.HahnSeries.HerglotzScalar
import Surreal.HahnSeries.Modulus

/-!
# Hahn–Herglotz normalization: common kernels, and the uncountable null-ideal example

This file formalizes, from `docs/surcomplex/hahn-herglotz-positivity/article.tex`, Example
`herg:ex:uncountable`; three parts of Theorem `herg:thm:normalization`, namely the common kernel
`herg:eq:commonkernel` (together with the equality of the kernels at all ordinary points), the
clause "positivity at ordinary points is equivalent to positivity throughout `U^#`", and the
finite algebraic fact of its proof; the first sentence of `herg:thm:harnack`; and the
divisibility counterexample of Section `herg:sec:framework`. The normal form of
`herg:thm:normalization`, the zero rows and columns of `H - iB` along `ker P` in its proof, and
its converse clause are not proved here (see Pending).

## `herg:ex:uncountable`

The generic setting is a measurable space `X` with a finite measure `m`, a well-ordered type `ι`
(the ordinals `α < κ`), a surjection `x : ι → X` (the enumeration `{x_α : α < κ}`), and a
strictly monotone `e : WithTop ι → Γ` into a linear order (the exponents `e_α` for `α ≤ κ`, with
`⊤ = κ`). `uncFamily` is the family `δ_{x_α}` (`α < κ`), `-m` (`α = κ`); `uncCoeff` places it on
`Γ`, and `uncMeasure x m he E = ∑_{α<κ} δ_{x_α}(E) t^{e_α} - m(E) t^{e_κ}` is the coefficientwise
Hahn measure `herg:eq:uncountable`, built with `Surreal.NullIdeal.coefSeries` on its well-ordered
support `range e` (`isWF_range`).

* `uncMeasure_leading`, `uncMeasure_pos`: on a nonempty measurable `E`, the least `α` with
  `x_α ∈ E` gives the leading term `1 · t^{e_α}`, so `μ(E) > 0`; `uncMeasure_nonneg`.
* `nullIdeal_uncCoeff_top`: `J_{<e_κ} = {∅}`, so the negative diffuse coefficient is harmless.
* `control_compl_range`, `measure_compl_range`, `not_negPart_absolutelyContinuous_control`: for
  every countable family `β` of indices below `κ` and all weights, the control measure
  `herg:eq:control` of the point masses `δ_{x_{β_j}}` vanishes on the complement `A` of the
  countable set `{x_{β_j}}`, while `m(A) = m(X)` when `m` vanishes on singletons (no point
  atoms, `NullSingletonClass m`). Hence, for `m ≠ 0`, the negative part `ν_κ⁻ = m`
  (`negPart_uncCoeff_top`) is not absolutely continuous with respect to it: the countable
  control-measure form `herg:eq:ACcriterion` would reject the positive `μ`.
* `not_countable_index`: under these hypotheses `κ` is necessarily uncountable.
* `UncGroup ι = Colex (WithTop ι →₀ ℚ)` is the group `Γ = ⊕_{α ≤ κ} ℚ e_α` ordered by the sign
  of the coefficient with the greatest index, an ordered abelian group
  (`uncGroup_isOrderedAddMonoid`), whose basis `uncBasis` has `0 < e_α < e_β` for `α < β`
  (`uncBasis_pos`, `uncBasis_strictMono`).
* `circleExample`: the example itself, on the circle `AddCircle T` with normalized Haar measure,
  well ordered by the initial ordinal `κ` of its cardinality (`circleEnum`), which is the
  continuum (`mk_addCircle`), with `Γ = UncGroup`; the complement of every countable set of
  points has Haar measure `1`.

## `herg:thm:normalization`

* The finite algebraic fact of its proof, valid without divisibility, over `F[i]` for any ordered
  field `F`: a Hermitian `A` with `Re(x* A x) ≥ 0` for all `x` and `Re(v* A v) = 0` has `A v = 0`
  (`mulVec_eq_zero_of_re_eq_zero`, by the source's choice `λ = -conj(b)/(d + 1)`). Hence
  `ker A = {v : Re(v* A v) = 0}` (`mulVec_eq_zero_iff_re_eq_zero`), and two such matrices whose
  quadratic forms vanish at the same vectors have the same kernel
  (`mulVec_eq_zero_iff_of_re_eq_zero_iff`). The same fact over `K_Γ = ℂ((t^Γ))`
  (`hahn_mulVec_eq_zero_iff`) is transported along `ℂ((t^Γ)) ≃ ℝ((t^Γ))[i]`.
* A matrix `H ∈ M_n(𝒪_Γ(U))` of coherent functions is a `Matrix n n (ℂ → ℂ)⟦Γ⟧` with coherent
  entries, in the model of `Surreal.HerglotzScalar`; its value is `H.map (evalAt a)` at an
  ordinary point `a` and `H.map (haloEval · z)` at a halo point `z`. `hahnReMat M = (M + M*)/2`
  is the real part, and `HahnPSD M` is `M ⪰ 0` tested against all vectors of `K_Γⁿ`.
  `halo_psd_and_ker_eq`: if `Re H(a) ⪰ 0` at every ordinary `a ∈ U` and `P = Re H(a₀)`, then
  `Re H(z) ⪰ 0` and `ker Re H(z) = ker P` at every `z ∈ U^#`. This is `herg:eq:commonkernel`
  and also the first sentence of `herg:thm:harnack`; `ker_hahnReMat_evalAt_eq` is its
  specialization to ordinary points. `hahnPSD_ordinary_iff_halo` is the clause "positivity at
  ordinary points is equivalent to positivity throughout `U^#`". As in the proof of
  `herg:thm:harnack`, each scalar function `u* H u` (`formFn`) is treated by `herg:lem:scalar`(b)
  and `herg:cor:scalarnormal` (`hahnRe_haloEval_nonneg_and_eq_zero_iff`), and the algebraic
  fact turns equal zero sets of quadratic forms into equal kernels.
* Divisibility (`herg:sec:framework`): if `2γ + η ≠ 0` for every `γ`, no `L ∈ ℂ((t^Γ))` has
  `conj(L) t^η L = 1` (`conj_mul_single_mul_ne_one`); `int_conj_mul_t_mul_ne_one` is the source's
  case `P = t` over `ℂ((t^ℤ))`.

## Generality

The halo results hold for every ordered abelian group `Γ`, with no divisibility and no
nonzeroness assumption, on a connected open `U` (Mathlib's `IsConnected` includes
nonemptiness). The algebraic fact holds over every ordered field. The example is proved for an
arbitrary well-ordered index type, measurable space and finite measure, and then instantiated.

## Pending

* `herg:thm:normalization`: the constant congruence `L ∈ GL_n(K_Γ)` with `L*(H - iB)L = G ⊕ 0`
  and `L* P L = I_r ⊕ 0` (`herg:eq:normalform`, which needs finite Hermitian congruence over the
  real closed field `F_Γ` for divisible `Γ`), the proof step that `H - iB` has zero rows and
  columns along `ker P`, the properties `herg:eq:normalizedG` of `G`, and the converse clause
  (the normal form defines a function with nonnegative real part on `U^#`).
* `herg:thm:harnack`: the Loewner inequalities `herg:eq:harnack` with ordinary constants (its
  failure clause is in `Surreal.Algebra.HerglotzHierarchy`).
* `herg:ex:uncountable`: the surreal exponent realization `e_α ↦ ω^α`, with
  `t^{e_α} ↦ ω^{-ω^α}`, is not formalized; the abstract group `Γ` is `UncGroup`. Regularity of
  the coefficient measures is not part of the model `Surreal.NullIdeal.coefSeries`.
-/

namespace Surreal.HerglotzNormalization

open MeasureTheory _root_.HahnSeries Surreal.NullIdeal
open scoped ENNReal

noncomputable section

section Uncountable

variable {X : Type*} [MeasurableSpace X]

theorem dirac_toSignedMeasure_of_mem {a : X} {E : Set X} (hE : MeasurableSet E) (h : a ∈ E) :
    (Measure.dirac a).toSignedMeasure E = 1 := by
  rw [Measure.toSignedMeasure_apply_measurable hE, measureReal_def,
    Measure.dirac_apply_of_mem h, ENNReal.toReal_one]

theorem dirac_toSignedMeasure_of_notMem {a : X} {E : Set X} (hE : MeasurableSet E)
    (h : a ∉ E) : (Measure.dirac a).toSignedMeasure E = 0 := by
  rw [Measure.toSignedMeasure_apply_measurable hE, measureReal_def,
    Measure.dirac_apply' a hE, Set.indicator_of_notMem h, ENNReal.toReal_zero]

/-- The negative Jordan part of `-m` is `m`. -/
theorem negPart_neg_toSignedMeasure (m : Measure X) [IsFiniteMeasure m] :
    (-m.toSignedMeasure).toJordanDecomposition.negPart = m := by
  let j : JordanDecomposition X :=
    { posPart := 0, negPart := m, mutuallySingular := Measure.MutuallySingular.zero_left }
  have hj : (-m.toSignedMeasure).toJordanDecomposition = j := by
    apply SignedMeasure.toJordanDecomposition_eq
    simp [j, JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_zero]
  rw [hj]

variable {ι : Type*}

/-- The coefficient measures of `herg:eq:uncountable`, indexed by the ordinals `α ≤ κ`, that is
by `WithTop ι` with `ι = {α : α < κ}` and `⊤ = κ`: the point mass `δ_{x_α}` for `α < κ` and
`-m` for `α = κ`. -/
def uncFamily (x : ι → X) (m : Measure X) [IsFiniteMeasure m] (a : WithTop ι) :
    SignedMeasure X :=
  WithTop.recTopCoe (-m.toSignedMeasure) (fun i => (Measure.dirac (x i)).toSignedMeasure) a

variable (x : ι → X) (m : Measure X) [IsFiniteMeasure m]

@[simp] theorem uncFamily_coe (i : ι) :
    uncFamily x m i = (Measure.dirac (x i)).toSignedMeasure := rfl

@[simp] theorem uncFamily_top : uncFamily x m ⊤ = -m.toSignedMeasure := rfl

omit [IsFiniteMeasure m] in
/-- `herg:ex:uncountable`: the index set `κ` of a surjective enumeration `{x_α : α < κ}` of a
space carrying a nonzero measure that vanishes on singletons (no point atoms) is uncountable. -/
theorem not_countable_index [NullSingletonClass m] (hm : m ≠ 0)
    (hx : Function.Surjective x) : ¬ Countable ι := by
  intro hι
  apply hm
  rw [← Measure.measure_univ_eq_zero, ← Set.range_eq_univ.mpr hx]
  exact (Set.countable_range x).measure_zero m

/-- `herg:ex:uncountable`: a measure that vanishes on singletons (no point atoms) gives full mass
to the complement of every countable set of points `A = {x_{β_j}}`, `m(X \ A) = m(X)`. -/
theorem measure_compl_range [MeasurableSingletonClass X] [NullSingletonClass m] {κ : Type*}
    [Countable κ] (β : κ → ι) : m (Set.range (x ∘ β))ᶜ = m Set.univ := by
  rw [measure_compl (Set.countable_range _).measurableSet (measure_ne_top _ _),
    (Set.countable_range _).measure_zero m, tsub_zero]

variable [LinearOrder ι] {Γ : Type*} [LinearOrder Γ] (e : WithTop ι → Γ)

/-- The coefficient family of `herg:eq:uncountable` on the exponent set `Γ`: the measure at
`e_α` is `uncFamily x m α`, and the measure at an exponent outside the range of `e` is zero. -/
def uncCoeff : Γ → SignedMeasure X := Function.extend e (uncFamily x m) 0

variable {e}

theorem uncCoeff_apply (he : StrictMono e) (a : WithTop ι) :
    uncCoeff x m e (e a) = uncFamily x m a :=
  he.injective.extend_apply _ _ a

/-- `herg:ex:uncountable`: the only Borel set null for all the earlier point masses is the empty
set, `J_{<e_κ} = {∅}`. -/
theorem nullIdeal_uncCoeff_top (he : StrictMono e) (hx : Function.Surjective x) :
    nullIdeal (Set.range e) (uncCoeff x m e) (e ⊤) = {∅} := by
  ext A
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hnull⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨i, rfl⟩ := hx y
    have h := hnull (e i) ⟨i, rfl⟩ (he (WithTop.coe_lt_top i))
    rw [uncCoeff_apply x m he, uncFamily_coe, totalVariation_toSignedMeasure,
      Measure.dirac_apply_of_mem hy] at h
    exact one_ne_zero h
  · rintro rfl
    exact empty_mem_nullIdeal

/-- The negative part of the last coefficient `ν_κ = -m` is `m`. -/
theorem negPart_uncCoeff_top (he : StrictMono e) :
    (uncCoeff x m e (e ⊤)).toJordanDecomposition.negPart = m := by
  rw [uncCoeff_apply x m he, uncFamily_top, negPart_neg_toSignedMeasure]

/-- `herg:ex:uncountable`: every control measure `herg:eq:control` built from countably many
earlier point masses vanishes on the complement of the countable set of their atoms. -/
theorem control_compl_range [MeasurableSingletonClass X] (he : StrictMono e) {κ : Type*}
    [Countable κ] (β : κ → ι) (w : κ → ℝ≥0∞) :
    NullIdeal.control (uncCoeff x m e) (fun k => e (β k)) w (Set.range (x ∘ β))ᶜ = 0 := by
  have hA : MeasurableSet (Set.range (x ∘ β))ᶜ :=
    (Set.countable_range _).measurableSet.compl
  rw [NullIdeal.control, Measure.sum_apply_eq_zero' hA]
  intro k
  rw [Measure.smul_apply, smul_eq_mul, uncCoeff_apply x m he, uncFamily_coe,
    totalVariation_toSignedMeasure, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem (show x (β k) ∉ (Set.range (x ∘ β))ᶜ from fun h => h ⟨k, rfl⟩),
    mul_zero]

/-- `herg:ex:uncountable`: no countable collection of earlier point masses controls `m`. Let
`m ≠ 0` vanish on singletons (no point atoms). For every countable family `β` of indices below
`κ` and all weights, the negative part `m` of the
last coefficient is not absolutely continuous with respect to the control measure
`herg:eq:control`, so the countable control-measure form `herg:eq:ACcriterion` of the condition
at `e_κ` fails, although `μ` is positive (`uncMeasure_nonneg`). -/
theorem not_negPart_absolutelyContinuous_control [MeasurableSingletonClass X]
    [NullSingletonClass m] (hm : m ≠ 0) (he : StrictMono e) {κ : Type*} [Countable κ]
    (β : κ → ι) (w : κ → ℝ≥0∞) :
    ¬ (uncCoeff x m e (e ⊤)).toJordanDecomposition.negPart ≪
      NullIdeal.control (uncCoeff x m e) (fun k => e (β k)) w := by
  intro hac
  rw [negPart_uncCoeff_top x m he] at hac
  have h0 := hac (control_compl_range x m he β w)
  rw [measure_compl_range x m β, Measure.measure_univ_eq_zero] at h0
  exact hm h0

variable [WellFoundedLT ι]

/-- The support `{e_α : α ≤ κ}` of `herg:eq:uncountable` is well ordered. -/
theorem isWF_range (he : StrictMono e) : (Set.range e).IsWF := by
  rw [← Set.image_univ]
  exact ((Set.IsWF.of_wellFoundedLT _).isPWO.image_of_monotone he.monotone).isWF

/-- `herg:eq:uncountable`: the coefficientwise Hahn measure
`μ(E) = ∑_{α<κ} δ_{x_α}(E) t^{e_α} - m(E) t^{e_κ}`. -/
def uncMeasure (he : StrictMono e) (E : Set X) : ℝ⟦Γ⟧ :=
  coefSeries (Set.range e) (isWF_range he) (uncCoeff x m e) E

theorem coeff_uncMeasure_coe (he : StrictMono e) (i : ι) (E : Set X) :
    (uncMeasure x m he E).coeff (e i) = (Measure.dirac (x i)).toSignedMeasure E := by
  rw [uncMeasure, coeff_coefSeries_of_mem _ (Set.mem_range_self _), uncCoeff_apply x m he,
    uncFamily_coe]

/-- `herg:ex:uncountable`, leading term: on a nonempty measurable set `E`, the least index `α`
with `x_α ∈ E` gives the leading term `1 · t^{e_α}` of `μ(E)`. -/
theorem uncMeasure_leading (he : StrictMono e) (hx : Function.Surjective x) {E : Set X}
    (hE : MeasurableSet E) (hne : E.Nonempty) :
    ∃ i : ι, x i ∈ E ∧ (∀ j, x j ∈ E → i ≤ j) ∧
      (∀ γ < e i, (uncMeasure x m he E).coeff γ = 0) ∧ (uncMeasure x m he E).coeff (e i) = 1 := by
  have hS : {j | x j ∈ E}.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨j, rfl⟩ := hx y
    exact ⟨j, hy⟩
  set i := wellFounded_lt.min {j | x j ∈ E} hS
  have hi : x i ∈ E := wellFounded_lt.min_mem {j | x j ∈ E} hS
  have hmin : ∀ j, x j ∈ E → i ≤ j := fun j hj =>
    not_lt.mp (wellFounded_lt.not_lt_min {j | x j ∈ E} hj)
  refine ⟨i, hi, hmin, fun γ hγ => ?_, ?_⟩
  · by_cases hγW : γ ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hγW
      have ha : a < (i : WithTop ι) := he.lt_iff_lt.mp hγ
      induction a using WithTop.recTopCoe with
      | top => exact absurd ha (not_lt_of_ge le_top)
      | coe j =>
        have hj : j < i := WithTop.coe_lt_coe.mp ha
        rw [coeff_uncMeasure_coe]
        exact dirac_toSignedMeasure_of_notMem hE fun hjE => not_le_of_gt hj (hmin j hjE)
    · rw [uncMeasure, coeff_coefSeries_of_notMem _ hγW]
  · rw [coeff_uncMeasure_coe]
    exact dirac_toSignedMeasure_of_mem hE hi

/-- `herg:ex:uncountable`: `μ` is strictly positive on every nonempty Borel set. -/
theorem uncMeasure_pos (he : StrictMono e) (hx : Function.Surjective x) {E : Set X}
    (hE : MeasurableSet E) (hne : E.Nonempty) : 0 < toLex (uncMeasure x m he E) := by
  obtain ⟨i, -, -, hbelow, hi⟩ := uncMeasure_leading x m he hx hE hne
  exact Surreal.HahnSeries.pos_of_coeff hbelow (by rw [hi]; exact one_pos)

theorem uncMeasure_empty (he : StrictMono e) : uncMeasure x m he ∅ = 0 := by
  ext γ
  rw [uncMeasure, coeff_coefSeries, coeff_zero]
  split_ifs <;> simp

/-- `herg:ex:uncountable`: `μ` is a positive coefficientwise Hahn measure. -/
theorem uncMeasure_nonneg (he : StrictMono e) (hx : Function.Surjective x) {E : Set X}
    (hE : MeasurableSet E) : 0 ≤ toLex (uncMeasure x m he E) := by
  rcases E.eq_empty_or_nonempty with rfl | hne
  · rw [uncMeasure_empty]
    exact le_rfl
  · exact (uncMeasure_pos x m he hx hE hne).le

end Uncountable

section Realization

variable (ι : Type*) [LinearOrder ι]

/-- The exponent group `Γ = ⊕_{α ≤ κ} ℚ e_α` of `herg:ex:uncountable`, with `α ≤ κ` ranging
over `WithTop ι`, ordered by the sign of the coefficient with the greatest index: this is the
colexicographic order on finitely supported functions. -/
abbrev UncGroup := Colex (WithTop ι →₀ ℚ)

/-- `Γ` is an ordered abelian group. -/
theorem uncGroup_isOrderedAddMonoid : IsOrderedAddMonoid (UncGroup ι) := inferInstance

variable {ι}

/-- The basis element `e_α` of `Γ`. -/
def uncBasis (a : WithTop ι) : UncGroup ι := toColex (Finsupp.single a 1)

/-- `e_α < e_β` for `α < β`. -/
theorem uncBasis_strictMono : StrictMono (uncBasis (ι := ι)) := fun a b hab =>
  Finsupp.Colex.lt_iff.mpr ⟨b, fun j hj => by
    simp [uncBasis, (hab.trans hj).ne, hj.ne],
    by simp [uncBasis, hab.ne]⟩

/-- `0 < e_α`. -/
theorem uncBasis_pos (a : WithTop ι) : 0 < uncBasis a :=
  Finsupp.Colex.lt_iff.mpr ⟨a, fun j hj => by simp [uncBasis, hj.ne],
    by simp [uncBasis]⟩

end Realization

section Circle

universe u

open AddCircle

variable (T : ℝ) [Fact (0 < T)]

/-- A well ordering `{x_α : α < κ}` of the circle `AddCircle T`, indexed by the initial ordinal
`κ` of its cardinality. -/
def circleEnum : (Cardinal.mk (AddCircle T)).ord.ToType ≃ AddCircle T :=
  Classical.choice (Cardinal.eq.mp (Cardinal.mk_ord_toType _))

/-- The circle `AddCircle T` has the cardinality of the continuum, so the index `κ` of
`circleEnum` is the initial ordinal of the continuum. -/
theorem mk_addCircle : Cardinal.mk (AddCircle T) = Cardinal.continuum := by
  rw [Cardinal.mk_congr (AddCircle.equivIco T 0),
    Cardinal.mk_Ico_real (by rw [zero_add]; exact Fact.out)]

theorem nullSingletonClass_haarAddCircle : NullSingletonClass (haarAddCircle (T := T)) :=
  ⟨Surreal.NegativeAtomMeasure.haarAddCircle_singleton⟩

/-- `herg:ex:uncountable` on the ordinary circle `AddCircle T` with normalized Haar measure `m`,
well ordered as `{x_α : α < κ}` by the initial ordinal `κ` of its cardinality, the continuum
(`mk_addCircle`), and the exponent group `Γ = ⊕_{α ≤ κ} ℚ e_α`. The measure
`μ = ∑_{α<κ} t^{e_α} δ_{x_α} - t^{e_κ} m` is strictly positive on every nonempty Borel set;
`J_{<e_κ} = {∅}`; `κ` is uncountable; and for every countable family of indices `β_j < κ`
(indexed by a countable type in any universe), the complement of the countable set
`{x_{β_j}}` has Haar measure `1` and is null for every control measure built from the point
masses `δ_{x_{β_j}}`, so `m = ν_κ⁻` is not absolutely continuous with respect to any of them. -/
theorem circleExample :
    (∀ E, MeasurableSet E → E.Nonempty →
      0 < toLex (uncMeasure (circleEnum T) haarAddCircle uncBasis_strictMono E)) ∧
    nullIdeal (Set.range uncBasis) (uncCoeff (circleEnum T) haarAddCircle uncBasis)
      (uncBasis ⊤) = {∅} ∧
    ¬ Countable (Cardinal.mk (AddCircle T)).ord.ToType ∧
    ∀ (κ : Type u) [Countable κ] (β : κ → (Cardinal.mk (AddCircle T)).ord.ToType)
      (w : κ → ℝ≥0∞),
      haarAddCircle (Set.range (circleEnum T ∘ β))ᶜ = 1 ∧
      NullIdeal.control (uncCoeff (circleEnum T) haarAddCircle uncBasis)
        (fun k => uncBasis (β k)) w (Set.range (circleEnum T ∘ β))ᶜ = 0 ∧
      ¬ (uncCoeff (circleEnum T) haarAddCircle uncBasis
          (uncBasis ⊤)).toJordanDecomposition.negPart ≪
        NullIdeal.control (uncCoeff (circleEnum T) haarAddCircle uncBasis)
          (fun k => uncBasis (β k)) w := by
  haveI := nullSingletonClass_haarAddCircle T
  have hm : (haarAddCircle : Measure (AddCircle T)) ≠ 0 := IsProbabilityMeasure.ne_zero _
  refine ⟨fun E hE hne => uncMeasure_pos _ _ _ (circleEnum T).surjective hE hne,
    nullIdeal_uncCoeff_top _ _ uncBasis_strictMono (circleEnum T).surjective,
    not_countable_index _ _ hm (circleEnum T).surjective, fun κ _ β w => ⟨?_,
    control_compl_range _ _ uncBasis_strictMono β w,
    not_negPart_absolutelyContinuous_control _ _ hm uncBasis_strictMono β w⟩⟩
  rw [measure_compl_range, measure_univ]

end Circle

section ZeroForm

open Matrix Surreal.Complexify Surreal.HerglotzHierarchy

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {n : Type*} [Fintype n]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem cHermForm_eq_dotProduct (A : Matrix n n (Complexify F)) (x : n → Complexify F) :
    cHermForm A x = star x ⬝ᵥ (A *ᵥ x) := by
  simp only [cHermForm, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- Expansion of the Hermitian form at `v + λ w`. -/
theorem dotProduct_add_smul (A : Matrix n n (Complexify F)) (v w : n → Complexify F)
    (l : Complexify F) :
    star (v + l • w) ⬝ᵥ (A *ᵥ (v + l • w)) = star v ⬝ᵥ (A *ᵥ v) + l * (star v ⬝ᵥ (A *ᵥ w)) +
      star l * (star w ⬝ᵥ (A *ᵥ v)) + star l * l * (star w ⬝ᵥ (A *ᵥ w)) := by
  rw [star_add, star_smul, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
    add_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- For Hermitian `A`, `w* A v = conj(v* A w)`. -/
theorem star_dotProduct_mulVec_swap {A : Matrix n n (Complexify F)} (hA : A.IsHermitian)
    (v w : n → Complexify F) : star w ⬝ᵥ (A *ᵥ v) = star (star v ⬝ᵥ (A *ᵥ w)) := by
  rw [star_dotProduct, star_mulVec, hA.eq, dotProduct_mulVec]

/-- Proof of `herg:thm:normalization`, the finite algebraic fact: over `F[i]`, with `F` any
ordered field, if `A` is Hermitian with `Re(x* A x) ≥ 0` for every vector `x` and
`Re(v* A v) = 0`, then `A v = 0`. For every `w`, with `b = v* A w` and `d = Re(w* A w)`, the
choice `λ = -conj(b)/(d + 1)` would give `Re((v + λw)* A (v + λw)) = -b conj(b) (d + 2)/(d + 1)²`,
negative unless `b = 0`. No square root is used. -/
theorem mulVec_eq_zero_of_re_eq_zero {A : Matrix n n (Complexify F)} (hA : A.IsHermitian)
    (hpsd : ∀ x, 0 ≤ (cHermForm A x).re) {v : n → Complexify F}
    (hv : (cHermForm A v).re = 0) : A *ᵥ v = 0 := by
  have hv' : (star v ⬝ᵥ (A *ᵥ v)).re = 0 := by rwa [cHermForm_eq_dotProduct] at hv
  have hb : ∀ w, star v ⬝ᵥ (A *ᵥ w) = 0 := by
    intro w
    by_contra hne
    have hN : 0 < normSq (star v ⬝ᵥ (A *ᵥ w)) := normSq_pos hne
    have hd : 0 ≤ (star w ⬝ᵥ (A *ᵥ w)).re := by
      have h := hpsd w
      rwa [cHermForm_eq_dotProduct] at h
    have key := hpsd (v + (-(algebraMap F (Complexify F) ((star w ⬝ᵥ (A *ᵥ w)).re + 1)⁻¹ *
      star (star v ⬝ᵥ (A *ᵥ w)))) • w)
    rw [cHermForm_eq_dotProduct, dotProduct_add_smul, star_dotProduct_mulVec_swap hA v w] at key
    generalize star v ⬝ᵥ (A *ᵥ w) = b at key hN
    generalize star w ⬝ᵥ (A *ᵥ w) = q at key hd
    generalize star v ⬝ᵥ (A *ᵥ v) = p at key hv'
    simp only [QuadraticAlgebra.re_add, mul_re, mul_im, conj_re, conj_im, QuadraticAlgebra.re_neg,
      QuadraticAlgebra.im_neg, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
      hv'] at key
    rw [normSq] at hN
    have hc : 0 < (q.re + 1)⁻¹ := inv_pos.mpr (by linarith)
    have hcd : (q.re + 1)⁻¹ * q.re < 1 := by
      have h1 : (q.re + 1)⁻¹ * (q.re + 1) = 1 := inv_mul_cancel₀ (by linarith)
      linarith
    have hneg : (q.re + 1)⁻¹ * (b.re ^ 2 + b.im ^ 2) * ((q.re + 1)⁻¹ * q.re - 2) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hc hN) (by linarith)
    nlinarith [hneg]
  have hvA : star v ᵥ* A = 0 := by
    classical
    funext i
    have h := hb (Pi.single i 1)
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at h
    exact h
  calc A *ᵥ v = star (star (A *ᵥ v)) := (star_star _).symm
    _ = 0 := by rw [star_mulVec, hA.eq, hvA, star_zero]

/-- For a Hermitian `A ⪰ 0` over `F[i]`, the kernel is exactly the zero set of the quadratic
form: `A v = 0 ↔ Re(v* A v) = 0`. -/
theorem mulVec_eq_zero_iff_re_eq_zero {A : Matrix n n (Complexify F)} (hA : A.IsHermitian)
    (hpsd : ∀ x, 0 ≤ (cHermForm A x).re) (v : n → Complexify F) :
    A *ᵥ v = 0 ↔ (cHermForm A v).re = 0 := by
  refine ⟨fun h => ?_, mulVec_eq_zero_of_re_eq_zero hA hpsd⟩
  rw [cHermForm_eq_dotProduct, h, dotProduct_zero, QuadraticAlgebra.re_zero]

/-- The algebraic core of the common-kernel clauses `herg:eq:commonkernel` and
`herg:thm:harnack`: if two Hermitian matrices `A, B ⪰ 0` over `F[i]` have quadratic forms
vanishing at the same vectors, then `ker A = ker B`. -/
theorem mulVec_eq_zero_iff_of_re_eq_zero_iff {A B : Matrix n n (Complexify F)}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hpA : ∀ x, 0 ≤ (cHermForm A x).re)
    (hpB : ∀ x, 0 ≤ (cHermForm B x).re)
    (h : ∀ v, (cHermForm A v).re = 0 ↔ (cHermForm B v).re = 0) (v : n → Complexify F) :
    A *ᵥ v = 0 ↔ B *ᵥ v = 0 := by
  rw [mulVec_eq_zero_iff_re_eq_zero hA hpA, mulVec_eq_zero_iff_re_eq_zero hB hpB, h]

end ZeroForm

section Divisibility

open Surreal.HahnSeries

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Why `herg:thm:normalization` assumes divisibility (Section `herg:sec:framework`): if `η` is
not of the form `-2γ`, then no `L ∈ ℂ((t^Γ))` satisfies `conj(L) t^η L = 1`, since the valuation
would give `2 v(L) + η = 0`. -/
theorem conj_mul_single_mul_ne_one {η : Γ} (hη : ∀ γ : Γ, γ + γ + η ≠ 0) (L : ℂ⟦Γ⟧) :
    complexConjugation L * single η (1 : ℂ) * L ≠ 1 := by
  intro h
  have hL : L ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact zero_ne_one h
  have hv := congrArg orderTop h
  rw [orderTop_mul, orderTop_mul, orderTop_complexConjugation, orderTop_single one_ne_zero,
    orderTop_one, ← order_eq_orderTop_of_ne_zero hL] at hv
  have hv' : L.order + η + L.order = 0 := by exact_mod_cast hv
  exact hη L.order (by rw [← hv']; abel)

/-- `herg:sec:framework`: over `ℂ((t^ℤ))` the positive scalar `P = t` admits no congruence
`conj(L) P L = 1`, since `2 v(L) + 1 = 0` has no solution in `ℤ`. -/
theorem int_conj_mul_t_mul_ne_one (L : ℂ⟦ℤ⟧) :
    complexConjugation L * single (1 : ℤ) (1 : ℂ) * L ≠ 1 :=
  conj_mul_single_mul_ne_one (fun γ => by omega) L

end Divisibility

section Halo

open Matrix Surreal.HahnSeries Surreal.HerglotzScalar Surreal.Herglotz Surreal.Complexify
  Surreal.HerglotzHierarchy

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] {n : Type*}
  [Fintype n]

/-- The real part `Re M = (M + M*)/2` of a square matrix over `K_Γ = ℂ((t^Γ))`. -/
def hahnReMat (M : Matrix n n ℂ⟦Γ⟧) : Matrix n n ℂ⟦Γ⟧ :=
  fun j k => C (2⁻¹ : ℂ) * (M j k + complexConjugation (M k j))

/-- `M ⪰ 0` tested against all vectors of `K_Γⁿ`, not only ordinary ones: `Re(u* M u) ≥ 0` in
`F_Γ = ℝ((t^Γ))` for every `u ∈ K_Γⁿ`. -/
def HahnPSD (M : Matrix n n ℂ⟦Γ⟧) : Prop :=
  ∀ u : n → ℂ⟦Γ⟧, 0 ≤ toLex (hahnRe (complexHermForm M u))

omit [Fintype n] in
/-- `Re M` is Hermitian. -/
theorem complexConjugation_hahnReMat (M : Matrix n n ℂ⟦Γ⟧) (j k : n) :
    complexConjugation (hahnReMat M j k) = hahnReMat M k j := by
  simp only [hahnReMat, map_mul, map_add, complexConjugation_complexConjugation, map_inv₀,
    map_ofNat, add_comm]

/-- `u* (Re M) u = Re(u* M u)`. -/
theorem complexHermForm_hahnReMat (M : Matrix n n ℂ⟦Γ⟧) (u : n → ℂ⟦Γ⟧) :
    complexHermForm (hahnReMat M) u = complexRealEmbedding (hahnRe (complexHermForm M u)) := by
  have hconj : complexConjugation (complexHermForm M u) =
      ∑ i, ∑ j, complexConjugation (u i) * complexConjugation (M j i) * u j := by
    simp only [complexHermForm, map_sum, map_mul, complexConjugation_complexConjugation]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsplit : complexHermForm (hahnReMat M) u =
      C (2⁻¹ : ℂ) * (complexHermForm M u + complexConjugation (complexHermForm M u)) := by
    rw [hconj]
    simp only [complexHermForm, hahnReMat, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  ext g
  rw [C_mul_eq_smul, coeff_smul, coeff_add, coeff_complexConjugation,
    coeff_complexRealEmbedding, coeff_hahnRe, smul_eq_mul]
  apply Complex.ext
  · simp
    ring
  · simp

theorem hahnRe_complexHermForm_hahnReMat (M : Matrix n n ℂ⟦Γ⟧) (u : n → ℂ⟦Γ⟧) :
    hahnRe (complexHermForm (hahnReMat M) u) = hahnRe (complexHermForm M u) := by
  rw [complexHermForm_hahnReMat]
  ext g
  simp

/-- `Re M ⪰ 0` exactly when `Re(u* M u) ≥ 0` for every `u ∈ K_Γⁿ`. -/
theorem hahnPSD_hahnReMat_iff (M : Matrix n n ℂ⟦Γ⟧) :
    HahnPSD (hahnReMat M) ↔ ∀ u, 0 ≤ toLex (hahnRe (complexHermForm M u)) := by
  simp only [HahnPSD, hahnRe_complexHermForm_hahnReMat]

theorem complexHahnLexEquiv_re (w : ℂ⟦Γ⟧) :
    (complexHahnLexEquiv w).re = toLex (hahnRe w) := rfl

theorem cHermForm_map_complexHahnLexEquiv (M : Matrix n n ℂ⟦Γ⟧) (u : n → ℂ⟦Γ⟧) :
    cHermForm (M.map complexHahnLexEquiv) (fun i => complexHahnLexEquiv (u i)) =
      complexHahnLexEquiv (complexHermForm M u) := by
  simp only [cHermForm, complexHermForm, map_sum, map_mul, Matrix.map_apply,
    complexHahnLexEquiv_conjugation]

/-- The finite algebraic fact of the proof of `herg:thm:normalization` over `K_Γ = ℂ((t^Γ))`,
transported from `F_Γ[i]` along `ℂ((t^Γ)) ≃ ℝ((t^Γ))[i]`: for a Hermitian `M ⪰ 0`,
`M u = 0 ↔ Re(u* M u) = 0`. -/
theorem hahn_mulVec_eq_zero_iff {M : Matrix n n ℂ⟦Γ⟧}
    (hM : ∀ j k, complexConjugation (M j k) = M k j) (hpsd : HahnPSD M) (u : n → ℂ⟦Γ⟧) :
    M *ᵥ u = 0 ↔ hahnRe (complexHermForm M u) = 0 := by
  set e : ℂ⟦Γ⟧ ≃+* Complexify (Lex ℝ⟦Γ⟧) := complexHahnLexEquiv
  have hA : (M.map e).IsHermitian := Matrix.ext fun j k => by
    rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hM k j]
    exact (complexHahnLexEquiv_conjugation (M k j)).symm
  have hpA : ∀ x, 0 ≤ (cHermForm (M.map e) x).re := by
    intro x
    have hx : x = fun i => e (e.symm (x i)) := by simp
    rw [hx, cHermForm_map_complexHahnLexEquiv, complexHahnLexEquiv_re]
    exact hpsd _
  have hmul : ∀ i, (M.map e *ᵥ fun i => e (u i)) i = e ((M *ᵥ u) i) := by
    intro i
    simp only [mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hiff := mulVec_eq_zero_iff_re_eq_zero hA hpA (fun i => e (u i))
  rw [cHermForm_map_complexHahnLexEquiv, complexHahnLexEquiv_re, toLex_eq_zero] at hiff
  rw [← hiff]
  constructor
  · intro h
    funext i
    rw [hmul, h, Pi.zero_apply, map_zero, Pi.zero_apply]
  · intro h
    funext i
    have hi := congrFun h i
    rw [hmul, Pi.zero_apply, map_eq_zero_iff e e.injective] at hi
    exact hi

variable {U : Set ℂ}

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem isCoherentOn_add [AddCommMonoid Γ] {f g : (ℂ → ℂ)⟦Γ⟧} (hf : IsCoherentOn U f)
    (hg : IsCoherentOn U g) : IsCoherentOn U (f + g) := fun γ => by
  rw [coeff_add]
  exact (hf γ).add (hg γ)

theorem isCoherentOn_sum {ι : Type*} (s : Finset ι) {f : ι → (ℂ → ℂ)⟦Γ⟧}
    (hf : ∀ i, IsCoherentOn U (f i)) : IsCoherentOn U (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, ← map_zero (constSeries (Γ := Γ))]
    exact isCoherentOn_constSeries 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isCoherentOn_add (hf a) ih

/-- Taylor evaluation at a point of `U` is additive on finite sums of coherent functions. -/
theorem taylorEval_sum (hU : IsOpen U) {ι : Type*} (s : Finset ι) {f : ι → (ℂ → ℂ)⟦Γ⟧}
    (hf : ∀ i, IsCoherentOn U (f i)) {a : ℂ} (ha : a ∈ U) (η : ℂ⟦Γ⟧) :
    taylorEval (∑ i ∈ s, f i) a η = ∑ i ∈ s, taylorEval (f i) a η := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ← map_zero (constSeries (Γ := Γ)),
      taylorEval_constSeries]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, ← ih]
    have h := taylorEval_sub hU (isCoherentOn_add (hf b) (isCoherentOn_sum s hf))
      (isCoherentOn_sum s hf) ha η
    rw [add_sub_cancel_right] at h
    rw [h, sub_add_cancel]

/-- The scalar coherent function `u* H u` of a constant vector `u ∈ K_Γⁿ`. -/
def formFn (H : Matrix n n (ℂ → ℂ)⟦Γ⟧) (u : n → ℂ⟦Γ⟧) : (ℂ → ℂ)⟦Γ⟧ :=
  ∑ i, ∑ j, constSeries (complexConjugation (u i)) * H i j * constSeries (u j)

variable {H : Matrix n n (ℂ → ℂ)⟦Γ⟧}

theorem isCoherentOn_formFn (hH : ∀ i j, IsCoherentOn U (H i j)) (u : n → ℂ⟦Γ⟧) :
    IsCoherentOn U (formFn H u) :=
  isCoherentOn_sum _ fun i => isCoherentOn_sum _ fun j =>
    ((isCoherentOn_constSeries _).mul (hH i j)).mul (isCoherentOn_constSeries _)

theorem evalAt_formFn (a : ℂ) (u : n → ℂ⟦Γ⟧) :
    evalAt a (formFn H u) = complexHermForm (H.map (evalAt a)) u := by
  simp only [formFn, complexHermForm, map_sum, map_mul, evalAt_constSeries, Matrix.map_apply]

/-- At a halo point, `(u* H u)(z) = u* H(z) u`. -/
theorem haloEval_formFn (hU : IsOpen U) (hH : ∀ i j, IsCoherentOn U (H i j))
    {z : ℂ⟦Γ⟧} (hz : z ∈ hahnHalo U) (u : n → ℂ⟦Γ⟧) :
    haloEval (formFn H u) z = complexHermForm (H.map fun f => haloEval f z) u := by
  obtain ⟨a, ha, η, hη, rfl⟩ := hz
  have hfn : ∀ i, IsCoherentOn U
      (∑ j, constSeries (complexConjugation (u i)) * H i j * constSeries (u j)) := fun i =>
    isCoherentOn_sum _ fun j =>
      ((isCoherentOn_constSeries _).mul (hH i j)).mul (isCoherentOn_constSeries _)
  rw [haloEval_C_add _ a hη, formFn, taylorEval_sum hU _ hfn ha, complexHermForm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [taylorEval_sum hU _ (fun j => ((isCoherentOn_constSeries _).mul (hH i j)).mul
    (isCoherentOn_constSeries _)) ha]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show constSeries (complexConjugation (u i)) * H i j * constSeries (u j) =
      H i j * constSeries (complexConjugation (u i)) * constSeries (u j) by ring,
    taylorEval_mul_constSeries hU ((hH i j).mul (isCoherentOn_constSeries _)) ha,
    taylorEval_mul_constSeries hU (hH i j) ha, Matrix.map_apply, haloEval_C_add _ a hη]
  ring

/-- Halo evaluation at an ordinary point is ordinary evaluation. -/
theorem haloEval_C (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) : haloEval f (C a) = evalAt a f := by
  have h := haloEval_C_add f a (η := 0) (by rw [orderTop_zero]; exact WithTop.coe_lt_top 0)
  rw [add_zero] at h
  rw [h, taylorEval_zero]

omit [Fintype n] in
theorem map_haloEval_C (a : ℂ) : (H.map fun f => haloEval f (C a)) = H.map (evalAt a) := by
  ext i j
  simp only [Matrix.map_apply, haloEval_C]

/-- Every ordinary point of `U` is a halo point. -/
theorem C_mem_hahnHalo {a : ℂ} (ha : a ∈ U) : (C a : ℂ⟦Γ⟧) ∈ hahnHalo U :=
  ⟨a, ha, 0, by rw [orderTop_zero]; exact WithTop.coe_lt_top 0, add_zero _⟩

/-- The scalar step of `herg:thm:harnack`: for a coherent `f` with `Re f ≥ 0` at the ordinary
points of `U`, at every halo point `Re f(z) ≥ 0`, and `Re f(z) = 0` exactly when
`Re f(a₀) = 0`. If `Re f(a₀) = 0`, `f` is a constant in `i F_Γ` (`herg:lem:scalar`(b)); otherwise
the scalar normalization gives `Re f(z) > 0` (`herg:cor:scalarnormal`). -/
theorem hahnRe_haloEval_nonneg_and_eq_zero_iff (hU : IsOpen U) (hc : IsConnected U)
    {f : (ℂ → ℂ)⟦Γ⟧} (hf : IsCoherentOn U f) (hpos : HasNonnegReOn U f) {a₀ : ℂ}
    (ha₀ : a₀ ∈ U) {z : ℂ⟦Γ⟧} (hz : z ∈ hahnHalo U) :
    0 ≤ toLex (hahnRe (haloEval f z)) ∧
      (hahnRe (haloEval f z) = 0 ↔ hahnRe (evalAt a₀ f) = 0) := by
  by_cases h0 : hahnRe (evalAt a₀ f) = 0
  · obtain ⟨c, hcf⟩ := isImagConstOn_of_hahnRe_eq_zero hU hc hf hpos ha₀ h0
    have hconst : haloEval f z = C Complex.I * complexRealEmbedding c := by
      rw [haloEval_congr hU (f' := constSeries (C Complex.I * complexRealEmbedding c))
        (fun γ b hb => ?_) hz]
      · obtain ⟨a, ha, η, hη, rfl⟩ := hz
        rw [haloEval_C_add _ a hη, taylorEval_constSeries]
      · rw [coeff_constSeries, hcf γ b hb, C_mul_eq_smul, coeff_smul,
          coeff_complexRealEmbedding, smul_eq_mul, mul_comm]
    have hre : hahnRe (haloEval f z) = 0 := by
      ext γ
      rw [hconst, coeff_hahnRe, C_mul_eq_smul, coeff_smul, coeff_complexRealEmbedding,
        smul_eq_mul]
      simp
    refine ⟨by rw [hre]; exact le_rfl, iff_of_true hre h0⟩
  · have hρ : 0 < toLex (hahnRe (evalAt a₀ f)) :=
      (hpos a₀ ha₀).lt_of_ne fun h => h0 (toLex_eq_zero.mp h.symm)
    obtain ⟨-, -, hg⟩ := scalarNormalization_halo hU hc hf hpos ha₀ hρ hz
    rw [haloEval_scalarNormalize hU hf hz, hahnRe_mul_complexRealEmbedding,
      hahnRe_sub_imagConst] at hg
    change 0 < toLex (hahnRe (haloEval f z)) * (toLex (hahnRe (evalAt a₀ f)))⁻¹ at hg
    have hz' : 0 < toLex (hahnRe (haloEval f z)) :=
      (mul_pos_iff_of_pos_right (inv_pos.mpr hρ)).mp hg
    exact ⟨hz'.le, iff_of_false (fun h => by rw [h] at hz'; exact lt_irrefl _ hz') h0⟩

/-- `herg:thm:harnack`, first sentence, and the common kernel `herg:eq:commonkernel` of
`herg:thm:normalization`, for any ordered abelian group `Γ` (no divisibility): let
`H ∈ M_n(𝒪_Γ(U))` on a connected open `U` satisfy `Re H(a) ⪰ 0` at every ordinary `a ∈ U`, and
put `P = Re H(a₀)`. Then at every halo point `z ∈ U^#`, `Re H(z) ⪰ 0` and
`ker Re H(z) = ker P`. -/
theorem halo_psd_and_ker_eq (hU : IsOpen U) (hc : IsConnected U)
    (hH : ∀ i j, IsCoherentOn U (H i j))
    (hpos : ∀ a ∈ U, HahnPSD (hahnReMat (H.map (evalAt a)))) {a₀ : ℂ} (ha₀ : a₀ ∈ U)
    {z : ℂ⟦Γ⟧} (hz : z ∈ hahnHalo U) :
    HahnPSD (hahnReMat (H.map fun f => haloEval f z)) ∧
      ∀ u, hahnReMat (H.map fun f => haloEval f z) *ᵥ u = 0 ↔
        hahnReMat (H.map (evalAt a₀)) *ᵥ u = 0 := by
  have hf : ∀ u, HasNonnegReOn U (formFn H u) := fun u a ha => by
    rw [evalAt_formFn]
    exact (hahnPSD_hahnReMat_iff _).mp (hpos a ha) u
  have hstep := fun u => hahnRe_haloEval_nonneg_and_eq_zero_iff hU hc
    (isCoherentOn_formFn hH u) (hf u) ha₀ hz
  have hpsdz : HahnPSD (hahnReMat (H.map fun f => haloEval f z)) := by
    rw [hahnPSD_hahnReMat_iff]
    intro u
    rw [← haloEval_formFn hU hH hz]
    exact (hstep u).1
  refine ⟨hpsdz, fun u => ?_⟩
  rw [hahn_mulVec_eq_zero_iff (complexConjugation_hahnReMat _) hpsdz,
    hahn_mulVec_eq_zero_iff (complexConjugation_hahnReMat _) (hpos a₀ ha₀),
    hahnRe_complexHermForm_hahnReMat, hahnRe_complexHermForm_hahnReMat,
    ← haloEval_formFn hU hH hz, ← evalAt_formFn]
  exact (hstep u).2

/-- Proof of `herg:thm:normalization`: the kernels `ker Re H(a)` at the ordinary points
`a ∈ U` are all equal to `W = ker P`. -/
theorem ker_hahnReMat_evalAt_eq (hU : IsOpen U) (hc : IsConnected U)
    (hH : ∀ i j, IsCoherentOn U (H i j))
    (hpos : ∀ a ∈ U, HahnPSD (hahnReMat (H.map (evalAt a)))) {a₀ a : ℂ} (ha₀ : a₀ ∈ U)
    (ha : a ∈ U) (u : n → ℂ⟦Γ⟧) :
    hahnReMat (H.map (evalAt a)) *ᵥ u = 0 ↔ hahnReMat (H.map (evalAt a₀)) *ᵥ u = 0 := by
  have h := (halo_psd_and_ker_eq hU hc hH hpos ha₀ (C_mem_hahnHalo ha)).2 u
  rwa [map_haloEval_C] at h

/-- `herg:thm:normalization`, "positivity at ordinary points is equivalent to positivity
throughout `U^#`": for coherent `H` on a connected open `U`, `Re H(a) ⪰ 0` at every ordinary
`a ∈ U` exactly when `Re H(z) ⪰ 0` at every `z ∈ U^#`. -/
theorem hahnPSD_ordinary_iff_halo (hU : IsOpen U) (hc : IsConnected U)
    (hH : ∀ i j, IsCoherentOn U (H i j)) :
    (∀ a ∈ U, HahnPSD (hahnReMat (H.map (evalAt a)))) ↔
      ∀ z ∈ hahnHalo U, HahnPSD (hahnReMat (H.map fun f => haloEval f z)) := by
  constructor
  · intro hpos z hz
    obtain ⟨a₀, ha₀⟩ := hc.nonempty
    exact (halo_psd_and_ker_eq hU hc hH hpos ha₀ hz).1
  · intro h a ha
    rw [← map_haloEval_C]
    exact h _ (C_mem_hahnHalo ha)

end Halo

end

end Surreal.HerglotzNormalization
