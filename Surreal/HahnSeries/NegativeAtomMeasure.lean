import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Surreal.HahnSeries.NullIdealPositivity
import Surreal.Algebra.HerglotzHierarchy
import Surreal.HahnSeries.ModulusStandardPart

/-!
# The negative atom: signed representation, uniqueness and nonpositivity

This file proves the measure-theoretic clauses of `herg:thm:negativeatom` in
`docs/surcomplex/hahn-herglotz-positivity/article.tex`, and with them the pending
`M \ P` clause of `herg:thm:hierarchy` and the absence of a positive coefficientwise spectral
measure in `herg:cor:unitary`. The finite algebraic clauses of `herg:thm:negativeatom` are in
`Surreal.Algebra.HerglotzNegativeAtom` (over any field or ordered field) and
`Surreal.Algebra.HerglotzHierarchy` (strict Toeplitz positivity over `ℂ((t^Γ))`); here the
matrix and determinant formulas and strict Toeplitz positivity are restated for the same moment
sequence `negAtomMoments` in `ℂ((t^Γ))`, the positivity of the determinant is instantiated over
`ℝ((t^Γ))` at `ε = t^η`, and so are the algebraic clauses of `herg:cor:unitary` from
`Surreal.Algebra.HerglotzHierarchy`.

## Setting

The ordinary circle is `AddCircle T` for any `T > 0`; its point `x` is the point
`ζ = toCircle x = fourier 1 x` of the unit circle in `ℂ`, the point `0` is `ζ = 1`
(`toCircle_zero_eq_one`), and `ζ^{-n}` is `fourier (-n) x`. The Haar measure `m` is Mathlib's
normalized `haarAddCircle`. The Fourier moment of a finite measure is
`moment μ n = ∫ ζ^{-n} dμ`, and that of a finite signed measure is
`signedMoment s n = ∫ ζ^{-n} ds⁺ - ∫ ζ^{-n} ds⁻`. A signed coefficientwise Hahn measure
(`herg:def:measure`) is a well-ordered `W ⊆ Γ` with a family `ν : Γ → SignedMeasure`; its set
function is `Surreal.NullIdeal.coefSeries W hW ν`, with values in `ℝ((t^Γ))`, and its
coefficientwise Fourier moments are `coefMoment W hW ν n = ∑_{γ ∈ W} (∫ ζ^{-n} dν_γ) t^γ` in
`ℂ((t^Γ))`. Positivity means `0 ≤ μ(A)` in the lexicographic order for every Borel `A`.
The exponent set `Γ` is any linearly ordered type with a zero, and `ε = t^η` with `0 < η`;
the ring forms and the bridges to the finite clauses use an ordered abelian group `Γ`.

## Main results

* Fourier uniqueness on the circle: finite measures with equal Fourier coefficients are equal
  (`ext_of_moment_eq`, through Mathlib's point-separating subalgebra criterion applied to the
  Fourier subalgebra and its identification with the span of the characters), hence so are
  finite signed measures (`signedMeasure_ext`). Coefficientwise, two coefficientwise Hahn
  measures on the circle have equal moments exactly when their coefficient families agree
  (`coefMoment_eq_iff`), and then they define the same set function
  (`coefSeries_eq_of_coefMoment_eq`), with no restriction on the supports.
* `herg:thm:negativeatom`, with `c_0 = 1`, `c_n = -ε` (`negAtomMoments`): the signed
  coefficientwise measure `μ = m + t^η (m - δ_1) = (1 + ε) m - ε δ_1` (`negAtomFamily` on the
  support `{0, η}`, `herg:eq:badmeasure`: `coefSeries_negAtomFamily`,
  `coefSeries_negAtomFamily_eq`) has the moments `c_n` (`coefMoment_negAtomFamily`); every
  signed coefficientwise Hahn measure with these moments, on any well-ordered support, has the
  same coefficient family and set function (`coefMoment_eq_negAtomMoments_iff`,
  `coefSeries_eq_negAtom_of_coefMoment_eq`); `μ({1}) = -ε` (`m({1}) = 0`,
  `coefSeries_negAtomFamily_singleton`), so `μ` is not positive; and no positive
  coefficientwise Hahn measure has these moments (`not_exists_positive_representation`). The
  package is `negativeAtom`. For an ordered abelian group `Γ`, `T_N(c) = (1 + ε) I - ε J`,
  `det T_N(c) = (1 + ε)^N (1 - Nε)` (`toeplitz_negAtomMoments`) and `T_N(c) ≻ 0` against all
  vectors over `ℂ((t^Γ))` for every `N` (`toeplitz_negAtomMoments_pos`). The positivity
  `det T_N(c) > 0` of `herg:eq:det` is stated over `ℝ((t^Γ))`, with the same moments read in
  that ordered field (`det_toeplitz_negAtomMoments_pos`). The eigenvalue clause
  `herg:eq:eigen` is not restated here: it is `Surreal.Herglotz.toeplitz_negAtomMoment_mulVec_one`
  and `toeplitz_negAtomMoment_mulVec_of_sum_eq_zero` over any field, which apply to
  `negAtomMoments` through `negAtomMoments_eq_negAtomMoment`.
* `herg:thm:hierarchy`, `M \ P`: the witness moments in the form of
  `Surreal.HerglotzHierarchy.negAtomWitness_toeplitz_pos` are represented by the signed
  coefficientwise measure `μ` and have no positive representation
  (`hierarchyWitness_signed_not_positive`).
* `herg:cor:unitary`: no positive coefficientwise Hahn measure reproduces the vacuum moments
  `⟨Uⁿ 1, 1⟩ = c_n` of `U p = ζ p` on `V = K_Γ[ζ, ζ⁻¹]`, `K_Γ = ℝ((t^Γ))[i]`, transported
  along `ℂ((t^Γ)) ≃ ℝ((t^Γ))[i]` (`unitary_not_exists_positive_measure`). The package
  `unitary` adds the existence half at `F_Γ = ℝ((t^Γ))`, `ε = t^η`: the form
  `⟨p, q⟩ = Λ_ε(p̄ q)` is Hermitian and positive definite, `U` preserves it, `1` is cyclic, and
  the vacuum moments correspond to `negAtomMoments` (`complexHahnLexEquiv_negAtomMoments`).
* Bridge to measures on `ℂ` concentrated on the unit circle (`Surreal.Herglotz.circleMoment`):
  the image of a measure under `x ↦ ζ` has the same moments and is concentrated on `‖z‖ = 1`
  (`circleMoment_map_fourier_one`, `ae_norm_map_fourier_one`).

## Scope

The circle is modelled as `AddCircle T`. The bridge above transports moments to measures on
`ℂ`, but uniqueness is not re-proved for arbitrary measures on `ℂ` concentrated on the unit
circle. The classes `P, M, D, A, H` of `herg:thm:hierarchy` are not defined here, and the
spectral measures of `herg:cor:unitary` are not defined: the corollary is formalized as its
cyclic unitary system over `K_Γ` together with its stated reason, the absence of a positive
coefficientwise measure with the vacuum moments.
The weak-* convergence clauses of `herg:thm:quadrature` and `herg:thm:fejer` remain pending;
`negAtomFamily_not_positive` is the nonpositivity of their limit.
-/

namespace Surreal.NegativeAtomMeasure

open MeasureTheory AddCircle _root_.HahnSeries Surreal.NullIdeal
open scoped BoundedContinuousFunction

noncomputable section

section Fourier

variable {T : ℝ}

/-- The Fourier moment `∫ ζ^{-n} dμ` of a measure on the circle `AddCircle T`. -/
def moment (μ : Measure (AddCircle T)) (n : ℤ) : ℂ :=
  ∫ x, fourier (-n) x ∂μ

/-- The Fourier coefficients of the Dirac mass at `ζ = 1` are all `1`. -/
theorem moment_dirac_zero (n : ℤ) : moment (Measure.dirac (0 : AddCircle T)) n = 1 := by
  rw [moment, integral_dirac, fourier_eval_zero]

theorem moment_zero_measure (n : ℤ) : moment (0 : Measure (AddCircle T)) n = 0 :=
  integral_zero_measure _

variable [Fact (0 < T)]

theorem integrable_continuousMap (μ : Measure (AddCircle T)) [IsFiniteMeasure μ]
    (f : C(AddCircle T, ℂ)) : Integrable f μ :=
  (BoundedContinuousFunction.mkOfCompact f).integrable μ

/-- Finite measures with equal Fourier moments have equal integrals against every trigonometric
polynomial. -/
theorem integral_eq_of_mem_span {μ ν : Measure (AddCircle T)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ n, moment μ n = moment ν n) {f : C(AddCircle T, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (fourier (T := T)))) :
    ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨n, rfl⟩ := hg
    simpa [moment, neg_neg] using h (-n)
  | zero => simp
  | add f g _ _ hf hg =>
    simp only [ContinuousMap.add_apply]
    rw [integral_add (integrable_continuousMap μ f) (integrable_continuousMap μ g),
      integral_add (integrable_continuousMap ν f) (integrable_continuousMap ν g), hf, hg]
  | smul c f _ hf =>
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, hf]

/-- Fourier uniqueness on the circle (the ingredient of `herg:thm:negativeatom`): two finite
Borel measures on `AddCircle T` with the same Fourier coefficients are equal. The Fourier
subalgebra separates points, and its elements are trigonometric polynomials. -/
theorem ext_of_moment_eq {μ ν : Measure (AddCircle T)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ n, moment μ n = moment ν n) : μ = ν := by
  let A : StarSubalgebra ℂ (AddCircle T →ᵇ ℂ) :=
    fourierSubalgebra.comap (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    (A := A) ?_ ?_
  · intro x y hxy
    obtain ⟨_, ⟨f, hf, rfl⟩, hfxy⟩ := fourierSubalgebra_separatesPoints hxy
    exact ⟨_, ⟨_, ⟨BoundedContinuousFunction.mkOfCompact f, hf, rfl⟩, rfl⟩, hfxy⟩
  · intro g hg
    have hg' : (g : C(AddCircle T, ℂ)) ∈ Submodule.span ℂ (Set.range (fourier (T := T))) := by
      rw [← fourierSubalgebra_coe]
      exact hg
    exact integral_eq_of_mem_span h hg'

theorem moment_add (μ ν : Measure (AddCircle T)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (n : ℤ) : moment (μ + ν) n = moment μ n + moment ν n :=
  integral_add_measure (integrable_continuousMap μ _) (integrable_continuousMap ν _)

/-- The Fourier coefficients of Haar measure are `δ_{n0}`. -/
theorem moment_haarAddCircle (n : ℤ) :
    moment (haarAddCircle (T := T)) n = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) 0) n
  simp only [fourierCoeff, fourier_zero, smul_eq_mul, mul_one, Pi.single_apply] at h
  exact h

/-- Haar measure has no atoms: `m({x}) = 0`. -/
theorem haarAddCircle_singleton (x : AddCircle T) : haarAddCircle {x} = 0 := by
  have hT : ENNReal.ofReal T ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Fact.out : 0 < T)
  have h := AddCircle.volume_closedBall T (x := x) 0
  rw [Metric.closedBall_zero, mul_zero, min_eq_right (Fact.out : 0 < T).le,
    ENNReal.ofReal_zero, volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul,
    mul_eq_zero] at h
  exact h.resolve_left hT

/-- The Fourier moments `∫ ζ^{-n} ds = ∫ ζ^{-n} ds⁺ - ∫ ζ^{-n} ds⁻` of a finite signed measure. -/
def signedMoment (s : SignedMeasure (AddCircle T)) (n : ℤ) : ℂ :=
  moment s.toJordanDecomposition.posPart n - moment s.toJordanDecomposition.negPart n

/-- The signed moment may be computed from any decomposition `s = μ₁ - μ₂` into finite
measures, not only the Jordan decomposition. -/
theorem signedMoment_eq_of_eq_sub {s : SignedMeasure (AddCircle T)}
    {μ₁ μ₂ : Measure (AddCircle T)} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hs : s = μ₁.toSignedMeasure - μ₂.toSignedMeasure) (n : ℤ) :
    signedMoment s n = moment μ₁ n - moment μ₂ n := by
  have h1 : s.toJordanDecomposition.posPart.toSignedMeasure -
      s.toJordanDecomposition.negPart.toSignedMeasure =
        μ₁.toSignedMeasure - μ₂.toSignedMeasure := by
    rw [← hs]
    exact s.toSignedMeasure_toJordanDecomposition
  have h2 : s.toJordanDecomposition.posPart + μ₂ = μ₁ + s.toJordanDecomposition.negPart := by
    rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff, Measure.toSignedMeasure_add,
      Measure.toSignedMeasure_add, ← sub_eq_sub_iff_add_eq_add]
    exact h1
  have h3 := congrArg (fun m => moment m n) h2
  simp only [moment_add] at h3
  rw [signedMoment]
  linear_combination h3

theorem signedMoment_toSignedMeasure (μ : Measure (AddCircle T)) [IsFiniteMeasure μ]
    (n : ℤ) : signedMoment μ.toSignedMeasure n = moment μ n := by
  rw [signedMoment_eq_of_eq_sub (μ₁ := μ) (μ₂ := 0)
    (by rw [Measure.toSignedMeasure_zero, sub_zero]) n, moment_zero_measure, sub_zero]

theorem signedMoment_zero (n : ℤ) : signedMoment (0 : SignedMeasure (AddCircle T)) n = 0 := by
  rw [← Measure.toSignedMeasure_zero, signedMoment_toSignedMeasure, moment_zero_measure]

/-- Fourier uniqueness for finite signed measures on the circle: two finite signed measures
with the same Fourier coefficients are equal. -/
theorem signedMeasure_ext {s s' : SignedMeasure (AddCircle T)}
    (h : ∀ n, signedMoment s n = signedMoment s' n) : s = s' := by
  have hm : s.toJordanDecomposition.posPart + s'.toJordanDecomposition.negPart =
      s'.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart :=
    ext_of_moment_eq fun n => by
      rw [moment_add, moment_add]
      have := h n
      rw [signedMoment, signedMoment] at this
      linear_combination this
  rw [← s.toSignedMeasure_toJordanDecomposition, ← s'.toSignedMeasure_toJordanDecomposition,
    JordanDecomposition.toSignedMeasure, JordanDecomposition.toSignedMeasure,
    sub_eq_sub_iff_add_eq_add, ← Measure.toSignedMeasure_add, ← Measure.toSignedMeasure_add]
  exact Measure.toSignedMeasure_congr hm

end Fourier

section Coefficientwise

variable {T : ℝ} {Γ : Type*} [LinearOrder Γ]

open scoped Classical in
/-- The coefficientwise Fourier moment `∫ ζ^{-n} dμ = ∑_{γ ∈ W} (∫ ζ^{-n} dν_γ) t^γ` in
`ℂ((t^Γ))` of the coefficientwise Hahn measure `μ = ∑_{γ ∈ W} ν_γ t^γ` of `herg:def:measure`
(`coefSeries W hW ν`). The measures at exponents outside `W` are ignored. -/
def coefMoment (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure (AddCircle T)) (n : ℤ) :
    ℂ⟦Γ⟧ where
  coeff γ := if γ ∈ W then signedMoment (ν γ) n else 0
  isPWO_support' := hW.isPWO.mono fun γ hγ => by
    by_contra h
    exact hγ (if_neg h)

variable {W W' : Set Γ} {hW : W.IsWF} {hW' : W'.IsWF}
  {ν ν' : Γ → SignedMeasure (AddCircle T)}

open scoped Classical in
theorem coeff_coefMoment (n : ℤ) (γ : Γ) :
    (coefMoment W hW ν n).coeff γ = if γ ∈ W then signedMoment (ν γ) n else 0 :=
  rfl

open scoped Classical in
/-- The coefficient family of `μ`, with the measures outside the support replaced by `0`. -/
def coefFamily (W : Set Γ) (ν : Γ → SignedMeasure (AddCircle T)) (γ : Γ) :
    SignedMeasure (AddCircle T) :=
  if γ ∈ W then ν γ else 0

/-- The set function `coefSeries` depends only on the coefficient family. -/
theorem coefSeries_eq_of_coefFamily_eq (h : coefFamily W ν = coefFamily W' ν')
    (A : Set (AddCircle T)) : coefSeries W hW ν A = coefSeries W' hW' ν' A := by
  classical
  ext γ
  have := congrArg (fun s : SignedMeasure (AddCircle T) => s A) (congrFun h γ)
  simp only [coefFamily] at this
  rw [coeff_coefSeries, coeff_coefSeries]
  split_ifs at this ⊢ <;> simp_all

variable [Fact (0 < T)]

/-- Uniqueness of coefficientwise representations (`herg:thm:negativeatom`, the uniqueness
step): if two coefficientwise Hahn measures on the circle have the same coefficientwise Fourier
moments, then every coefficient measure of their difference has all Fourier coefficients zero,
so the two coefficient families agree. -/
theorem coefFamily_eq_of_coefMoment_eq (h : ∀ n, coefMoment W hW ν n = coefMoment W' hW' ν' n) :
    coefFamily W ν = coefFamily W' ν' := by
  classical
  funext γ
  refine signedMeasure_ext fun n => ?_
  have := congrArg (fun x : ℂ⟦Γ⟧ => x.coeff γ) (h n)
  simp only [coeff_coefMoment] at this
  simp only [coefFamily]
  split_ifs at this ⊢ <;> simp [signedMoment_zero, this]

/-- Conversely, the coefficientwise moments depend only on the coefficient family. -/
theorem coefMoment_eq_of_coefFamily_eq (h : coefFamily W ν = coefFamily W' ν') (n : ℤ) :
    coefMoment W hW ν n = coefMoment W' hW' ν' n := by
  classical
  ext γ
  have := congrArg (fun s => signedMoment s n) (congrFun h γ)
  simp only [coefFamily] at this
  rw [coeff_coefMoment, coeff_coefMoment]
  split_ifs at this ⊢ <;> simp_all [signedMoment_zero]

/-- Two coefficientwise Hahn measures on the circle have the same coefficientwise Fourier
moments exactly when they have the same coefficient families. -/
theorem coefMoment_eq_iff :
    (∀ n, coefMoment W hW ν n = coefMoment W' hW' ν' n) ↔ coefFamily W ν = coefFamily W' ν' :=
  ⟨coefFamily_eq_of_coefMoment_eq, fun h => coefMoment_eq_of_coefFamily_eq h⟩

/-- Coefficientwise Hahn measures on the circle with the same coefficientwise Fourier moments
define the same set function. -/
theorem coefSeries_eq_of_coefMoment_eq (h : ∀ n, coefMoment W hW ν n = coefMoment W' hW' ν' n)
    (A : Set (AddCircle T)) : coefSeries W hW ν A = coefSeries W' hW' ν' A :=
  coefSeries_eq_of_coefFamily_eq (coefFamily_eq_of_coefMoment_eq h) A

end Coefficientwise

section NegativeAtom

variable {T : ℝ} {Γ : Type*} [LinearOrder Γ] [Zero Γ] {η : Γ}

/-- `herg:eq:mainmoments` in `ℂ((t^Γ))`, with `ε = t^η`: `c_0 = 1` and `c_n = -t^η` for
`n ≠ 0`. -/
def negAtomMoments (η : Γ) (n : ℤ) : ℂ⟦Γ⟧ :=
  if n = 0 then 1 else -single η 1

/-- The two-exponent support `{0, η}` is well ordered. -/
theorem isWF_pair (η : Γ) : ({0, η} : Set Γ).IsWF :=
  (Set.toFinite _).isWF

/-- The point `0` of `AddCircle T` is the point `ζ = 1` of the unit circle. -/
theorem toCircle_zero_eq_one : (toCircle (0 : AddCircle T) : ℂ) = 1 := by
  rw [toCircle_zero, Circle.coe_one]

omit [Zero Γ] in
theorem toLex_neg_single_lt_zero (η : Γ) : toLex (-single η (1 : ℝ) : ℝ⟦Γ⟧) < 0 :=
  (_root_.HahnSeries.lt_iff _ _).mpr ⟨η, fun j hj => by simp [hj.ne], by simp⟩

theorem one_add_single_ne_zero (hη : 0 < η) : (1 + single η 1 : ℂ⟦Γ⟧) ≠ 0 := fun h => by
  have := congrArg (fun x : ℂ⟦Γ⟧ => x.coeff 0) h
  simp [hη.ne] at this

variable [Fact (0 < T)]

/-- `herg:eq:badmeasure`: the coefficient family of `μ = (1 + ε)m - εδ_1 = m + t^η (m - δ_1)`,
with `m` the normalized Haar measure and `δ_1` the Dirac mass at the point `0` of
`AddCircle T` (the point `ζ = 1`). The exponent-`0` coefficient is `m`; every other exponent
carries `m - δ_1`, but only `{0, η}` is used as support. -/
def negAtomFamily (γ : Γ) : SignedMeasure (AddCircle T) :=
  if γ = 0 then (haarAddCircle (T := T)).toSignedMeasure
  else (haarAddCircle (T := T)).toSignedMeasure - (Measure.dirac 0).toSignedMeasure

theorem signedMoment_negAtomFamily_zero (n : ℤ) :
    signedMoment (negAtomFamily (T := T) (0 : Γ)) n = if n = 0 then 1 else 0 := by
  rw [negAtomFamily, if_pos rfl, signedMoment_toSignedMeasure, moment_haarAddCircle]

theorem signedMoment_negAtomFamily_of_ne {γ : Γ} (hγ : γ ≠ 0) (n : ℤ) :
    signedMoment (negAtomFamily (T := T) γ) n = if n = 0 then 0 else -1 := by
  rw [negAtomFamily, if_neg hγ, signedMoment_eq_of_eq_sub rfl, moment_haarAddCircle,
    moment_dirac_zero]
  split_ifs <;> norm_num

/-- `herg:thm:negativeatom`, representation: the signed coefficientwise Hahn measure
`μ = m + t^η (m - δ_1)` has the Fourier moments `herg:eq:mainmoments`, because the moments of
`m` are `δ_{n0}` and those of `δ_1` are all `1`. -/
theorem coefMoment_negAtomFamily (hη : 0 < η) (n : ℤ) :
    coefMoment {0, η} (isWF_pair η) (negAtomFamily (T := T)) n = negAtomMoments η n := by
  ext γ
  rw [coeff_coefMoment, negAtomMoments]
  by_cases h0 : γ = 0
  · subst h0
    rw [if_pos (by simp), signedMoment_negAtomFamily_zero]
    split_ifs with hn <;> simp [hη.ne]
  · by_cases h1 : γ = η
    · subst h1
      rw [if_pos (by simp), signedMoment_negAtomFamily_of_ne h0]
      split_ifs with hn <;> simp [h0]
    · rw [if_neg (by simp [h0, h1])]
      split_ifs <;> simp [h0, h1]

/-- `herg:eq:badmeasure`: the set function of the negative-atom measure is
`μ(A) = m(A) + t^η (m(A) - δ_1(A))` on measurable sets. -/
theorem coefSeries_negAtomFamily (hη : 0 < η) {A : Set (AddCircle T)} (hA : MeasurableSet A) :
    coefSeries {0, η} (isWF_pair η) (negAtomFamily (T := T)) A =
      single 0 ((haarAddCircle (T := T)).real A) +
        single η ((haarAddCircle (T := T)).real A - (Measure.dirac (0 : AddCircle T)).real A) := by
  ext γ
  rw [coeff_coefSeries, coeff_add]
  by_cases h0 : γ = 0
  · subst h0
    simp [negAtomFamily, hη.ne, Measure.toSignedMeasure_apply_measurable hA]
  · by_cases h1 : γ = η
    · subst h1
      simp [negAtomFamily, h0, Measure.toSignedMeasure_apply_measurable hA]
    · simp [h0, h1]

/-- `herg:thm:negativeatom`: `μ({1}) = -ε`, since `m({1}) = 0`. -/
theorem coefSeries_negAtomFamily_singleton (hη : 0 < η) :
    coefSeries {0, η} (isWF_pair η) (negAtomFamily (T := T)) {0} = -single η 1 := by
  rw [coefSeries_negAtomFamily hη (measurableSet_singleton 0), measureReal_def,
    haarAddCircle_singleton, measureReal_def, Measure.dirac_apply_of_mem (Set.mem_singleton 0)]
  simp

/-- `herg:thm:negativeatom`: the negative-atom measure is not positive. -/
theorem negAtomFamily_not_positive (hη : 0 < η) :
    ¬ ∀ A, MeasurableSet A →
      0 ≤ toLex (coefSeries {0, η} (isWF_pair η) (negAtomFamily (T := T)) A) := fun h => by
  have := h {0} (measurableSet_singleton 0)
  rw [coefSeries_negAtomFamily_singleton hη] at this
  exact absurd this (not_le.mpr (toLex_neg_single_lt_zero η))

/-- `herg:thm:negativeatom`, uniqueness: a signed coefficientwise Hahn measure on the circle,
with any well-ordered support `W` and any finite signed coefficient measures, has the moments
`herg:eq:mainmoments` exactly when its coefficient family is that of
`μ = m + t^η (m - δ_1)`. -/
theorem coefMoment_eq_negAtomMoments_iff (hη : 0 < η) {W : Set Γ} (hW : W.IsWF)
    {ν : Γ → SignedMeasure (AddCircle T)} :
    (∀ n, coefMoment W hW ν n = negAtomMoments η n) ↔
      coefFamily W ν = coefFamily {0, η} negAtomFamily := by
  simp_rw [← coefMoment_negAtomFamily (T := T) hη]
  exact coefMoment_eq_iff

/-- `herg:thm:negativeatom`, uniqueness: every signed coefficientwise Hahn measure on the circle
with the moments `herg:eq:mainmoments` defines the same set function as
`μ = m + t^η (m - δ_1)`. -/
theorem coefSeries_eq_negAtom_of_coefMoment_eq (hη : 0 < η) {W : Set Γ} (hW : W.IsWF)
    {ν : Γ → SignedMeasure (AddCircle T)} (h : ∀ n, coefMoment W hW ν n = negAtomMoments η n)
    (A : Set (AddCircle T)) :
    coefSeries W hW ν A = coefSeries {0, η} (isWF_pair η) negAtomFamily A :=
  coefSeries_eq_of_coefFamily_eq ((coefMoment_eq_negAtomMoments_iff hη hW).mp h) A

/-- `herg:thm:negativeatom`, last clause: the moments `herg:eq:mainmoments` have no positive
coefficientwise Hahn-measure representation on the circle, whatever the well-ordered support. -/
theorem not_exists_positive_representation (hη : 0 < η) :
    ¬ ∃ (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure (AddCircle T)),
      (∀ n, coefMoment W hW ν n = negAtomMoments η n) ∧
        ∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries W hW ν A) := by
  rintro ⟨W, hW, ν, hmom, hpos⟩
  have h := hpos {0} (measurableSet_singleton 0)
  rw [coefSeries_eq_negAtom_of_coefMoment_eq hη hW hmom, coefSeries_negAtomFamily_singleton hη]
    at h
  exact absurd h (not_le.mpr (toLex_neg_single_lt_zero η))

/-- `herg:thm:negativeatom`, measure-theoretic clauses, for `ε = t^η` with `0 < η` in any
linearly ordered exponent set: the signed coefficientwise Hahn measure `μ = m + t^η (m - δ_1)`
has the moments `c_0 = 1`, `c_n = -ε`; every signed coefficientwise Hahn measure with these
moments defines the same set function; `μ({1}) = -ε`; and no positive coefficientwise Hahn
measure has these moments. -/
theorem negativeAtom (hη : 0 < η) :
    (∀ n, coefMoment {0, η} (isWF_pair η) (negAtomFamily (T := T)) n = negAtomMoments η n) ∧
    (∀ (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure (AddCircle T)),
      (∀ n, coefMoment W hW ν n = negAtomMoments η n) →
        ∀ A, coefSeries W hW ν A = coefSeries {0, η} (isWF_pair η) negAtomFamily A) ∧
    coefSeries {0, η} (isWF_pair η) (negAtomFamily (T := T)) {0} = -single η 1 ∧
    ¬ ∃ (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure (AddCircle T)),
      (∀ n, coefMoment W hW ν n = negAtomMoments η n) ∧
        ∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries W hW ν A) :=
  ⟨coefMoment_negAtomFamily hη, fun _ hW _ h => coefSeries_eq_negAtom_of_coefMoment_eq hη hW h,
    coefSeries_negAtomFamily_singleton hη, not_exists_positive_representation hη⟩

end NegativeAtom

section OrderedGroup

open Surreal.HahnSeries (complexHahnLexEquiv complexRealEmbedding
  complexHahnLexEquiv_complexRealEmbedding)

variable {T : ℝ} [Fact (0 < T)] {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] {η : Γ}

/-- Over an ordered abelian group of exponents, `negAtomMoments η` is the moment sequence
`Surreal.Herglotz.negAtomMoment ε` of `herg:eq:mainmoments` in the field `ℂ((t^Γ))`, at
`ε = t^η`; the finite Toeplitz clauses of `herg:thm:negativeatom` for it are proved in
`Surreal.Algebra.HerglotzNegativeAtom`. -/
theorem negAtomMoments_eq_negAtomMoment (η : Γ) (n : ℤ) :
    negAtomMoments η n = Herglotz.negAtomMoment (single η (1 : ℂ)) n :=
  rfl

/-- The moments of the `M \ P` witness of `herg:thm:hierarchy`, in the form used by
`Surreal.HerglotzHierarchy.negAtomWitness_toeplitz_pos`, are `herg:eq:mainmoments`. -/
theorem hierarchyWitness_eq (η : Γ) (k : ℤ) :
    C (if k = 0 then 1 else 0) + single η 1 * C ((if k = 0 then 0 else -1 : ℝ) : ℂ) =
      negAtomMoments η k := by
  by_cases hk : k = 0
  · simp [hk, negAtomMoments]
  · simp [hk, negAtomMoments]

/-- `herg:eq:mainmatrix` and the determinant formula of `herg:eq:det` for the moments in
`ℂ((t^Γ))`: `T_N(c) = (1 + ε) I - ε J` and `det T_N(c) = (1 + ε)^N (1 - Nε)`, with `ε = t^η`.
The positivity of the determinant is `det_toeplitz_negAtomMoments_pos`, over `ℝ((t^Γ))`. -/
theorem toeplitz_negAtomMoments (hη : 0 < η) (N : ℕ) :
    Herglotz.toeplitz N (negAtomMoments η) =
        (1 + single η (1 : ℂ)) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ⟦Γ⟧) -
          single η (1 : ℂ) • Herglotz.allOnes N ∧
      (Herglotz.toeplitz N (negAtomMoments η)).det =
        (1 + single η (1 : ℂ)) ^ N * (1 - (N : ℂ⟦Γ⟧) * single η 1) :=
  ⟨Herglotz.toeplitz_negAtomMoment N _,
    Herglotz.det_toeplitz_negAtomMoment N (one_add_single_ne_zero hη)⟩

/-- `herg:thm:negativeatom`, `herg:eq:mainmatrix`: for every ordinary `N`, `T_N(c)` is strictly
positive against all nonzero vectors over `ℂ((t^Γ))`, its Hermitian form being a positive
element of `ℝ((t^Γ))` (`Surreal.HerglotzHierarchy.negAtomWitness_toeplitz_pos`). -/
theorem toeplitz_negAtomMoments_pos (hη : 0 < η) (N : ℕ) {u : Fin (N + 1) → ℂ⟦Γ⟧}
    (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧
      Herglotz.complexHermForm (Herglotz.toeplitz N (negAtomMoments η)) u =
        complexRealEmbedding r := by
  have h := HerglotzHierarchy.negAtomWitness_toeplitz_pos hη N hu
  simp_rw [hierarchyWitness_eq] at h
  exact h

/-- `herg:eq:det`, positivity, at the model infinitesimal: over `F_Γ = ℝ((t^Γ))` with
`ε = t^η`, `det T_N(c) = (1 + ε)^N (1 - Nε)` is positive for every ordinary `N`. This is
`Surreal.Herglotz.det_toeplitz_negAtomMoment_pos`, whose hypothesis `Nε < 1` is
`Surreal.HerglotzHierarchy.natCast_mul_toLex_single_lt_one`; the moments are those of
`negAtomMoments η` read in `F_Γ` rather than in `ℂ((t^Γ))`. -/
theorem det_toeplitz_negAtomMoments_pos (hη : 0 < η) (N : ℕ) :
    0 < (Herglotz.toeplitz N (Herglotz.negAtomMoment (toLex (single η (1 : ℝ))))).det :=
  Herglotz.det_toeplitz_negAtomMoment_pos N (Herglotz.toLex_single_one_pos η).le
    (HerglotzHierarchy.natCast_mul_toLex_single_lt_one hη N)

/-- `herg:eq:badmeasure` in the ring `ℝ((t^Γ))`: `μ(A) = (1 + ε) m(A) - ε δ_1(A)` with
`ε = t^η`. -/
theorem coefSeries_negAtomFamily_eq (hη : 0 < η) {A : Set (AddCircle T)} (hA : MeasurableSet A) :
    coefSeries {0, η} (isWF_pair η) (negAtomFamily (T := T)) A =
      (1 + single η 1) * C ((haarAddCircle (T := T)).real A) -
        single η 1 * C ((Measure.dirac (0 : AddCircle T)).real A) := by
  rw [coefSeries_negAtomFamily hη hA, add_mul, one_mul, C_apply, C_apply, single_mul_single,
    single_mul_single, add_zero, one_mul, one_mul, single_sub, add_sub_assoc]

/-- `herg:thm:hierarchy`, the witness of `M \ P`: the moments `c_0 = 1`, `c_n = -t^η` are the
coefficientwise Fourier moments of the signed coefficientwise Hahn measure
`m + t^η (m - δ_1)` (and all their finite Toeplitz matrices are strictly positive by
`Surreal.HerglotzHierarchy.negAtomWitness_toeplitz_pos`), but they have no positive
coefficientwise Hahn-measure representation on the circle. -/
theorem hierarchyWitness_signed_not_positive (hη : 0 < η) :
    (∀ k, coefMoment {0, η} (isWF_pair η) (negAtomFamily (T := T)) k =
      C (if k = 0 then 1 else 0) + single η 1 * C ((if k = 0 then 0 else -1 : ℝ) : ℂ)) ∧
    ¬ ∃ (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure (AddCircle T)),
      (∀ k, coefMoment W hW ν k =
        C (if k = 0 then 1 else 0) + single η 1 * C ((if k = 0 then 0 else -1 : ℝ) : ℂ)) ∧
        ∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries W hW ν A) := by
  simp_rw [hierarchyWitness_eq]
  exact ⟨coefMoment_negAtomFamily hη, not_exists_positive_representation hη⟩

/-- The vacuum moments `⟨Uⁿ 1, 1⟩` of `herg:cor:unitary`, on `V = K_Γ[ζ, ζ⁻¹]` with
`K_Γ = F_Γ[i]`, `F_Γ = ℝ((t^Γ))` and `ε = t^η`, correspond to `herg:eq:mainmoments` under the
identification `ℂ((t^Γ)) ≃ F_Γ[i]`. -/
theorem complexHahnLexEquiv_negAtomMoments (η : Γ) (n : ℤ) :
    complexHahnLexEquiv (negAtomMoments η n) =
      HerglotzHierarchy.vacuumInner (toLex (single η (1 : ℝ)))
        ((HerglotzHierarchy.unitaryShift (Lex ℝ⟦Γ⟧) ^ n) 1) 1 := by
  rw [HerglotzHierarchy.vacuumInner_unitaryShift_zpow_one, Herglotz.negAtomMoment,
    negAtomMoments]
  split_ifs
  · simp
  · rw [map_neg, map_neg, ← Herglotz.complexRealEmbedding_single_one,
      complexHahnLexEquiv_complexRealEmbedding]

/-- `herg:cor:unitary`, the absence of the spectral measure: no positive coefficientwise Hahn
measure on the circle, with any well-ordered support, reproduces the vacuum moments
`⟨Uⁿ 1, 1⟩ = c_n` of the cyclic algebraic unitary `U p = ζ p` on `V = K_Γ[ζ, ζ⁻¹]`. -/
theorem unitary_not_exists_positive_measure (hη : 0 < η) :
    ¬ ∃ (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure (AddCircle T)),
      (∀ n : ℤ, complexHahnLexEquiv (coefMoment W hW ν n) =
        HerglotzHierarchy.vacuumInner (toLex (single η (1 : ℝ)))
          ((HerglotzHierarchy.unitaryShift (Lex ℝ⟦Γ⟧) ^ n) 1) 1) ∧
        ∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries W hW ν A) := by
  simp_rw [← complexHahnLexEquiv_negAtomMoments, EmbeddingLike.apply_eq_iff_eq]
  exact not_exists_positive_representation hη

open HerglotzHierarchy (vacuumInner unitaryShift) in
/-- `herg:cor:unitary` at `F_Γ = ℝ((t^Γ))`, `K_Γ = F_Γ[i]` and `ε = t^η` with `0 < η`. On
`V = K_Γ[ζ, ζ⁻¹]` the form `⟨p, q⟩ = Λ_ε(p̄ q)` is Hermitian and positive definite (`⟨p, p⟩`
is a positive element of `F_Γ` for every `p ≠ 0`), the unitary `U p = ζ p` preserves it, the
vector `1` is cyclic, the vacuum moments `⟨Uⁿ 1, 1⟩` are the moments `herg:eq:mainmoments`
transported along `ℂ((t^Γ)) ≃ K_Γ`, and no positive coefficientwise Hahn measure on the circle,
with any well-ordered support, reproduces them. Spectral measures are not defined: the last
clause is the absence of the positive coefficientwise measure that such a spectral measure
would be. -/
theorem unitary (hη : 0 < η) :
    (∀ p q : LaurentPolynomial (Complexify (Lex ℝ⟦Γ⟧)),
      vacuumInner (toLex (single η (1 : ℝ))) q p =
        star (vacuumInner (toLex (single η (1 : ℝ))) p q)) ∧
    (∀ p : LaurentPolynomial (Complexify (Lex ℝ⟦Γ⟧)), p ≠ 0 →
      ∃ r : Lex ℝ⟦Γ⟧, 0 < r ∧ vacuumInner (toLex (single η (1 : ℝ))) p p =
        algebraMap (Lex ℝ⟦Γ⟧) (Complexify (Lex ℝ⟦Γ⟧)) r) ∧
    (∀ p q : LaurentPolynomial (Complexify (Lex ℝ⟦Γ⟧)),
      vacuumInner (toLex (single η (1 : ℝ))) (unitaryShift (Lex ℝ⟦Γ⟧) p)
          (unitaryShift (Lex ℝ⟦Γ⟧) q) =
        vacuumInner (toLex (single η (1 : ℝ))) p q) ∧
    Submodule.span (Complexify (Lex ℝ⟦Γ⟧)) (Set.range fun n : ℤ =>
      (unitaryShift (Lex ℝ⟦Γ⟧) ^ n) (1 : LaurentPolynomial (Complexify (Lex ℝ⟦Γ⟧)))) = ⊤ ∧
    (∀ n : ℤ, complexHahnLexEquiv (negAtomMoments η n) =
      vacuumInner (toLex (single η (1 : ℝ))) ((unitaryShift (Lex ℝ⟦Γ⟧) ^ n) 1) 1) ∧
    ¬ ∃ (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure (AddCircle T)),
      (∀ n : ℤ, complexHahnLexEquiv (coefMoment W hW ν n) =
        vacuumInner (toLex (single η (1 : ℝ))) ((unitaryShift (Lex ℝ⟦Γ⟧) ^ n) 1) 1) ∧
        ∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries W hW ν A) :=
  ⟨fun p q => HerglotzHierarchy.vacuumInner_conj_symm _ p q,
    fun _ hp => HerglotzHierarchy.vacuumInner_self_pos_of_infinitesimal
      (Herglotz.toLex_single_one_pos η).le
      (HerglotzHierarchy.natCast_mul_toLex_single_lt_one hη) hp,
    HerglotzHierarchy.vacuumInner_unitaryShift _, HerglotzHierarchy.span_unitaryShift_orbit,
    complexHahnLexEquiv_negAtomMoments η, unitary_not_exists_positive_measure hη⟩

end OrderedGroup

section ComplexModel

variable {T : ℝ}

/-- Bridge to the model of circle measures as measures on `ℂ` concentrated on the unit circle
(`Surreal.Herglotz.circleMoment`): the image of a measure on `AddCircle T` under the
homeomorphism `x ↦ ζ = toCircle x = fourier 1 x` onto the unit circle has the same Fourier
moments. -/
theorem circleMoment_map_fourier_one (μ : Measure (AddCircle T)) (n : ℤ) :
    Herglotz.circleMoment (μ.map (fourier 1)) n = moment μ n := by
  have h := integral_map (μ := μ) (fourier (T := T) 1).continuous.aemeasurable
    (measurable_id.pow_const (-n)).aestronglyMeasurable
  refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
  simp only [fourier_apply, one_zsmul, toCircle_zsmul, Circle.coe_zpow, id]

/-- The image measure is concentrated on the unit circle. -/
theorem ae_norm_map_fourier_one (μ : Measure (AddCircle T)) :
    ∀ᵐ z ∂(μ.map (fourier (T := T) 1)), ‖z‖ = 1 :=
  (ae_map_iff (fourier (T := T) 1).continuous.aemeasurable
    (measurableSet_eq_fun measurable_norm measurable_const)).mpr
    (Filter.Eventually.of_forall fun _ => Circle.norm_coe _)

end ComplexModel

end

end Surreal.NegativeAtomMeasure
