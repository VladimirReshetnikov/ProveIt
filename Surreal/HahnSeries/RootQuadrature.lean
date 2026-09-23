import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.RingTheory.RootsOfUnity.Complex
import Surreal.HahnSeries.NegativeAtomMeasure

/-!
# Positive root-of-unity quadratures with a nonpositive weak-* limit

This file proves `herg:thm:quadrature` (with `herg:eq:quadrature`) of
`docs/surcomplex/hahn-herglotz-positivity/article.tex`: the positive coefficientwise Hahn
probability measures `μ_M = (1 + ε) σ_M - ε δ_1` built from the root-of-unity quadratures `σ_M`
converge coefficientwise weak-* to the nonpositive measure `(1 + ε) m - ε δ_1` of
`herg:thm:negativeatom`, so the positive coefficientwise Hahn-probability cone is not closed.
The finite algebraic clauses (positive weights, total mass one, moments `-ε` for `0 < n < M`)
are `Surreal.Herglotz.quadratureWeight_pos`, `sum_quadratureWeight` and `quadrature_moment` in
`Surreal.Algebra.HerglotzNegativeAtom`; here the measures themselves are constructed.

## Setting

As in `Surreal.HahnSeries.NegativeAtomMeasure`, the ordinary circle is `AddCircle T` for any
`T > 0`, its point `x` is `ζ = toCircle x`, the point `0` is `ζ = 1`, `m` is the normalized
`haarAddCircle`, and `δ_1` is the Dirac mass at `0`. The point `rootPoint M j = j T / M` is
the root of unity `ζ_M^j`, `ζ_M = e^{2π i / M}` (`fourier_rootPoint`), and
`σ_M = rootMeasure M = M⁻¹ ∑_{j < M} δ_{ζ_M^j}` is the uniform probability measure on the
`M`th roots of unity (`toCircle_rootPoint_pow`, `rootPoint_injOn`, `exists_rootPoint_eq`).
With `ε = t^η`, `0 < η`, in any linearly ordered exponent set with a zero,
`μ_M = σ_M + t^η (σ_M - δ_1)` is the coefficientwise Hahn measure `quadFamily M` on the fixed
support `{0, η}` (`herg:eq:quadrature`). For an ordered abelian group of exponents, its ring
form `(1 + ε) σ_M(A) - ε δ_1(A)` (`coefSeries_quadFamily_eq`) and its atomic form
`∑_j w_j δ_{ζ_M^j}(A)`, with the weights `w_j = quadratureWeight M ε j` of the finite clauses
(`coefSeries_quadFamily_eq_sum`), are proved as well; at `ε = t^η` these weights are positive
in the ordered field `Lex ℝ((t^Γ))` (`toLex_quadratureWeight_single_pos`). The integral of a
continuous `f` against a finite signed measure is `∫ f ds⁺ - ∫ f ds⁻` (`signedIntegral`), the
coefficientwise integral of `herg:def:measure` is `∫ f dμ = ∑_{γ ∈ W} (∫ f dν_γ) t^γ`
(`coefIntegral`), and coefficientwise weak-* convergence means convergence of every
coefficient of `∫ f dμ_k` for every continuous `f` (`CoefWeakStarTendsto`).

## Main results

* The general tool (`tendsto_integral_of_tendsto_moment`): if the Fourier coefficients of
  finite positive measures `μ_i` on the circle converge (along any filter) to those of a finite
  positive measure `μ`, then `∫ f dμ_i → ∫ f dμ` for every continuous `f`. The source's proof
  of `herg:thm:quadrature` uses the unit total masses of `σ_M`; no mass hypothesis is needed
  here, because the zeroth Fourier coefficient is the mass. The tool can also be applied to the
  measures `F_N m` of `herg:thm:fejer`, whose source proof argues directly from the Fejér-kernel
  bound instead.
* `σ_M` has Fourier coefficients `1` when `M ∣ n` and `0` otherwise (`moment_rootMeasure`,
  the finite orthogonality relation), hence the coefficients of `m` for `|n| < M`, and
  `σ_M → m` weak-*: `∫ f dσ_M → ∫ f dm` and `∫ f dσ_M - f(1) → ∫ f dm - f(1)` for every
  continuous `f` (`tendsto_integral_rootMeasure`, `tendsto_integral_rootMeasure_sub`), also
  as convergence of probability measures (`tendsto_rootProbabilityMeasure`).
* `herg:thm:quadrature`, for every `M ≥ 1` (the source takes `M ≥ 2`): `μ_M` is a positive
  coefficientwise Hahn probability measure (`quadFamily_nonneg`, via the two-scale criterion
  `herg:cor:twoscale`, and `coefSeries_quadFamily_univ`); it has the moments
  `herg:eq:mainmoments` for `|n| < M` (`coefMoment_quadFamily`); as `M → ∞` it converges
  coefficientwise weak-* to `(1 + ε) m - ε δ_1` (`coefWeakStarTendsto_quadFamily`), with
  `∫ f dσ_M → ∫ f dm` and `∫ f d(σ_M - δ_1) → ∫ f dm - f(1)`; its coefficient measures have
  total variation at most `1` and `2` (`totalVariation_quadFamily_zero_le`,
  `totalVariation_quadFamily_le`); and the limit is a nonpositive Hahn probability
  (`Surreal.NegativeAtomMeasure.negAtomFamily_not_positive`, `coefSeries_negAtomFamily_univ`).
  The package is `quadrature`; the nonclosedness of the positive cone, with one fixed
  two-element support and uniformly bounded coefficient variations, is
  `not_closed_positive_cone`.

## Scope

Coefficientwise weak-* convergence is formalized as the convergence of each coefficient of the
coefficientwise integral against each continuous complex function; no topology on the space of
coefficientwise measures is constructed, and the nonclosedness statement is the existence of a
convergent sequence of positive probabilities with a nonpositive limit. The general tool is
proved for positive finite measures, which covers `σ_M` (and the measures `F_N m` of
`herg:thm:fejer`); a version for signed measures of bounded total variation is not stated.
`herg:thm:fejer` remains pending.
-/

namespace Surreal.RootQuadrature

open MeasureTheory AddCircle Filter Topology _root_.HahnSeries Surreal.NullIdeal
  Surreal.NegativeAtomMeasure
open scoped NNReal ENNReal Real

noncomputable section

section WeakStar

variable {T : ℝ} [Fact (0 < T)]

omit [Fact (0 < T)] in
/-- The zeroth Fourier moment of a measure on the circle is its total mass. -/
theorem moment_zero_eq_mass (μ : Measure (AddCircle T)) :
    moment μ 0 = (μ.real Set.univ : ℂ) := by
  simp [moment, integral_const]

/-- `‖∫ f dμ‖ ≤ ‖f‖ μ(X)` for a continuous `f` on the circle. -/
theorem norm_integral_continuousMap_le (μ : Measure (AddCircle T)) [IsFiniteMeasure μ]
    (f : C(AddCircle T, ℂ)) : ‖∫ x, f x ∂μ‖ ≤ ‖f‖ * μ.real Set.univ :=
  norm_integral_le_of_norm_le_const (Eventually.of_forall f.norm_coe_le_norm)

variable {ι : Type*} {l : Filter ι} {μs : ι → Measure (AddCircle T)}
  [∀ i, IsFiniteMeasure (μs i)] {μ : Measure (AddCircle T)} [IsFiniteMeasure μ]

/-- Convergence of Fourier coefficients gives convergence of the integrals of every
trigonometric polynomial. -/
theorem tendsto_integral_of_mem_span
    (h : ∀ n, Tendsto (fun i => moment (μs i) n) l (𝓝 (moment μ n)))
    {f : C(AddCircle T, ℂ)} (hf : f ∈ Submodule.span ℂ (Set.range (fourier (T := T)))) :
    Tendsto (fun i => ∫ x, f x ∂μs i) l (𝓝 (∫ x, f x ∂μ)) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨n, rfl⟩ := hg
    simpa [moment, neg_neg] using h (-n)
  | zero => simpa using tendsto_const_nhds
  | add f g _ _ hf hg =>
    have e : ∀ (ν : Measure (AddCircle T)) [IsFiniteMeasure ν],
        ∫ x, (f + g) x ∂ν = ∫ x, f x ∂ν + ∫ x, g x ∂ν := fun ν _ =>
      integral_add (integrable_continuousMap ν f) (integrable_continuousMap ν g)
    rw [e μ]
    exact (hf.add hg).congr fun i => (e (μs i)).symm
  | smul c f _ hf =>
    simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
    exact hf.const_mul c

/-- The weak-* step of `herg:thm:quadrature`, in general form: if the Fourier coefficients of
finite positive measures `μ_i` on the circle converge to those of a finite positive measure
`μ`, then `∫ f dμ_i → ∫ f dμ` for every continuous `f`. The source's proof uses the unit total
masses of `σ_M`; no mass hypothesis is needed here, because the zeroth Fourier coefficient is
the mass. The proof approximates `f` uniformly by trigonometric polynomials. The tool can also
be applied to the measures `F_N m` of `herg:thm:fejer`. -/
theorem tendsto_integral_of_tendsto_moment
    (h : ∀ n, Tendsto (fun i => moment (μs i) n) l (𝓝 (moment μ n)))
    (f : C(AddCircle T, ℂ)) :
    Tendsto (fun i => ∫ x, f x ∂μs i) l (𝓝 (∫ x, f x ∂μ)) := by
  have hmass : Tendsto (fun i => (μs i).real Set.univ) l (𝓝 (μ.real Set.univ)) := by
    have h0 := (Complex.continuous_re.tendsto _).comp (h 0)
    simpa [Function.comp_def, moment_zero_eq_mass] using h0
  have hB0 : 0 < μ.real Set.univ + 1 := by positivity
  have hbound : ∀ᶠ i in l, (μs i).real Set.univ < μ.real Set.univ + 1 :=
    hmass.eventually (gt_mem_nhds (lt_add_one _))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (4 * (μ.real Set.univ + 1)) := by positivity
  have hf : f ∈ closure
      (Submodule.span ℂ (Set.range (fourier (T := T))) : Set C(AddCircle T, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨p, hp, hfp⟩ := Metric.mem_closure_iff.mp hf _ hδ
  have hpl := Metric.tendsto_nhds.mp (tendsto_integral_of_mem_span h hp) (ε / 2)
    (by positivity)
  filter_upwards [hpl, hbound] with i hi hbi
  rw [dist_eq_norm] at hi hfp ⊢
  have split : ∀ (ν : Measure (AddCircle T)) [IsFiniteMeasure ν],
      ∫ x, f x ∂ν = ∫ x, (f - p) x ∂ν + ∫ x, p x ∂ν := fun ν _ => by
    rw [← integral_add (integrable_continuousMap ν _) (integrable_continuousMap ν _)]
    simp
  rw [split (μs i), split μ]
  have e1 := norm_integral_continuousMap_le (μs i) (f - p)
  have e2 := norm_integral_continuousMap_le μ (f - p)
  have k1 : ‖f - p‖ * (μs i).real Set.univ ≤
      ε / (4 * (μ.real Set.univ + 1)) * (μ.real Set.univ + 1) :=
    mul_le_mul hfp.le hbi.le measureReal_nonneg hδ.le
  have k2 : ‖f - p‖ * μ.real Set.univ ≤
      ε / (4 * (μ.real Set.univ + 1)) * (μ.real Set.univ + 1) :=
    mul_le_mul hfp.le (by linarith) measureReal_nonneg hδ.le
  have k3 : ε / (4 * (μ.real Set.univ + 1)) * (μ.real Set.univ + 1) = ε / 4 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hB0.ne']
  have tri : ∀ a b c d : ℂ, ‖a + b - (c + d)‖ ≤ ‖a‖ + ‖b - d‖ + ‖c‖ := fun a b c d =>
    calc ‖a + b - (c + d)‖ = ‖(a + (b - d)) - c‖ := by congr 1; ring
      _ ≤ ‖a + (b - d)‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ ‖a‖ + ‖b - d‖ + ‖c‖ := add_le_add_left (norm_add_le _ _) _
  linarith [tri (∫ x, (f - p) x ∂μs i) (∫ x, p x ∂μs i) (∫ x, (f - p) x ∂μ) (∫ x, p x ∂μ)]

end WeakStar

section Roots

variable {T : ℝ}

/-- The point `x_j = j T / M` of `AddCircle T`; it is the root of unity `ζ_M^j`,
`ζ_M = e^{2π i / M}` (`fourier_rootPoint`). -/
def rootPoint (M j : ℕ) : AddCircle T :=
  ((j * (T / M) : ℝ) : AddCircle T)

theorem rootPoint_zero (M : ℕ) : rootPoint (T := T) M 0 = 0 := by
  simp [rootPoint]

/-- The root-of-unity quadrature `σ_M = M⁻¹ ∑_{j < M} δ_{ζ_M^j}` of `herg:thm:quadrature`: the
uniform probability measure on the `M`th roots of unity (for `M ≠ 0`). -/
def rootMeasure (M : ℕ) : Measure (AddCircle T) :=
  (M : ℝ≥0)⁻¹ • ∑ j ∈ Finset.range M, Measure.dirac (rootPoint M j)

theorem rootMeasure_apply (M : ℕ) (A : Set (AddCircle T)) :
    rootMeasure M A =
      (((M : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ∑ j ∈ Finset.range M, Measure.dirac (rootPoint M j) A := by
  rw [rootMeasure, Measure.smul_apply, Measure.finsetSum_apply, ENNReal.smul_def, smul_eq_mul]

theorem rootMeasure_univ {M : ℕ} (hM : M ≠ 0) : rootMeasure (T := T) M Set.univ = 1 := by
  rw [rootMeasure_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [ENNReal.coe_inv (by exact_mod_cast hM), ENNReal.coe_natCast,
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top M)]

theorem rootMeasure_univ_le_one (M : ℕ) : rootMeasure (T := T) M Set.univ ≤ 1 := by
  rcases eq_or_ne M 0 with rfl | hM
  · simp [rootMeasure]
  · rw [rootMeasure_univ hM]

instance isFiniteMeasure_rootMeasure (M : ℕ) : IsFiniteMeasure (rootMeasure (T := T) M) :=
  ⟨(rootMeasure_univ_le_one M).trans_lt ENNReal.one_lt_top⟩

instance isProbabilityMeasure_rootMeasure (M : ℕ) [NeZero M] :
    IsProbabilityMeasure (rootMeasure (T := T) M) :=
  ⟨rootMeasure_univ (NeZero.ne M)⟩

/-- `σ_{M+1}` as a probability measure. -/
def rootProbabilityMeasure (M : ℕ) : ProbabilityMeasure (AddCircle T) :=
  ⟨rootMeasure (M + 1), inferInstance⟩

/-- The point `ζ = 1` carries mass `1/M > 0` for `σ_M`, so `δ_1 ≪ σ_M`. -/
theorem dirac_zero_absolutelyContinuous {M : ℕ} (hM : M ≠ 0) :
    Measure.dirac (0 : AddCircle T) ≪ rootMeasure M := by
  refine Measure.AbsolutelyContinuous.mk fun A _ h => ?_
  rw [rootMeasure_apply, mul_eq_zero] at h
  have hinv : (((M : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simp [hM]
  have h0 := Finset.sum_eq_zero_iff.mp (h.resolve_left hinv) 0
    (Finset.mem_range.mpr (Nat.pos_of_ne_zero hM))
  rwa [rootPoint_zero] at h0

variable [Fact (0 < T)]

/-- `rootPoint M j` is the root of unity `ζ_M^j`: `ζ^n = fourier n` takes the value
`(ζ_M^n)^j` there. -/
theorem fourier_rootPoint {M : ℕ} (hM : M ≠ 0) (n : ℤ) (j : ℕ) :
    fourier n (rootPoint (T := T) M j) = (Complex.exp (2 * π * Complex.I / M) ^ n) ^ j := by
  have hT : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Fact.out : 0 < T).ne'
  have hMc : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  rw [rootPoint, fourier_coe_apply, ← Complex.exp_int_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- `rootPoint M j` is the point `ζ_M^j` of the unit circle, `ζ_M = e^{2π i / M}`. -/
theorem toCircle_rootPoint {M : ℕ} (hM : M ≠ 0) (j : ℕ) :
    (toCircle (rootPoint (T := T) M j) : ℂ) = Complex.exp (2 * π * Complex.I / M) ^ j := by
  rw [← fourier_one, fourier_rootPoint hM, zpow_one]

/-- Each `rootPoint M j` is an `M`th root of unity. -/
theorem toCircle_rootPoint_pow {M : ℕ} (hM : M ≠ 0) (j : ℕ) :
    (toCircle (rootPoint (T := T) M j) : ℂ) ^ M = 1 := by
  rw [toCircle_rootPoint hM, ← pow_mul, mul_comm j M, pow_mul,
    (Complex.isPrimitiveRoot_exp M hM).pow_eq_one, one_pow]

/-- The points `rootPoint M j`, `j < M`, are distinct. -/
theorem rootPoint_injOn {M : ℕ} (hM : M ≠ 0) : Set.InjOn (rootPoint (T := T) M) (Set.Iio M) :=
  fun i hi j hj h => (Complex.isPrimitiveRoot_exp M hM).pow_inj hi hj <| by
    rw [← toCircle_rootPoint (T := T) hM, ← toCircle_rootPoint (T := T) hM, h]

/-- Every `M`th root of unity is one of the points `rootPoint M j`, `j < M`; with
`toCircle_rootPoint_pow` and `rootPoint_injOn`, `σ_M` is the uniform probability measure on the
`M` distinct `M`th roots of unity. -/
theorem exists_rootPoint_eq {M : ℕ} (hM : M ≠ 0) {z : ℂ} (hz : z ^ M = 1) :
    ∃ j < M, (toCircle (rootPoint (T := T) M j) : ℂ) = z := by
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨j, hj, rfl⟩ := (Complex.isPrimitiveRoot_exp M hM).eq_pow_of_pow_eq_one hz
  exact ⟨j, hj, toCircle_rootPoint hM j⟩

/-- The finite orthogonality relation: the Fourier coefficient of `σ_M` at `n` is `1` when `M`
divides `n` and `0` otherwise. -/
theorem moment_rootMeasure {M : ℕ} (hM : M ≠ 0) (n : ℤ) :
    moment (rootMeasure (T := T) M) n = if (M : ℤ) ∣ n then 1 else 0 := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / M)) M :=
    Complex.isPrimitiveRoot_exp M hM
  rw [moment, rootMeasure, integral_smul_nnreal_measure,
    integral_finsetSum_measure fun j _ => integrable_continuousMap _ _]
  simp_rw [integral_dirac, fourier_rootPoint hM]
  generalize Complex.exp (2 * π * Complex.I / M) = ζ at hprim ⊢
  split_ifs with hdvd
  · have h1 : ζ ^ (-n) = 1 := (hprim.zpow_eq_one_iff_dvd (-n)).mpr (dvd_neg.mpr hdvd)
    rw [h1]
    simp [hM, NNReal.smul_def]
  · have h1 : ζ ^ (-n) ≠ 1 := fun h =>
      hdvd (dvd_neg.mp ((hprim.zpow_eq_one_iff_dvd (-n)).mp h))
    have hpow : (ζ ^ (-n)) ^ M = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hprim.pow_eq_one,
        one_zpow]
    rw [geom_sum_eq h1, hpow, sub_self, zero_div, smul_zero]

/-- For `|n| < M`, the Fourier coefficient of `σ_M` at `n` is that of Haar measure. -/
theorem moment_rootMeasure_of_natAbs_lt {M : ℕ} {n : ℤ} (hn : n.natAbs < M) :
    moment (rootMeasure (T := T) M) n = moment (haarAddCircle (T := T)) n := by
  have hM : M ≠ 0 := by omega
  rw [moment_rootMeasure hM, moment_haarAddCircle]
  by_cases h0 : n = 0
  · simp [h0]
  · rw [if_neg h0, if_neg fun h =>
      h0 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using hn))]

theorem tendsto_moment_rootMeasure (n : ℤ) :
    Tendsto (fun M => moment (rootMeasure (T := T) M) n) atTop
      (𝓝 (moment (haarAddCircle (T := T)) n)) :=
  tendsto_const_nhds.congr' <| (eventually_gt_atTop n.natAbs).mono fun _ hM =>
    (moment_rootMeasure_of_natAbs_lt hM).symm

/-- `herg:thm:quadrature`, weak-* convergence of the quadratures: `∫ f dσ_M → ∫ f dm` for every
continuous `f` on the circle. -/
theorem tendsto_integral_rootMeasure (f : C(AddCircle T, ℂ)) :
    Tendsto (fun M => ∫ x, f x ∂rootMeasure (T := T) M) atTop
      (𝓝 (∫ x, f x ∂haarAddCircle (T := T))) :=
  tendsto_integral_of_tendsto_moment tendsto_moment_rootMeasure f

/-- `herg:thm:quadrature`, weak-* convergence of the exponent-`η` coefficient:
`∫ f d(σ_M - δ_1) = ∫ f dσ_M - f(1) → ∫ f dm - f(1)`. -/
theorem tendsto_integral_rootMeasure_sub (f : C(AddCircle T, ℂ)) :
    Tendsto (fun M => ∫ x, f x ∂rootMeasure (T := T) M - f 0) atTop
      (𝓝 (∫ x, f x ∂haarAddCircle (T := T) - f 0)) :=
  (tendsto_integral_rootMeasure f).sub_const _

/-- The weak-* convergence `σ_M → m`, in the topology of weak convergence of probability
measures. -/
theorem tendsto_rootProbabilityMeasure :
    Tendsto (rootProbabilityMeasure (T := T)) atTop
      (𝓝 ⟨haarAddCircle (T := T), inferInstance⟩) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  exact (tendsto_integral_rootMeasure f.toContinuousMap).comp (tendsto_add_atTop_nat 1)

end Roots

section Coefficientwise

variable {T : ℝ}

/-- The integral `∫ f ds = ∫ f ds⁺ - ∫ f ds⁻` of a continuous function against a finite signed
measure on the circle. -/
def signedIntegral (s : SignedMeasure (AddCircle T)) (f : C(AddCircle T, ℂ)) : ℂ :=
  ∫ x, f x ∂s.toJordanDecomposition.posPart - ∫ x, f x ∂s.toJordanDecomposition.negPart

/-- The Fourier moments `signedMoment` are the integrals of the characters `ζ^{-n}`. -/
theorem signedIntegral_fourier (s : SignedMeasure (AddCircle T)) (n : ℤ) :
    signedIntegral s (fourier (-n)) = signedMoment s n :=
  rfl

variable {Γ : Type*} [LinearOrder Γ]

open scoped Classical in
/-- The coefficientwise integral `∫ f dμ = ∑_{γ ∈ W} (∫ f dν_γ) t^γ` in `ℂ((t^Γ))` of a
continuous `f` against the coefficientwise Hahn measure `μ = ∑_{γ ∈ W} ν_γ t^γ` of
`herg:def:measure`. The measures at exponents outside `W` are ignored. -/
def coefIntegral (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure (AddCircle T))
    (f : C(AddCircle T, ℂ)) : ℂ⟦Γ⟧ where
  coeff γ := if γ ∈ W then signedIntegral (ν γ) f else 0
  isPWO_support' := hW.isPWO.mono fun γ hγ => by
    by_contra h
    exact hγ (if_neg h)

open scoped Classical in
theorem coeff_coefIntegral (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure (AddCircle T))
    (f : C(AddCircle T, ℂ)) (γ : Γ) :
    (coefIntegral W hW ν f).coeff γ = if γ ∈ W then signedIntegral (ν γ) f else 0 :=
  rfl

/-- The coefficientwise Fourier moments are the coefficientwise integrals of the characters. -/
theorem coefIntegral_fourier (W : Set Γ) (hW : W.IsWF) (ν : Γ → SignedMeasure (AddCircle T))
    (n : ℤ) : coefIntegral W hW ν (fourier (-n)) = coefMoment W hW ν n :=
  rfl

/-- Coefficientwise weak-* convergence of coefficientwise Hahn measures with a fixed support
`W`: for every continuous `f` on the circle and every exponent `γ`, the `γ`-coefficient of
`∫ f dμ_i` converges to that of `∫ f dμ`. -/
def CoefWeakStarTendsto {ι : Type*} (l : Filter ι) (W : Set Γ) (hW : W.IsWF)
    (ν : ι → Γ → SignedMeasure (AddCircle T)) (ν' : Γ → SignedMeasure (AddCircle T)) : Prop :=
  ∀ (f : C(AddCircle T, ℂ)) (γ : Γ),
    Tendsto (fun i => (coefIntegral W hW (ν i) f).coeff γ) l
      (𝓝 ((coefIntegral W hW ν' f).coeff γ))

variable [Fact (0 < T)]

/-- The signed integral may be computed from any decomposition `s = μ₁ - μ₂`. -/
theorem signedIntegral_eq_of_eq_sub {s : SignedMeasure (AddCircle T)}
    {μ₁ μ₂ : Measure (AddCircle T)} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hs : s = μ₁.toSignedMeasure - μ₂.toSignedMeasure) (f : C(AddCircle T, ℂ)) :
    signedIntegral s f = ∫ x, f x ∂μ₁ - ∫ x, f x ∂μ₂ := by
  have h1 : s.toJordanDecomposition.posPart.toSignedMeasure -
      s.toJordanDecomposition.negPart.toSignedMeasure =
        μ₁.toSignedMeasure - μ₂.toSignedMeasure := by
    rw [← hs]
    exact s.toSignedMeasure_toJordanDecomposition
  have h2 : s.toJordanDecomposition.posPart + μ₂ = μ₁ + s.toJordanDecomposition.negPart := by
    rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff, Measure.toSignedMeasure_add,
      Measure.toSignedMeasure_add, ← sub_eq_sub_iff_add_eq_add]
    exact h1
  have h3 := congrArg (fun m => ∫ x, f x ∂m) h2
  rw [integral_add_measure (integrable_continuousMap _ f) (integrable_continuousMap _ f),
    integral_add_measure (integrable_continuousMap _ f) (integrable_continuousMap _ f)] at h3
  rw [signedIntegral]
  linear_combination h3

theorem signedIntegral_sub (μ₁ μ₂ : Measure (AddCircle T)) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (f : C(AddCircle T, ℂ)) :
    signedIntegral (μ₁.toSignedMeasure - μ₂.toSignedMeasure) f =
      ∫ x, f x ∂μ₁ - ∫ x, f x ∂μ₂ :=
  signedIntegral_eq_of_eq_sub rfl f

theorem signedIntegral_toSignedMeasure (μ : Measure (AddCircle T)) [IsFiniteMeasure μ]
    (f : C(AddCircle T, ℂ)) : signedIntegral μ.toSignedMeasure f = ∫ x, f x ∂μ := by
  rw [signedIntegral_eq_of_eq_sub (μ₁ := μ) (μ₂ := 0)
    (by rw [Measure.toSignedMeasure_zero, sub_zero]) f, integral_zero_measure, sub_zero]

end Coefficientwise

section Quadrature

variable {T : ℝ} {Γ : Type*} [LinearOrder Γ] [Zero Γ] {η : Γ}

/-- `herg:eq:quadrature`: the coefficient family of `μ_M = (1 + ε) σ_M - ε δ_1 =
σ_M + t^η (σ_M - δ_1)`. The exponent-`0` coefficient is `σ_M`; every other exponent carries
`σ_M - δ_1`, but only the support `{0, η}` is used. -/
def quadFamily (M : ℕ) (γ : Γ) : SignedMeasure (AddCircle T) :=
  if γ = 0 then (rootMeasure (T := T) M).toSignedMeasure
  else (rootMeasure (T := T) M).toSignedMeasure - (Measure.dirac (0 : AddCircle T)).toSignedMeasure

/-- `herg:eq:quadrature`: `μ_M(A) = σ_M(A) + t^η (σ_M(A) - δ_1(A))` on measurable sets. -/
theorem coefSeries_quadFamily (hη : 0 < η) (M : ℕ) {A : Set (AddCircle T)}
    (hA : MeasurableSet A) :
    coefSeries {0, η} (isWF_pair η) (quadFamily (T := T) M) A =
      single 0 ((rootMeasure (T := T) M).real A) +
        single η ((rootMeasure (T := T) M).real A - (Measure.dirac (0 : AddCircle T)).real A) := by
  ext γ
  rw [coeff_coefSeries, coeff_add]
  by_cases h0 : γ = 0
  · subst h0
    simp [quadFamily, hη.ne, Measure.toSignedMeasure_apply_measurable hA]
  · by_cases h1 : γ = η
    · subst h1
      simp [quadFamily, h0, Measure.toSignedMeasure_apply_measurable hA]
    · simp [h0, h1]

/-- `herg:thm:quadrature`, positivity: for `M ≥ 1`, `μ_M` is a positive coefficientwise Hahn
measure. By the two-scale criterion `herg:cor:twoscale`, this is `(σ_M - δ_1)⁻ ≪ σ_M`, and
`(σ_M - δ_1)⁻ = δ_1 - σ_M ≤ δ_1 ≪ σ_M` because `σ_M({1}) = 1/M > 0`. -/
theorem quadFamily_nonneg (hη : 0 < η) {M : ℕ} (hM : M ≠ 0) (A : Set (AddCircle T))
    (hA : MeasurableSet A) :
    0 ≤ toLex (coefSeries {0, η} (isWF_pair η) (quadFamily (T := T) M) A) := by
  have h := (twoScale_measure hη (rootMeasure (T := T) M)
    ((rootMeasure (T := T) M).toSignedMeasure -
      (Measure.dirac (0 : AddCircle T)).toSignedMeasure)).mpr ?_
  · rw [coefSeries_quadFamily hη M hA]
    have := h A hA
    rwa [Measure.toSignedMeasure_sub_apply hA] at this
  · rw [Measure.toJordanDecomposition_toSignedMeasure_sub,
      Measure.jordanDecompositionOfToSignedMeasureSub_negPart]
    exact (Measure.absolutelyContinuous_of_le Measure.sub_le).trans
      (dirac_zero_absolutelyContinuous hM)

/-- `herg:thm:quadrature`: `μ_M` is a Hahn probability, `μ_M(X) = 1`. -/
theorem coefSeries_quadFamily_univ (hη : 0 < η) {M : ℕ} (hM : M ≠ 0) :
    coefSeries {0, η} (isWF_pair η) (quadFamily (T := T) M) Set.univ = 1 := by
  haveI : NeZero M := ⟨hM⟩
  rw [coefSeries_quadFamily hη M MeasurableSet.univ, probReal_univ, probReal_univ, sub_self,
    single_eq_zero, add_zero, single_zero_one]

/-- `herg:thm:quadrature`: the coefficient measures of `μ_M` have total variation at most `1`
(exponent `0`, the probability `σ_M`). -/
theorem totalVariation_quadFamily_zero_le (M : ℕ) :
    (quadFamily (T := T) M (0 : Γ)).totalVariation Set.univ ≤ 1 := by
  rw [quadFamily, if_pos rfl, totalVariation_toSignedMeasure]
  exact rootMeasure_univ_le_one M

/-- `herg:thm:quadrature`: every coefficient measure of `μ_M` has total variation at most `2`
(at most `1` for `σ_M` and at most `2` for `σ_M - δ_1`). -/
theorem totalVariation_quadFamily_le (M : ℕ) (γ : Γ) :
    (quadFamily (T := T) M γ).totalVariation Set.univ ≤ 2 := by
  by_cases h : γ = 0
  · subst h
    exact (totalVariation_quadFamily_zero_le M).trans one_le_two
  · rw [quadFamily, if_neg h, SignedMeasure.totalVariation,
      Measure.toJordanDecomposition_toSignedMeasure_sub,
      Measure.jordanDecompositionOfToSignedMeasureSub_posPart,
      Measure.jordanDecompositionOfToSignedMeasureSub_negPart, Measure.add_apply]
    have e1 := Measure.le_iff'.mp
      (Measure.sub_le (μ := rootMeasure (T := T) M) (ν := Measure.dirac 0)) Set.univ
    have e2 := Measure.le_iff'.mp
      (Measure.sub_le (μ := Measure.dirac (0 : AddCircle T)) (ν := rootMeasure (T := T) M))
      Set.univ
    have e3 : Measure.dirac (0 : AddCircle T) Set.univ ≤ 1 := prob_le_one
    calc _ ≤ rootMeasure (T := T) M Set.univ + Measure.dirac (0 : AddCircle T) Set.univ :=
          add_le_add e1 e2
      _ ≤ 1 + 1 := add_le_add (rootMeasure_univ_le_one M) e3
      _ = 2 := one_add_one_eq_two

variable [Fact (0 < T)]

/-- For `|n| < M`, every coefficient measure of `μ_M` has the Fourier coefficient at `n` of the
corresponding coefficient measure of `(1 + ε) m - ε δ_1`. -/
theorem signedMoment_quadFamily {M : ℕ} {n : ℤ} (hn : n.natAbs < M) (γ : Γ) :
    signedMoment (quadFamily (T := T) M γ) n = signedMoment (negAtomFamily (T := T) γ) n := by
  have hm := moment_rootMeasure_of_natAbs_lt (T := T) hn
  by_cases h : γ = 0
  · rw [quadFamily, negAtomFamily, if_pos h, if_pos h, signedMoment_toSignedMeasure,
      signedMoment_toSignedMeasure, hm]
  · rw [quadFamily, negAtomFamily, if_neg h, if_neg h, signedMoment_eq_of_eq_sub rfl,
      signedMoment_eq_of_eq_sub rfl, hm]

/-- `herg:thm:quadrature`, moments: `μ_M` represents `herg:eq:mainmoments` for `|n| < M`,
`c_0 = 1` and `c_n = -ε` for `0 < |n| < M`. -/
theorem coefMoment_quadFamily (hη : 0 < η) {M : ℕ} {n : ℤ} (hn : n.natAbs < M) :
    coefMoment {0, η} (isWF_pair η) (quadFamily (T := T) M) n = negAtomMoments η n := by
  rw [← coefMoment_negAtomFamily (T := T) hη n]
  ext γ
  rw [coeff_coefMoment, coeff_coefMoment]
  split_ifs
  · exact signedMoment_quadFamily hn γ
  · rfl

theorem signedIntegral_quadFamily_zero (M : ℕ) (f : C(AddCircle T, ℂ)) :
    signedIntegral (quadFamily (T := T) M (0 : Γ)) f = ∫ x, f x ∂rootMeasure (T := T) M := by
  rw [quadFamily, if_pos rfl, signedIntegral_toSignedMeasure]

/-- The coefficient at every exponent `γ ≠ 0`, in particular `η`:
`∫ f d(σ_M - δ_1) = ∫ f dσ_M - f(1)`. -/
theorem signedIntegral_quadFamily_of_ne (M : ℕ) {γ : Γ} (hγ : γ ≠ 0) (f : C(AddCircle T, ℂ)) :
    signedIntegral (quadFamily (T := T) M γ) f = ∫ x, f x ∂rootMeasure (T := T) M - f 0 := by
  rw [quadFamily, if_neg hγ, signedIntegral_sub, integral_dirac]

/-- `herg:thm:quadrature`: each coefficient of `μ_M` converges weak-* to the corresponding
coefficient of `(1 + ε) m - ε δ_1`; `∫ f dσ_M → ∫ f dm` and
`∫ f d(σ_M - δ_1) → ∫ f dm - f(1)`. -/
theorem tendsto_signedIntegral_quadFamily (γ : Γ) (f : C(AddCircle T, ℂ)) :
    Tendsto (fun M => signedIntegral (quadFamily (T := T) M γ) f) atTop
      (𝓝 (signedIntegral (negAtomFamily (T := T) γ) f)) := by
  by_cases h : γ = 0
  · subst h
    rw [negAtomFamily, if_pos rfl, signedIntegral_toSignedMeasure]
    simp only [signedIntegral_quadFamily_zero]
    exact tendsto_integral_rootMeasure f
  · rw [negAtomFamily, if_neg h, signedIntegral_sub, integral_dirac]
    simp only [signedIntegral_quadFamily_of_ne _ h]
    exact tendsto_integral_rootMeasure_sub f

/-- `herg:thm:quadrature`: `μ_M` converges coefficientwise weak-* to `(1 + ε) m - ε δ_1`
(`herg:eq:badmeasure`) as `M → ∞`. -/
theorem coefWeakStarTendsto_quadFamily (η : Γ) :
    CoefWeakStarTendsto atTop {0, η} (isWF_pair η) (quadFamily (T := T))
      (negAtomFamily (T := T)) := by
  intro f γ
  simp only [coeff_coefIntegral]
  split_ifs
  · exact tendsto_signedIntegral_quadFamily γ f
  · exact tendsto_const_nhds

/-- The limit `(1 + ε) m - ε δ_1` is also a coefficientwise Hahn probability. -/
theorem coefSeries_negAtomFamily_univ (hη : 0 < η) :
    coefSeries {0, η} (isWF_pair η) (negAtomFamily (T := T)) Set.univ = 1 := by
  rw [coefSeries_negAtomFamily hη MeasurableSet.univ, probReal_univ, probReal_univ, sub_self,
    single_eq_zero, add_zero, single_zero_one]

/-- `herg:thm:quadrature`, for `ε = t^η` with `0 < η` in any linearly ordered exponent set:
for every `M ≥ 1`, `μ_M = σ_M + t^η (σ_M - δ_1) = (1 + ε) σ_M - ε δ_1` is a positive
coefficientwise Hahn probability measure on the circle with the moments `herg:eq:mainmoments`
for `|n| < M`, and its coefficient measures have total variation at most `1` and `2`; as
`M → ∞` it converges coefficientwise weak-* to `(1 + ε) m - ε δ_1`, which is a coefficientwise
Hahn probability measure that is not positive. -/
theorem quadrature (hη : 0 < η) :
    (∀ M : ℕ, M ≠ 0 →
      (∀ A, MeasurableSet A →
        0 ≤ toLex (coefSeries {0, η} (isWF_pair η) (quadFamily (T := T) M) A)) ∧
      coefSeries {0, η} (isWF_pair η) (quadFamily (T := T) M) Set.univ = 1 ∧
      ∀ n : ℤ, n.natAbs < M →
        coefMoment {0, η} (isWF_pair η) (quadFamily (T := T) M) n = negAtomMoments η n) ∧
    (∀ M : ℕ, (quadFamily (T := T) M (0 : Γ)).totalVariation Set.univ ≤ 1 ∧
      (quadFamily (T := T) M η).totalVariation Set.univ ≤ 2) ∧
    CoefWeakStarTendsto atTop {0, η} (isWF_pair η) (quadFamily (T := T))
      (negAtomFamily (T := T)) ∧
    coefSeries {0, η} (isWF_pair η) (negAtomFamily (T := T)) Set.univ = 1 ∧
    ¬ ∀ A, MeasurableSet A →
      0 ≤ toLex (coefSeries {0, η} (isWF_pair η) (negAtomFamily (T := T)) A) :=
  ⟨fun _ hM => ⟨quadFamily_nonneg hη hM, coefSeries_quadFamily_univ hη hM,
      fun _ hn => coefMoment_quadFamily hη hn⟩,
    fun M => ⟨totalVariation_quadFamily_zero_le M, totalVariation_quadFamily_le M η⟩,
    coefWeakStarTendsto_quadFamily η, coefSeries_negAtomFamily_univ hη,
    negAtomFamily_not_positive hη⟩

/-- `herg:thm:quadrature`, nonclosedness: the positive coefficientwise Hahn-probability cone on
the circle is not closed under coefficientwise weak-* convergence, even with one fixed
two-element support `{0, η}` and uniformly bounded coefficient total variations. -/
theorem not_closed_positive_cone (hη : 0 < η) :
    ∃ (ν : ℕ → Γ → SignedMeasure (AddCircle T)) (ν' : Γ → SignedMeasure (AddCircle T)),
      (∀ k, (∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries {0, η} (isWF_pair η) (ν k) A)) ∧
        coefSeries {0, η} (isWF_pair η) (ν k) Set.univ = 1 ∧
        ∀ γ, (ν k γ).totalVariation Set.univ ≤ 2) ∧
      CoefWeakStarTendsto atTop {0, η} (isWF_pair η) ν ν' ∧
      ¬ ∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries {0, η} (isWF_pair η) ν' A) :=
  ⟨fun k => quadFamily (k + 1), negAtomFamily,
    fun k => ⟨quadFamily_nonneg hη k.succ_ne_zero, coefSeries_quadFamily_univ hη k.succ_ne_zero,
      totalVariation_quadFamily_le (k + 1)⟩,
    fun f γ => (coefWeakStarTendsto_quadFamily η f γ).comp (tendsto_add_atTop_nat 1),
    negAtomFamily_not_positive hη⟩

end Quadrature

section OrderedGroup

variable {T : ℝ} {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] {η : Γ}

/-- `σ_M(A) = M⁻¹ ∑_{j < M} δ_{ζ_M^j}(A)`. -/
theorem rootMeasure_real_apply (M : ℕ) (A : Set (AddCircle T)) :
    (rootMeasure (T := T) M).real A =
      (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, (Measure.dirac (rootPoint (T := T) M j)).real A := by
  rw [measureReal_def, rootMeasure_apply, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_inv,
    NNReal.coe_natCast, ENNReal.toReal_sum fun j _ => measure_ne_top _ _]
  rfl

/-- `herg:eq:quadrature` in the ring `ℝ((t^Γ))`: `μ_M(A) = (1 + ε) σ_M(A) - ε δ_1(A)` with
`ε = t^η`. -/
theorem coefSeries_quadFamily_eq (hη : 0 < η) (M : ℕ) {A : Set (AddCircle T)}
    (hA : MeasurableSet A) :
    coefSeries {0, η} (isWF_pair η) (quadFamily (T := T) M) A =
      (1 + single η 1) * C ((rootMeasure (T := T) M).real A) -
        single η 1 * C ((Measure.dirac (0 : AddCircle T)).real A) := by
  rw [coefSeries_quadFamily hη M hA, add_mul, one_mul, C_apply, C_apply, single_mul_single,
    single_mul_single, add_zero, one_mul, one_mul, single_sub, add_sub_assoc]

/-- `herg:thm:quadrature`, atomic form: `μ_M(A) = ∑_{j < M} w_j δ_{ζ_M^j}(A)` in `ℝ((t^Γ))`,
with the weights `w_j = (1 + ε)/M - [j = 0] ε` of `Surreal.Herglotz.quadratureWeight` at
`ε = t^η`. They are positive in the ordered field `Lex ℝ((t^Γ))`
(`toLex_quadratureWeight_single_pos`). -/
theorem coefSeries_quadFamily_eq_sum (hη : 0 < η) {M : ℕ} (hM : M ≠ 0)
    {A : Set (AddCircle T)} (hA : MeasurableSet A) :
    coefSeries {0, η} (isWF_pair η) (quadFamily (T := T) M) A =
      ∑ j ∈ Finset.range M, Herglotz.quadratureWeight M (single η (1 : ℝ)) j *
        C ((Measure.dirac (rootPoint (T := T) M j)).real A) := by
  rw [coefSeries_quadFamily_eq hη M hA, rootMeasure_real_apply, map_mul, map_sum, map_inv₀,
    map_natCast]
  simp only [Herglotz.quadratureWeight, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_range, if_pos (Nat.pos_of_ne_zero hM), rootPoint_zero,
    ← Finset.mul_sum]
  ring

/-- `herg:thm:quadrature`, positive weights: for `M ≥ 1` the weights
`w_j = (1 + t^η)/M - [j = 0] t^η` of `coefSeries_quadFamily_eq_sum` are positive in the ordered
field `Lex ℝ((t^Γ))`, by `Surreal.Herglotz.quadratureWeight_pos`, since `(M - 1) t^η < 1`
(`Surreal.HerglotzHierarchy.natCast_mul_toLex_single_lt_one`). -/
theorem toLex_quadratureWeight_single_pos (hη : 0 < η) {M : ℕ} (hM : M ≠ 0) (j : ℕ) :
    0 < toLex (Herglotz.quadratureWeight M (single η (1 : ℝ)) j) := by
  have h := HerglotzHierarchy.natCast_mul_toLex_single_lt_one hη (M - 1)
  rw [Nat.cast_pred (Nat.pos_of_ne_zero hM)] at h
  exact Herglotz.quadratureWeight_pos (Nat.pos_of_ne_zero hM)
    (Herglotz.toLex_single_one_pos η) h j

end OrderedGroup

end

end Surreal.RootQuadrature
