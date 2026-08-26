import FabiusFunction.GlobalDyadic
import FabiusFunction.GlobalBounds
import FabiusFunction.Regularity
import FabiusFunction.FabiusUniformSpline
import FabiusFunction.PaperStatements
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Partrec
import Mathlib.Topology.EMetricSpace.Basic

/-!
# Computability of the Fabius function

This module formalizes the two clauses in the computable-analysis definition
of a computable real function: effective uniform continuity and preservation
of computable sequences.  The analytic clause is obtained from the global
derivative equation.  The algorithmic clause evaluates finite centered
splines on dyadic grids and rounds them with an explicit error bound.  The
uncentered and midpoint-corrected finite CDFs have respective all-real error
majorants `2 * 2⁻ᵖ` and `2⁻ᵖ`; the latter is exactly half the former.
The same splines approximate the signed extension uniformly on the whole
real line, with sup-norm error at most `2⁻ᵖ` at order `p`.
-/

open scoped BigOperators Topology
open Filter Set

namespace Fabius

set_option autoImplicit false

/-! ## Lipschitz bounds and uniform spline approximation -/

/-- The signed global extension is globally `2`-Lipschitz. -/
theorem extendedFabius_lipschitzWith_two
    (F : BoundedFabius) (hF : IsFabius F) :
    LipschitzWith 2 (extendedFabius F) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact (extendedFabius_contDiff F hF).differentiable (by simp)
  · intro x
    rw [(extendedFabius_hasDerivAt F hF x).deriv]
    change |2 * extendedFabius F (2 * x)| ≤ 2
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [abs_extendedFabius_le_one F hF (2 * x)]


/-- The bounded/CDF Fabius function is globally `2`-Lipschitz.

Retained under this name for source compatibility; the statement, together
with the proof that `2` is the *least* Lipschitz constant, lives in
`FabiusFunction.Regularity`. -/
theorem fabiusReal_lipschitzWith_two
    (F : BoundedFabius) (hF : IsFabius F) :
    LipschitzWith 2 (fabiusReal F) :=
  lipschitzWith_fabiusReal F hF

/-- The uncentered order-`p` finite CDF has the all-real Lipschitz error
majorant `2 * 2⁻ᵖ`. -/
theorem abs_uniformPartialCDF_sub_fabiusReal_le
    (F : BoundedFabius) (hF : IsFabius F) (p : ℕ) (x : ℝ) :
    |ProbabilityRepresentation.uniformPartialCDF p x - fabiusReal F x| ≤
      2 * ((2 : ℝ) ^ p)⁻¹ := by
  have hs := ProbabilityRepresentation.uniformPartialCDF_sandwich p x
  rw [ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal F hF,
    ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal F hF] at hs
  rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
  calc
    ProbabilityRepresentation.uniformPartialCDF p x - fabiusReal F x ≤
        fabiusReal F (x + 1 / (2 : ℝ) ^ p) - fabiusReal F x :=
      sub_le_sub_right hs.2 _
    _ ≤ |fabiusReal F (x + 1 / (2 : ℝ) ^ p) - fabiusReal F x| :=
      le_abs_self _
    _ ≤ 2 * |x + 1 / (2 : ℝ) ^ p - x| :=
      abs_fabiusReal_sub_le F hF _ _
    _ = 2 * ((2 : ℝ) ^ p)⁻¹ := by
      rw [show x + 1 / (2 : ℝ) ^ p - x = 1 / (2 : ℝ) ^ p by ring,
        abs_of_nonneg (by positivity), one_div]

/-- The midpoint-corrected order-`p` finite CDF has the all-real Lipschitz
error majorant `2⁻ᵖ`. -/
theorem abs_uniformCenteredPartialCDF_sub_fabiusReal_le
    (F : BoundedFabius) (hF : IsFabius F) (p : ℕ) (x : ℝ) :
    |ProbabilityRepresentation.uniformCenteredPartialCDF p x - fabiusReal F x| ≤
      ((2 : ℝ) ^ p)⁻¹ := by
  let δ : ℝ := 1 / (2 : ℝ) ^ (p + 1)
  have hs := ProbabilityRepresentation.uniformCenteredPartialCDF_sandwich p x
  rw [ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal F hF,
    ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal F hF] at hs
  have hδ : 2 * |δ| = ((2 : ℝ) ^ p)⁻¹ := by
    dsimp [δ]
    rw [abs_of_nonneg (by positivity), pow_succ]
    field_simp
  have hleft' : |fabiusReal F (x - δ) - fabiusReal F x| ≤
      ((2 : ℝ) ^ p)⁻¹ := by
    calc
      |fabiusReal F (x - δ) - fabiusReal F x| ≤ 2 * |x - δ - x| :=
        abs_fabiusReal_sub_le F hF _ _
      _ = ((2 : ℝ) ^ p)⁻¹ := by
        rw [show x - δ - x = -δ by ring, abs_neg, hδ]
  have hright' : |fabiusReal F (x + δ) - fabiusReal F x| ≤
      ((2 : ℝ) ^ p)⁻¹ := by
    calc
      |fabiusReal F (x + δ) - fabiusReal F x| ≤ 2 * |x + δ - x| :=
        abs_fabiusReal_sub_le F hF _ _
      _ = ((2 : ℝ) ^ p)⁻¹ := by
        rw [show x + δ - x = δ by ring, hδ]
  rw [abs_le]
  constructor
  · have hleftLower : -((2 : ℝ) ^ p)⁻¹ ≤
        fabiusReal F (x - δ) - fabiusReal F x := (abs_le.mp hleft').1
    dsimp [δ] at hs
    linarith [hs.1]
  · have hrightUpper : fabiusReal F (x + δ) - fabiusReal F x ≤
        ((2 : ℝ) ^ p)⁻¹ := (abs_le.mp hright').2
    dsimp [δ] at hs
    linarith [hs.2]

/-- The centered certified majorant is exactly half the uncentered certified
majorant.  This compares the bounds, not the actual pointwise errors, and
makes no optimality claim. -/
theorem uniformCenteredPartialCDF_error_bound_eq_half_uniformPartialCDF_error_bound
    (p : ℕ) :
    ((2 : ℝ) ^ p)⁻¹ =
      (1 / 2 : ℝ) * (2 * ((2 : ℝ) ^ p)⁻¹) := by
  ring

/-- The centered order-`p` uniform spline approximates the bounded Fabius
function with the explicit error `2⁻ᵖ`. -/
theorem abs_fabiusUniformSpline_sub_fabiusReal_le
    (F : BoundedFabius) (hF : IsFabius F) (p : ℕ) (hp : 0 < p)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |fabiusUniformSpline p x - fabiusReal F x| ≤ ((2 : ℝ) ^ p)⁻¹ := by
  rw [ProbabilityRepresentation.fabiusUniformSpline_eq_centeredPartialCDF p hp hx]
  exact abs_uniformCenteredPartialCDF_sub_fabiusReal_le F hF p x

/-- The same explicit spline error estimate in every degree.  At degree zero,
both the elementary step spline and the bounded Fabius function take values in
`[0,1]`, so the right-hand side is exactly one. -/
theorem abs_fabiusUniformSpline_sub_fabiusReal_le_all
    (F : BoundedFabius) (hF : IsFabius F) (p : ℕ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |fabiusUniformSpline p x - fabiusReal F x| ≤ ((2 : ℝ) ^ p)⁻¹ := by
  rw [ProbabilityRepresentation.fabiusUniformSpline_eq_centeredPartialCDF_all p hx]
  exact abs_uniformCenteredPartialCDF_sub_fabiusReal_le F hF p x

/-- The centered order-`p` uniform spline approximates the signed extension
on the whole real line with the same error `2⁻ᵖ` as on `[0,1]`.  Nonpositive
inputs are exact.  Every nonnegative two-unit block is a common signed copy
of the first block, and reflection on its second half preserves the error. -/
theorem abs_fabiusUniformSpline_sub_extendedFabius_le
    (F : BoundedFabius) (hF : IsFabius F) (p : ℕ) (x : ℝ) :
    |fabiusUniformSpline p x - extendedFabius F x| ≤ ((2 : ℝ) ^ p)⁻¹ := by
  rcases le_total 0 x with hx | hx
  · let block : ℕ := ⌊x / 2⌋₊
    let y : ℝ := x - 2 * (block : ℝ)
    have hfloor : (block : ℝ) ≤ x / 2 := by
      dsimp [block]
      exact Nat.floor_le (div_nonneg hx (by norm_num))
    have hfloor' : x / 2 < (block : ℝ) + 1 := by
      dsimp [block]
      exact Nat.lt_floor_add_one (x / 2)
    have hy0 : 0 ≤ y := by dsimp [y]; linarith
    have hy2 : y < 2 := by dsimp [y]; linarith
    have hxform : x = 2 * (block : ℝ) + y := by dsimp [y]; ring
    have hspline : fabiusUniformSpline p x =
        (thueMorseSign block : ℝ) * fabiusUniformSpline p y := by
      rw [hxform]
      exact fabiusUniformSpline_block_translate p block hy0 hy2
    have hext : extendedFabius F x =
        (thueMorseSign block : ℝ) * extendedFabius F y := by
      have hxblock := extendedFabius_eq_single_translate F hF block
        (x := x) (by rw [hxform]; linarith)
        (by rw [hxform]; linarith)
      have hyblock := extendedFabius_eq_single_translate F hF 0
        (x := y) (by norm_num; exact hy0) (by norm_num; exact hy2.le)
      rw [hxblock, hyblock]
      norm_num [binaryWeight, thueMorseSign]
      ring
    have hsign : |(thueMorseSign block : ℝ)| = 1 := by
      rw [thueMorseSign]
      push_cast
      rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [hspline, hext, ← mul_sub, abs_mul, hsign, one_mul]
    by_cases hy1 : y ≤ 1
    · have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨hy0, hy1⟩
      rw [extendedFabius_eq_fabiusReal F hF hyI]
      exact abs_fabiusUniformSpline_sub_fabiusReal_le_all F hF p hyI
    · let z : ℝ := y - 1
      have hzI : z ∈ Icc (0 : ℝ) 1 := by
        dsimp [z]
        constructor <;> linarith
      have hsplineOne : fabiusUniformSpline p y =
          1 - fabiusUniformSpline p z := by
        have hyz : y = 1 + z := by dsimp [z]; ring
        rw [hyz]
        exact fabiusUniformSpline_one_add p hzI.1 hzI.2
      have hextOne : extendedFabius F y = 1 - fabiusReal F z := by
        have hyz : y = 1 + z := by dsimp [z]; ring
        rw [hyz]
        exact extendedFabius_one_add F hF hzI
      rw [hsplineOne, hextOne, sub_sub_sub_cancel_left]
      simpa only [abs_sub_comm] using
        abs_fabiusUniformSpline_sub_fabiusReal_le_all F hF p hzI
  · rw [fabiusUniformSpline_eq_zero_of_nonpos p hx,
      extendedFabius_eq_zero_of_nonpos F hF hx, sub_zero, abs_zero]
    positivity

/-- Quantitative stability of the global spline evaluator when the spline and
the signed Fabius extension are evaluated at different points.  The first
term is the uniform spline error; the second is the global Lipschitz
propagation error. -/
theorem abs_fabiusUniformSpline_sub_extendedFabius_le_add
    (F : BoundedFabius) (hF : IsFabius F)
    (p : ℕ) (x y : ℝ) :
    |fabiusUniformSpline p x - extendedFabius F y| ≤
      ((2 : ℝ) ^ p)⁻¹ + 2 * |x - y| := by
  calc
    |fabiusUniformSpline p x - extendedFabius F y| ≤
        |fabiusUniformSpline p x - extendedFabius F x| +
          |extendedFabius F x - extendedFabius F y| :=
      abs_sub_le _ _ _
    _ ≤ ((2 : ℝ) ^ p)⁻¹ + 2 * |x - y| := by
      gcongr
      · exact abs_fabiusUniformSpline_sub_extendedFabius_le F hF p x
      · simpa only [Real.dist_eq, NNReal.coe_ofNat] using
          (extendedFabius_lipschitzWith_two F hF).dist_le_mul x y

/-- The centered uniform splines converge uniformly on the whole real line to
the signed Fabius extension. -/
theorem fabiusUniformSpline_tendstoUniformly_extendedFabius
    (F : BoundedFabius) (hF : IsFabius F) :
    TendstoUniformly fabiusUniformSpline (extendedFabius F) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hgeom : Tendsto (fun p : ℕ => ((2 : ℝ) ^ p)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1))
  have heps : ∀ᶠ p : ℕ in atTop, ((2 : ℝ) ^ p)⁻¹ < ε :=
    (tendsto_order.1 hgeom).2 ε hε
  filter_upwards [heps] with p hp
  intro x
  exact lt_of_le_of_lt
    (by simpa [Real.dist_eq, abs_sub_comm] using
      abs_fabiusUniformSpline_sub_extendedFabius_le F hF p x)
    hp

/-- The centered uniform splines converge uniformly to every bounded Fabius
function on the closed unit interval.  This packages the pointwise error
estimate `abs_fabiusUniformSpline_sub_fabiusReal_le_all` as Mathlib's standard
uniform-convergence predicate. -/
theorem fabiusUniformSpline_tendstoUniformlyOn_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) :
    TendstoUniformlyOn (fun p : ℕ => fabiusUniformSpline p) (fabiusReal F)
      atTop (Icc (0 : ℝ) 1) := by
  refine (fabiusUniformSpline_tendstoUniformly_extendedFabius
    F hF).tendstoUniformlyOn.congr_right ?_
  intro x hx
  exact extendedFabius_eq_fabiusReal F hF hx

/-- Pointwise form of the global uniform approximation theorem: at every real
input, the centered uniform splines converge to the signed Fabius extension. -/
theorem fabiusUniformSpline_tendsto_extendedFabius
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    Tendsto (fun p : ℕ => fabiusUniformSpline p x) atTop
      (𝓝 (extendedFabius F x)) :=
  (fabiusUniformSpline_tendstoUniformly_extendedFabius F hF).tendsto_at x

/-- Diagonal form of global uniform spline convergence: the evaluation point
may vary with the spline order, provided that it converges. -/
theorem fabiusUniformSpline_tendsto_extendedFabius_of_tendsto
    (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun p : ℕ => fabiusUniformSpline p (u p)) atTop
      (𝓝 (extendedFabius F x)) :=
  (fabiusUniformSpline_tendstoUniformly_extendedFabius F hF).tendsto_comp
    (extendedFabius_contDiff F hF).continuous.continuousAt hu

/-- On the unit interval, the same spline sequence converges pointwise to the
bounded/CDF representative of every Fabius solution. -/
theorem fabiusUniformSpline_tendsto_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun p : ℕ => fabiusUniformSpline p x) atTop
      (𝓝 (fabiusReal F x)) :=
  (fabiusUniformSpline_tendstoUniformlyOn_fabiusReal F hF).tendsto_at hx

/-- Canonical specialization: the centered uniform splines converge uniformly
on `ℝ` to `globalFabius`. -/
theorem fabiusUniformSpline_tendstoUniformly_globalFabius :
    TendstoUniformly fabiusUniformSpline globalFabius atTop := by
  simpa only [globalFabius] using
    fabiusUniformSpline_tendstoUniformly_extendedFabius fabius fabius_spec

/-- The canonical signed global Fabius function is globally `2`-Lipschitz. -/
theorem globalFabius_lipschitzWith_two :
    LipschitzWith 2 globalFabius := by
  simpa only [globalFabius] using
    extendedFabius_lipschitzWith_two fabius fabius_spec

/-! ## A global effective modulus -/

/-- A primitive-recursive modulus for the Fabius functions. -/
def fabiusEffectiveUniformModulus (n : ℕ) : ℕ :=
  2 * n

/-- The modulus `fabiusEffectiveUniformModulus n = 2 * n` is primitive
recursive.  Its `to_comp` form supplies the `Computable` field required by
`effectivelyUniformContinuous_of_lipschitzWith_two`. -/
theorem fabiusEffectiveUniformModulus_primrec :
    Primrec fabiusEffectiveUniformModulus := by
  exact Primrec.nat_mul.comp (Primrec.const 2) Primrec.id

/-! ## The computable-analysis definitions -/

/-- Wikipedia/Grzegorczyk-style effective uniform continuity.  Precision
indices are required to be positive because the reciprocal convention has no
meaningful requirement at `n = 0`. -/
def EffectivelyUniformContinuous (f : ℝ → ℝ) : Prop :=
  ∃ d : ℕ → ℕ, Computable d ∧
    (∀ n : ℕ, 0 < n → 0 < d n) ∧
    ∀ n : ℕ, 0 < n → ∀ x y : ℝ,
      |x - y| < 1 / (d n : ℝ) → |f x - f y| < 1 / (n : ℝ)

/-- A signed-natural numerator code `(positive, negative)`.  At precision
`p` it denotes `(positive - negative) / 2^p`.  This is the standard fast
dyadic-name normal form; allowing two natural parts keeps the representation
primitive recursive without relying on an opaque integer encoding. -/
abbrev DyadicNumerator := ℕ × ℕ

namespace DyadicNumerator

/-- The real represented by a signed numerator at dyadic precision `p`. -/
noncomputable def value (p : ℕ) (c : DyadicNumerator) : ℝ :=
  ((c.1 : ℝ) - c.2) / (2 : ℝ) ^ p

end DyadicNumerator

/-- A real sequence is computable when one recursive signed-natural-pair algorithm
gives dyadic approximations uniformly in the sequence index and precision. -/
def ComputableRealSequence (x : ℕ → ℝ) : Prop :=
  ∃ a : ℕ → ℕ → DyadicNumerator, Computable₂ a ∧
    ∀ i p : ℕ, |x i - (a i p).value p| ≤ ((2 : ℝ) ^ p)⁻¹

/-- The first clause of the cited definition: computable real sequences are
sent to computable real sequences. -/
def SequentiallyComputable (f : ℝ → ℝ) : Prop :=
  ∀ x : ℕ → ℝ, ComputableRealSequence x →
    ComputableRealSequence (fun i => f (x i))

/-- The two clauses defining a computable real function. -/
structure IsComputableRealFunction (f : ℝ → ℝ) : Prop where
  sequentiallyComputable : SequentiallyComputable f
  effectivelyUniformContinuous : EffectivelyUniformContinuous f

/-- A single recursive algorithm approximates `f` on the fast dyadic grid.
At requested output precision `p`, it consumes a numerator at the finer input
grid `p+3`.  The error budget `5·2^(-(p+3))` accounts for one spline-error
unit and four nearest-rounding units; a global `2`-Lipschitz propagation costs
two further units, leaving one unit of slack. -/
structure HasComputableDyadicApproximation (f : ℝ → ℝ) where
  approx : DyadicNumerator → ℕ → DyadicNumerator
  computable : Computable₂ approx
  error : ∀ c p,
    |f (c.value (p + 3)) - (approx c p).value p| ≤
      5 * ((2 : ℝ) ^ (p + 3))⁻¹

private theorem dyadic_bridge_error_bound (p : ℕ) :
    (2 : ℝ) * ((2 : ℝ) ^ (p + 3))⁻¹ +
        5 * ((2 : ℝ) ^ (p + 3))⁻¹ ≤
      ((2 : ℝ) ^ p)⁻¹ := by
  rw [show p + 3 = ((p + 1) + 1) + 1 by omega,
    pow_succ, pow_succ, pow_succ]
  have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
  field_simp
  norm_num

/-- A global `2`-Lipschitz bound and a recursive dyadic evaluator imply
sequential computability in the dyadic-name representation. -/
theorem sequentiallyComputable_of_lipschitzWith_two_of_dyadicApproximation
    {f : ℝ → ℝ} (hlip : LipschitzWith 2 f)
    (hdyadic : HasComputableDyadicApproximation f) :
    SequentiallyComputable f := by
  intro x hx
  obtain ⟨a, haComp, haErr⟩ := hx
  let b : ℕ → ℕ → DyadicNumerator := fun i p =>
    hdyadic.approx (a i (p + 3)) p
  refine ⟨b, ?_, ?_⟩
  · change Computable (fun q : ℕ × ℕ =>
      hdyadic.approx (a q.1 (q.2 + 3)) q.2)
    have hshiftThree : Computable (fun q : ℕ × ℕ => q.2 + 3) :=
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 3)).to_comp
    have hinput : Computable (fun q : ℕ × ℕ => a q.1 (q.2 + 3)) :=
      haComp.comp Computable.fst hshiftThree
    exact hdyadic.computable.comp hinput Computable.snd
  · intro i p
    let c : DyadicNumerator := a i (p + 3)
    have hinput : |x i - c.value (p + 3)| ≤ ((2 : ℝ) ^ (p + 3))⁻¹ :=
      haErr i (p + 3)
    have hprop : |f (x i) - f (c.value (p + 3))| ≤
        2 * |x i - c.value (p + 3)| := by
      simpa only [Real.dist_eq, NNReal.coe_ofNat] using
        hlip.dist_le_mul (x i) (c.value (p + 3))
    have hout : |f (c.value (p + 3)) - (b i p).value p| ≤
        5 * ((2 : ℝ) ^ (p + 3))⁻¹ := by
      simpa [b, c] using hdyadic.error c p
    calc
      |f (x i) - (b i p).value p| ≤
          |f (x i) - f (c.value (p + 3))| +
            |f (c.value (p + 3)) - (b i p).value p| :=
        abs_sub_le (f (x i)) (f (c.value (p + 3))) ((b i p).value p)
      _ ≤ 2 * |x i - c.value (p + 3)| +
          |f (c.value (p + 3)) - (b i p).value p| :=
        add_le_add hprop le_rfl
      _ ≤ 2 * ((2 : ℝ) ^ (p + 3))⁻¹ +
          5 * ((2 : ℝ) ^ (p + 3))⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_left hinput (by norm_num)) hout
      _ ≤ ((2 : ℝ) ^ p)⁻¹ := dyadic_bridge_error_bound p

/-- Any global `2`-Lipschitz function has the explicit recursive modulus
`d(n)=2n`. -/
theorem effectivelyUniformContinuous_of_lipschitzWith_two
    {f : ℝ → ℝ} (hlip : LipschitzWith 2 f) :
    EffectivelyUniformContinuous f := by
  refine ⟨fabiusEffectiveUniformModulus,
    fabiusEffectiveUniformModulus_primrec.to_comp, ?_, ?_⟩
  · intro n hn
    exact Nat.mul_pos (by norm_num) hn
  intro n hn x y hxy
  have hl := hlip.dist_le_mul x y
  simp only [Real.dist_eq] at hl
  rw [fabiusEffectiveUniformModulus] at hxy
  have hxy' : |x - y| < ((2 * (n : ℝ))⁻¹) := by
    simpa [one_div] using hxy
  have hmul : 2 * |x - y| < 2 * ((2 * (n : ℝ))⁻¹) :=
    mul_lt_mul_of_pos_left hxy' (by norm_num)
  have hsimp : 2 * ((2 * (n : ℝ))⁻¹) = (n : ℝ)⁻¹ := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
  rw [hsimp] at hmul
  exact lt_of_le_of_lt hl (by simpa [one_div, abs_sub_comm] using hmul)

/-- Every bounded Fabius solution is effectively uniformly continuous, with
the same explicit recursive modulus `d(n)=2n`. -/
theorem fabiusReal_effectivelyUniformContinuous
    (F : BoundedFabius) (hF : IsFabius F) :
    EffectivelyUniformContinuous (fabiusReal F) :=
  effectivelyUniformContinuous_of_lipschitzWith_two
    (fabiusReal_lipschitzWith_two F hF)

/-- Every signed global Fabius extension is effectively uniformly continuous,
with the same explicit primitive-recursive modulus `d(n)=2n`. -/
theorem extendedFabius_effectivelyUniformContinuous
    (F : BoundedFabius) (hF : IsFabius F) :
    EffectivelyUniformContinuous (extendedFabius F) :=
  effectivelyUniformContinuous_of_lipschitzWith_two
    (extendedFabius_lipschitzWith_two F hF)

/-- The canonical signed global extension is effectively uniformly
continuous with modulus `d(n)=2n`. -/
theorem globalFabius_effectivelyUniformContinuous :
    EffectivelyUniformContinuous globalFabius := by
  simpa only [globalFabius] using
    extendedFabius_effectivelyUniformContinuous fabius fabius_spec

/-- Effective uniform continuity in the reciprocal convention: for positive
`n`, input distance less than `1 / d(n)` forces output distance less than
`1 / n`, where `d(n) = 2n` is primitive recursive. -/
theorem globalFabius_effectively_uniformly_continuous
    (n : ℕ) (hn : 0 < n) {x y : ℝ}
    (hxy : |x - y| < 1 / (fabiusEffectiveUniformModulus n : ℝ)) :
    |globalFabius x - globalFabius y| < 1 / (n : ℝ) := by
  have hlip := globalFabius_lipschitzWith_two.dist_le_mul x y
  have hlip' : |globalFabius x - globalFabius y| ≤
      2 * |x - y| := by
    simpa only [Real.dist_eq, abs_sub_comm, NNReal.coe_ofNat] using hlip
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (fabiusEffectiveUniformModulus n : ℝ) = 2 * n := by
    simp [fabiusEffectiveUniformModulus]
  rw [hd] at hxy
  calc
    |globalFabius x - globalFabius y| ≤ 2 * |x - y| := by
      exact hlip'
    _ < 2 * (1 / (2 * (n : ℝ))) :=
      mul_lt_mul_of_pos_left hxy (by norm_num)
    _ = 1 / (n : ℝ) := by field_simp

end Fabius
