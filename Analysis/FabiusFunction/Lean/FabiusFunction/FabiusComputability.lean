import FabiusFunction.GlobalDyadic
import FabiusFunction.GlobalBounds
import FabiusFunction.Regularity
import FabiusFunction.FabiusUniformSpline
import FabiusFunction.WeakConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Computability.Partrec

/-!
# Computability of the Fabius function

This module formalizes the two clauses in the computable-analysis definition
of a computable real function: effective uniform continuity and preservation
of computable sequences.  The analytic clause is obtained from the global
derivative equation.  The algorithmic clause evaluates finite centered
splines on dyadic grids and rounds them with an explicit error bound.
-/

open scoped BigOperators
open Set

namespace Fabius

set_option autoImplicit false

/-! ## A global effective modulus -/

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

/-- The centered order-`p` uniform spline approximates the bounded Fabius
function with the explicit error `2⁻ᵖ`. -/
theorem abs_fabiusUniformSpline_sub_fabiusReal_le
    (F : BoundedFabius) (hF : IsFabius F) (p : ℕ) (hp : 0 < p)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |fabiusUniformSpline p x - fabiusReal F x| ≤ ((2 : ℝ) ^ p)⁻¹ := by
  let δ : ℝ := 1 / (2 : ℝ) ^ (p + 1)
  have hs := ProbabilityRepresentation.uniformCenteredPartialCDF_sandwich p x
  rw [← ProbabilityRepresentation.fabiusUniformSpline_eq_centeredPartialCDF p hp hx,
    ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal F hF,
    ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal F hF] at hs
  have hleft := (fabiusReal_lipschitzWith_two F hF).dist_le_mul (x - δ) x
  have hright := (fabiusReal_lipschitzWith_two F hF).dist_le_mul (x + δ) x
  have hδ : 2 * |δ| = ((2 : ℝ) ^ p)⁻¹ := by
    dsimp [δ]
    rw [abs_of_nonneg (by positivity), pow_succ]
    field_simp
  have hleft' : |fabiusReal F (x - δ) - fabiusReal F x| ≤
      ((2 : ℝ) ^ p)⁻¹ := by
    rw [Real.dist_eq, Real.dist_eq] at hleft
    calc
      |fabiusReal F (x - δ) - fabiusReal F x| ≤ 2 * |x - δ - x| := by
        simpa only [NNReal.coe_ofNat] using hleft
      _ = ((2 : ℝ) ^ p)⁻¹ := by
        rw [show x - δ - x = -δ by ring, abs_neg, hδ]
  have hright' : |fabiusReal F (x + δ) - fabiusReal F x| ≤
      ((2 : ℝ) ^ p)⁻¹ := by
    rw [Real.dist_eq, Real.dist_eq] at hright
    calc
      |fabiusReal F (x + δ) - fabiusReal F x| ≤ 2 * |x + δ - x| := by
        simpa only [NNReal.coe_ofNat] using hright
      _ = ((2 : ℝ) ^ p)⁻¹ := by
        rw [show x + δ - x = δ by ring, hδ]
  rw [abs_le]
  constructor
  · have hleftLower : -((2 : ℝ) ^ p)⁻¹ ≤
        fabiusReal F (x - δ) - fabiusReal F x :=
      (abs_le.mp hleft').1
    dsimp [δ] at hs
    linarith [hs.1]
  · have hrightUpper : fabiusReal F (x + δ) - fabiusReal F x ≤
        ((2 : ℝ) ^ p)⁻¹ := (abs_le.mp hright').2
    dsimp [δ] at hs
    linarith [hs.2]

/-- The same explicit spline error estimate in every degree.  At degree zero,
both the elementary step spline and the bounded Fabius function take values in
`[0,1]`, so the right-hand side is exactly one. -/
theorem abs_fabiusUniformSpline_sub_fabiusReal_le_all
    (F : BoundedFabius) (hF : IsFabius F) (p : ℕ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |fabiusUniformSpline p x - fabiusReal F x| ≤ ((2 : ℝ) ^ p)⁻¹ := by
  cases p with
  | zero =>
      have hspline : fabiusUniformSpline 0 x ∈ Icc (0 : ℝ) 1 := by
        rw [ProbabilityRepresentation.fabiusUniformSpline_zero_eq_centeredPartialCDF_of_mem_Icc
          hx]
        exact ⟨ProbabilityTheory.cdf_nonneg _ _, ProbabilityTheory.cdf_le_one _ _⟩
      rw [pow_zero, inv_one, abs_le]
      constructor
      · linarith [hspline.1, fabiusReal_le_one F x]
      · linarith [hspline.2, fabiusReal_nonneg F x]
  | succ p =>
      exact abs_fabiusUniformSpline_sub_fabiusReal_le F hF (p + 1) (by omega) hx

/-- The canonical signed global Fabius function is globally `2`-Lipschitz. -/
theorem globalFabius_lipschitzWith_two :
    LipschitzWith 2 globalFabius := by
  simpa only [globalFabius] using
    extendedFabius_lipschitzWith_two fabius fabius_spec

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

/-- The canonical signed global extension is effectively uniformly
continuous with modulus `d(n)=2n`. -/
theorem globalFabius_effectivelyUniformContinuous :
    EffectivelyUniformContinuous globalFabius :=
  effectivelyUniformContinuous_of_lipschitzWith_two
    globalFabius_lipschitzWith_two

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
