import FabiusFunction.PeriodicFourier
import FabiusFunction.FabiusExplicitSharpTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The periodic obstruction to the uncorrected Wikipedia asymptotic

The centered periodic correction is nonconstant, and its exact lower-Lambert
phase visits every sufficiently far integer translate of any fixed phase.
Consequently this oscillation does not tend to zero as `x → 0⁺`, and in
particular cannot be absorbed into an `O(1 / (-log x))` error.

The final theorems turn this into a source-facing statement: once a corrected
asymptotic with that error is known, deleting the periodic term makes the same
error estimate impossible.
-/

set_option autoImplicit false

open Filter Asymptotics Set

namespace Fabius

/-- The positive lower-Lambert phase exactly inverts `y ↦ y 2⁻ʸ` after the
branch point `log(2) y = 1`. -/
lemma fabiusLambertPhase_inverse_on_lower_branch
    {y : ℝ} (hy : 1 < Real.log 2 * y) :
    fabiusLambertPhase (y * (2 : ℝ) ^ (-y)) = y := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy0 : 0 < y := by nlinarith
  let u : ℝ := Real.log 2 * y
  let x : ℝ := y * (2 : ℝ) ^ (-y)
  have hu : 1 < u := hy
  have hx : 0 < x := by
    dsimp [x]
    exact mul_pos hy0 (Real.rpow_pos_of_pos (by norm_num) _)
  have hrpow : (2 : ℝ) ^ (-y) = Real.exp (-u) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [u]
    ring
  have hux : Real.log 2 * x = u * Real.exp (-u) := by
    dsimp [x, u]
    rw [hrpow]
    ring
  have hlt : u * Real.exp (-u) < Real.exp (-1) := by
    have hexp : u < Real.exp (u - 1) := by
      have h := Real.add_one_lt_exp (by linarith : u - 1 ≠ 0)
      simpa only [sub_add_cancel] using h
    have hmul := mul_lt_mul_of_pos_right hexp (Real.exp_pos (-u))
    calc
      u * Real.exp (-u) < Real.exp (u - 1) * Real.exp (-u) := hmul
      _ = Real.exp (-1) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hz : -(Real.log 2 * x) ∈ Ioo (-Real.exp (-1)) 0 := by
    constructor
    · rw [hux]
      linarith
    · exact neg_lt_zero.mpr (mul_pos hL hx)
  have hw : -u < -1 := neg_lt_neg hu
  have heq : (-u) * Real.exp (-u) = -(Real.log 2 * x) := by
    rw [hux]
    ring
  have hunique := lowerLambertW_unique hz hw heq
  unfold fabiusLambertPhase paperLambertN
  rw [← hunique]
  dsimp [u]
  field_simp [hL.ne']

/-- Nonconstancy supplies a phase at which the centered correction is
nonzero. -/
lemma exists_negativeLaplacePsi_ne_zero :
    ∃ a : ℝ, negativeLaplacePsi a ≠ 0 := by
  by_contra h
  apply negativeLaplacePsi_not_constant
  refine ⟨0, fun t => ?_⟩
  by_contra ht
  exact h ⟨t, ht⟩

/-- The periodic fluctuation sampled at the exact lower-Lambert phase does
not tend to zero as `x → 0⁺`.  This is the intrinsic obstruction behind all
of the rate-specific results below. -/
theorem negativeLaplacePsi_comp_fabiusLambertPhase_not_tendsto_zero :
    ¬ Tendsto (negativeLaplacePsi ∘ fabiusLambertPhase)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  intro hzero
  obtain ⟨a, ha⟩ := exists_negativeLaplacePsi_ne_zero
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / Real.log 2 - a)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : 1 < Real.log 2 * (a + (N : ℝ)) := by
    have hN' : 1 / Real.log 2 < a + (N : ℝ) := by linarith
    have hmul := mul_lt_mul_of_pos_left hN' hlogTwo
    calc
      1 = Real.log 2 * (1 / Real.log 2) := by field_simp [hlogTwo.ne']
      _ < Real.log 2 * (a + (N : ℝ)) := hmul
  let y : ℕ → ℝ := fun n => a + ((N + n : ℕ) : ℝ)
  let x : ℕ → ℝ := fun n => y n * (2 : ℝ) ^ (-y n)
  have hyLower : ∀ n : ℕ, 1 < Real.log 2 * y n := by
    intro n
    dsimp [y]
    push_cast
    nlinarith [hbase]
  have hyPos : ∀ n : ℕ, 0 < y n := by
    intro n
    have := hyLower n
    nlinarith
  have hxPos : ∀ n : ℕ, 0 < x n := by
    intro n
    dsimp [x]
    exact mul_pos (hyPos n) (Real.rpow_pos_of_pos (by norm_num) _)
  have hyTop : Tendsto y atTop atTop := by
    simpa [y, Nat.cast_add, add_assoc] using
      (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (a + (N : ℝ)) + (n : ℝ)) atTop atTop)
  have hxZero : Tendsto x atTop (nhds 0) := by
    have hdecay :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (1 : ℝ) (Real.log 2) hlogTwo
    apply (hdecay.comp hyTop).congr'
    filter_upwards with n
    dsimp [x]
    rw [Real.rpow_one, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 2
    ring
  have hxWithin : Tendsto x atTop (nhdsWithin 0 (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hxZero, Eventually.of_forall hxPos⟩
  have hphase : ∀ n : ℕ, fabiusLambertPhase (x n) = y n := by
    intro n
    exact fabiusLambertPhase_inverse_on_lower_branch (hyLower n)
  have hperiod : ∀ n : ℕ, negativeLaplacePsi (y n) = negativeLaplacePsi a := by
    intro n
    have hp : Function.Periodic negativeLaplacePsi 1 :=
      negativeLaplacePsi_add_one
    simpa [y] using hp.nat_mul (N + n) a
  have hcomposed : ∀ n : ℕ,
      (negativeLaplacePsi ∘ fabiusLambertPhase) (x n) =
        negativeLaplacePsi a := by
    intro n
    simp only [Function.comp_apply, hphase n, hperiod n]
  have hpsiZero : Tendsto
      (fun n : ℕ => (negativeLaplacePsi ∘ fabiusLambertPhase) (x n))
      atTop (nhds 0) :=
    hzero.comp hxWithin
  have hpsiA : Tendsto
      (fun n : ℕ => (negativeLaplacePsi ∘ fabiusLambertPhase) (x n))
      atTop (nhds (negativeLaplacePsi a)) := by
    simpa only [hcomposed] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => negativeLaplacePsi a)
        atTop (nhds (negativeLaplacePsi a)))
  exact ha (tendsto_nhds_unique hpsiA hpsiZero)

/-- The periodic fluctuation sampled at the exact lower-Lambert phase cannot
be hidden in an `O(1 / (-log x))` remainder at `x → 0⁺`. -/
theorem negativeLaplacePsi_comp_fabiusLambertPhase_not_isBigO :
    ¬ ((negativeLaplacePsi ∘ fabiusLambertPhase) =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => (-Real.log x)⁻¹)) := by
  intro hO
  apply negativeLaplacePsi_comp_fabiusLambertPhase_not_tendsto_zero
  have hlog : Tendsto (fun x : ℝ => -Real.log x)
      (nhdsWithin 0 (Ioi 0)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  exact hO.trans_tendsto (tendsto_inv_atTop_zero.comp hlog)

/-- If an error scale tends to zero, an approximation containing the exact
periodic correction and an approximation omitting it cannot both have that
error scale. -/
theorem fabiusWikipediaElementaryMain_error_not_isBigO_of_corrected_of_tendsto
    (q g : ℝ → ℝ)
    (hg : Tendsto g (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hcorrected :
      (fun x : ℝ => q x - fabiusExplicitCorrectedWikipediaMain x)
          =O[nhdsWithin 0 (Ioi 0)] g) :
    ¬ ((fun x : ℝ => q x - fabiusWikipediaElementaryMain x)
        =O[nhdsWithin 0 (Ioi 0)] g) := by
  intro huncorrected
  apply negativeLaplacePsi_comp_fabiusLambertPhase_not_tendsto_zero
  have hdiff := huncorrected.sub hcorrected
  apply (hdiff.congr' ?_ Filter.EventuallyEq.rfl).trans_tendsto hg
  filter_upwards with x
  simp only [fabiusExplicitCorrectedWikipediaMain, Function.comp_apply]
  ring

/-- Once an approximation contains the exact periodic correction with an
`O(1 / (-log x))` remainder, deleting that correction cannot preserve the
same error estimate. -/
theorem fabiusWikipediaElementaryMain_error_not_isBigO_of_corrected
    (q : ℝ → ℝ)
    (hcorrected :
      (fun x : ℝ => q x - fabiusExplicitCorrectedWikipediaMain x)
          =O[nhdsWithin 0 (Ioi 0)] (fun x : ℝ => (-Real.log x)⁻¹)) :
    ¬ ((fun x : ℝ => q x - fabiusWikipediaElementaryMain x)
        =O[nhdsWithin 0 (Ioi 0)] (fun x : ℝ => (-Real.log x)⁻¹)) := by
  apply fabiusWikipediaElementaryMain_error_not_isBigO_of_corrected_of_tendsto
    q (fun x : ℝ => (-Real.log x)⁻¹) ?_ hcorrected
  have hlog : Tendsto (fun x : ℝ => -Real.log x)
      (nhdsWithin 0 (Ioi 0)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  exact tendsto_inv_atTop_zero.comp hlog

/-- In particular, the normalized saddle-kernel estimate proves that the
literal uncorrected Wikipedia expression does not have the claimed
`O(1 / (-log x))` error. -/
theorem log_fabius_sub_WikipediaElementaryMain_not_isBigO_of_kernelMass
    (F : BoundedFabius) (hF : IsFabius F)
    (hkernel :
      (fun t : ℝ => fabiusSaddleKernelMass F ((2 : ℝ) ^ (-t))
          (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
          (fabiusLambertPhase ((2 : ℝ) ^ (-t))) - 1) =O[atTop]
        (fun t : ℝ => (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹)) :
    ¬ ((fun x : ℝ => Real.log (fabiusReal F x) -
          fabiusWikipediaElementaryMain x) =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => (-Real.log x)⁻¹)) :=
  fabiusWikipediaElementaryMain_error_not_isBigO_of_corrected
    (fun x : ℝ => Real.log (fabiusReal F x))
    (log_fabius_sub_explicitCorrectedWikipediaMain_isBigO_of_kernelMass
      F hF hkernel)

end Fabius
