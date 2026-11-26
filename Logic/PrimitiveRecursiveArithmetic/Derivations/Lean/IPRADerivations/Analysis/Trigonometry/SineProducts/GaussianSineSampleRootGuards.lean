import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionCayleyMargins
import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineSampleRootList
import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineSquaredRootSeparation

/-!
# Uniform guards for the sampled odd sine roots

A single cofinal clock provides all sine margins and all pairwise
root separations on the original divided-angle sample list. These
certificates discharge both numerical hypotheses of reconstruction.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineSampleRootGuards

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentDivisionAngles (modulus)
open GaussianArctangentDivisionAngleResidual (rootSample mesh index mesh_positive positiveBudget)
open GaussianArctangentDivisionCayleyMargins (precision sine_lower_at squared_sine_gap_at)
open GaussianCoefficientNameBounds (unit)
open GaussianNameReciprocal (lower lower_congr)
open GaussianRationalHorner (qmul evaluate positive_product)
open GaussianRationalMetric (bounded qsub distanceBounded)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReconstruction (product)
open GaussianRationalSeparatedDeflation (separation separationFrom)
open GaussianRationalSeparatedReconstruction (errorNumerator)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianSineSampleRootList (roots roots_at roots_length subst_roots sineMargins reconstruction normalization_at_four)
open GaussianSineSquaredPolynomial (coefficients)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sineDenominator (J : PTm n) : PTm n := num 4*modulus J
def rootDenominator (J : PTm n) : PTm n :=
  GaussianArctangentCayleySquareGap.separationDenominator (sineDenominator J)
def fine (p J : PTm n) : Fm PTm n := le (num 28*modulus J) (unit (precision p))
def clock (p J : PTm n) : PTm n := p+num 28*modulus J

@[simp] theorem subst_sineDenominator {l : ℕ} (σ : Fin n → PTm l) (J : PTm n) :
    Syn.subst σ (sineDenominator J) = sineDenominator (Syn.subst σ J) := by
  simp [sineDenominator]

@[simp] theorem subst_rootDenominator {l : ℕ} (σ : Fin n → PTm l) (J : PTm n) :
    Syn.subst σ (rootDenominator J) = rootDenominator (Syn.subst σ J) := by
  simp [rootDenominator,GaussianArctangentCayleySquareGap.separationDenominator]

@[simp] theorem subst_fine {l : ℕ} (σ : Fin n → PTm l) (p J : PTm n) :
    (fine p J).subst σ = fine (Syn.subst σ p) (Syn.subst σ J) := by
  simp [fine,precision,GaussianArctangentInverseCayleySamples.inversePrecision,
    GaussianArctangentNamedInverse.precision,GaussianArctangentNamedInverse.modulus,
    GaussianArctangentNamedExtension.clock,two,one]

@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (p J : PTm n) :
    Syn.subst σ (clock p J) = clock (Syn.subst σ p) (Syn.subst σ J) := by
  simp [clock]

theorem sine_denominator_positive (J : PTm n) : Γ ⊢[PRAAx] le one (sineDenominator J) :=
  positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring)) (zero_lt_succ _)

theorem root_denominator_positive (J : PTm n) : Γ ⊢[PRAAx] le one (rootDenominator J) := by
  have h := sine_denominator_positive (Γ := Γ) J
  exact positive_product _ _ (positive_product _ _ (positive_product _ _
    (le_of_eq_add (d := num 3) (by ipra_ring)) h) h) h

theorem clock_later (p J : PTm n) : Γ ⊢[PRAAx] le p (clock p J) := le_add_right _ _

theorem precision_later (p : PTm n) : Γ ⊢[PRAAx] le p (precision p) := by
  unfold precision GaussianArctangentInverseCayleySamples.inversePrecision
  apply le_trans _ (GaussianArctangentNamedInverse.precision_later _)
  unfold GaussianArctangentNamedExtension.clock GaussianArctangentNamedCayley.queryPrecision
    GaussianRadiusExponentialName.inputPrecision
  exact le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) (le_add_right _ _)

theorem clock_fine (p J : PTm n) : Γ ⊢[PRAAx] fine (clock p J) J :=
  le_trans (le_add_left _ _)
    (le_trans (LeanProofs.IPRA.Foundations.DyadicGain.amplitude_absorb (clock p J))
      (GaussianExponentialReference.unit_monotone (precision_later (clock p J))))

theorem sine_margins (p J z : PTm n) (hf : Γ ⊢[PRAAx] fine p J) :
    Γ ⊢[PRAAx] sineMargins p J z (sineDenominator J) := by
  refine .allI (.impI ?_)
  let P := Syn.shift p
  let N := Syn.shift J
  let Z := Syn.shift z
  let j : PTm (n+1) := var 0
  let Δ := lt j N :: Γ.map Fm.shift
  have hf' : Δ ⊢[PRAAx] fine P N := by simpa [Δ,Fm.shift,Syn.shift,P,N,j] using hf.shift.wk
  have smaller : Δ ⊢[PRAAx] le (num 14*modulus N) (unit (precision P)) :=
    le_trans (le_of_eq_add (d := num 14*modulus N) (by ipra_ring)) hf'
  simpa [sineMargins,Δ,Syn.shift,P,N,Z,j,sineDenominator] using
    sine_lower_at (Γ := Δ) P (succ j) N Z (zero_lt_succ j) Prf.hyp0 smaller

theorem root_gap_at (p k l J z : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hkl : Γ ⊢[PRAAx] lt k l)
    (hJ : Γ ⊢[PRAAx] le l J) (hf : Γ ⊢[PRAAx] fine p J) :
    Γ ⊢[PRAAx] lower (qsub (rootSample p l J z) (rootSample p k J z)) (rootDenominator J) :=
  GaussianSineSquaredRootSeparation.root_gap (mesh p k J z) (index p k J z) (mesh p l J z) (index p l J z)
    (rootDenominator J) (mesh_positive p k J z) (mesh_positive p l J z) (root_denominator_positive J)
    (squared_sine_gap_at p k l J z hk hkl hJ hf)

private theorem root_separation_from (p J z i : PTm n) (hf : Γ ⊢[PRAAx] fine p J) :
    Γ ⊢[PRAAx] separationFrom (roots p J z) (rootDenominator J) i := by
  refine .allI (.impI (.impI ?_))
  let P := Syn.shift p
  let N := Syn.shift J
  let Z := Syn.shift z
  let I := Syn.shift i
  let j : PTm (n+1) := var 0
  let Δ := lt I j :: lt j (length (roots P N Z)) :: Γ.map Fm.shift
  have hf' : Δ ⊢[PRAAx] fine P N := by simpa [Δ,Fm.shift,Syn.shift,P,N,Z,I,j] using hf.shift.wk.wk
  have order : Δ ⊢[PRAAx] lt I j := Prf.hyp0
  have hj : Δ ⊢[PRAAx] lt j N := lt_congr (.eqRefl _) (roots_length P N Z) Prf.hyp1
  have hi := lt_of_lt_of_le order (le_of_lt hj)
  have succOrder : Δ ⊢[PRAAx] lt (succ I) (succ j) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one order)
  have raw := root_gap_at P (succ I) (succ j) N Z (zero_lt_succ I) succOrder hj hf'
  have compare := qsub_congr (roots_at P N Z j hj).eqSymm (roots_at P N Z I hi).eqSymm
  simpa [separationFrom,Δ,Syn.shift,P,N,Z,I,j] using lower_congr compare (.eqRefl _) raw

theorem root_separation (p J z : PTm n) (hf : Γ ⊢[PRAAx] fine p J) :
    Γ ⊢[PRAAx] separation (roots p J z) (rootDenominator J) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] fine (Syn.shift p) (Syn.shift J) :=
    by simpa [Fm.shift,Syn.shift] using hf.shift
  simpa only [separation,subst_roots,subst_rootDenominator,Syn.shift] using
    root_separation_from (Syn.shift p) (Syn.shift J) (Syn.shift z) (var 0) hs

theorem reconstruction_at (p J z y B : PTm n) (hf : Γ ⊢[PRAAx] fine p J) (hy : Γ ⊢[PRAAx] bounded y B one) :
    Γ ⊢[PRAAx] distanceBounded (evaluate (coefficients J) y) (product (roots p J z) J y)
      (errorNumerator (sineDenominator J*positiveBudget J) (rootDenominator J) J (B+num 8) J) (unit p) :=
  reconstruction _ _ _ _ _ _ _ (sine_denominator_positive J) (root_denominator_positive J)
    (sine_margins p J z hf) (root_separation p J z hf) hy

theorem normalization_at (p J z : PTm n) (hf : Γ ⊢[PRAAx] fine p J) :
    Γ ⊢[PRAAx] distanceBounded (naturalPoint (succ (two*J))) (product (roots p J z) J (naturalPoint (num 4)))
      (errorNumerator (sineDenominator J*positiveBudget J) (rootDenominator J) J (num 4+num 8) J) (unit p) :=
  normalization_at_four _ _ _ _ _ (sine_denominator_positive J) (root_denominator_positive J)
    (sine_margins p J z hf) (root_separation p J z hf)

theorem actual_odd_sample_root_margins_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sineMargins (clock (var 0) (var 1)) (var 1) (var 2) (sineDenominator (var 1)) ⋏
      separation (roots (clock (var 0) (var 1)) (var 1) (var 2)) (rootDenominator (var 1))) :=
  closeUniv 3 (.andI (sine_margins _ _ _ (clock_fine _ _)) (root_separation _ _ _ (clock_fine _ _)))

end LeanProofs.IPRA.Analysis.GaussianSineSampleRootGuards
