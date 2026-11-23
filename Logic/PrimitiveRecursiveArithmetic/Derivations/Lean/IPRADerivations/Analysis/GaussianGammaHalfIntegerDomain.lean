import IPRADerivations.Analysis.GaussianGammaDensityDomain
import IPRADerivations.Analysis.GaussianEulerQuadraticGamma

/-!
# Source-derived half-integer trajectory for Gaussian moments

The original native trajectory starts at 1/2 and advances by every
internal N. Its original positive margin remains two and its disk
radius is 1+N. The native doubled Euler power coefficient is exactly
the original natural point 2N, before any analytic value theorem.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfIntegerDomain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (source)
open GaussianRationalHorner (ofGaussian canonical_unique represents_congr ofGaussian_represents)
open ComplexLogarithmRemainder (oneCode scale re im)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def argument (N : PTm n) : PTm n := GaussianGammaShiftTrajectory.point oneCode two N
def radius (N : PTm n) : PTm n := one+N
@[simp] theorem subst_argument {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (argument N) = argument (Syn.subst σ N) := by simp [argument]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (radius N) = radius (Syn.subst σ N) := by simp [radius]

theorem half_source : Γ ⊢[PRAAx] source (oneCode : PTm n) one two two := by
  have hp : Γ ⊢[PRAAx] le one (two : PTm n) := zero_lt_succ one
  have disk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (oneCode : PTm n) (one*two) :=
    le_congr ((by ipra_ring : Γ ⊢[PRAAx] one*one ≐ one).eqTrans ComplexLogarithmRemainder.normSq_one.eqSymm) (by ipra_ring)
      (AnalyticNumberTheory.PhiLower.le_mul_mono hp hp)
  have margin : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower (oneCode : PTm n) two two := by
    apply zle_of_toZ (ConciseIPRA.PTm.zero : PTm n)
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_one]
    ipra_simps
    ring
  exact .andI (.andI hp (.andI (.andI hp disk) margin)) (le_refl one)

theorem original_source (N : PTm n) : Γ ⊢[PRAAx] source (argument N) (radius N) two two :=
  GaussianGammaDensityDomain.shifted_source oneCode one two two N half_source

theorem quadratic_source (N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    GaussianEulerQuadraticGamma.source (argument N) (radius N) two two c d := .andI (original_source N) (.andI hc hd)

theorem doubled_coefficient (N : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.coefficient (GaussianEulerSquareKernel.doubled (argument N) two) two ≐
      GaussianRationalNaturalScale.naturalPoint (two*N) := by
  have hp : Γ ⊢[PRAAx] le one (two : PTm n) := zero_lt_succ one
  have lhs := GaussianRationalMetric.qsub_represents _ _ _ _ two hp
    (ofGaussian_represents (GaussianEulerSquareKernel.doubled (argument N) two) two hp)
    (GaussianRationalReciprocal.qone_represents_scaled two)
  have rhs := represents_congr (Γ := Γ) (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (one_mul two)
    (GaussianRationalHorner.represents_rescale (GaussianRationalNaturalScale.naturalPoint (two*N))
      (scale (two*N) oneCode) one two (GaussianRationalNaturalScale.natural_point_represents (two*N)))
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) hp ?_ rhs
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) lhs
  have pt := GaussianGammaShiftTrajectory.point_native (Γ := Γ) oneCode two N
  have dt := GaussianEulerSquareKernel.doubled_parameter_equal (Γ := Γ) (argument N) two
  apply GaussianRootAlgebra.equal_of_values
  · simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.re_scale]
    rw [GaussianRootAlgebra.equal_re dt]
    simp only [GaussianRootAlgebra.re_add]
    change ZT.toZ Γ (re (GaussianGammaShiftTrajectory.point oneCode two N)) +
      ZT.toZ Γ (re (GaussianGammaShiftTrajectory.point oneCode two N)) - _ = _
    rw [GaussianRootAlgebra.equal_re pt]
    simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.re_one]
    ipra_simps
    ring
  · simp only [GaussianRootAlgebra.im_sub,GaussianRootAlgebra.im_scale]
    rw [GaussianRootAlgebra.equal_im dt]
    simp only [GaussianRootAlgebra.im_add]
    change ZT.toZ Γ (im (GaussianGammaShiftTrajectory.point oneCode two N)) +
      ZT.toZ Γ (im (GaussianGammaShiftTrajectory.point oneCode two N)) - _ = _
    rw [GaussianRootAlgebra.equal_im pt]
    simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.im_one]
    ipra_simps
    ring

theorem actual_original_half_integer_quadratic_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ GaussianEulerQuadraticGamma.source
      (argument (var 0)) (radius (var 0)) two two (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (quadratic_source _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_half_integer_Gaussian_power_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (GaussianEulerIntegrandName.coefficient (GaussianEulerSquareKernel.doubled (argument (var 0)) two) two ≐
      GaussianRationalNaturalScale.naturalPoint (two*(var 0))) := closeUniv 1 (doubled_coefficient _)

end LeanProofs.IPRA.Analysis.GaussianGammaHalfIntegerDomain
