import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithmHalfDiskBound
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmTaylorRemainder
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# The original logarithm in the Glaisher increment

The logarithm of `(N+1)/N` uses the original positive rational logarithm
name. For `N ≥ 2`, its actual samples have the Mercator remainder about
the encoded rational `1/N` at every encoded truncation order.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherLogarithm

open_ipra
open ComplexLogarithmRemainder (normSq normSq_one oneCode)
open GaussianFiniteLogarithmTaylorRemainder (numerator denominator denominator_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRightHalfPlaneLogarithmOffset (offset signedImag)
open GaussianPositiveRationalLogarithm (logF data)
open GaussianLocalLogarithmTaylorRemainder (polynomial)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def unitOffset (N : PTm n) : PTm n := offset (succ N) zero N zero

theorem unit_offset (N : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (unitOffset N) oneCode := by
  apply GaussianRootAlgebra.equal_of_values
  · simp only [unitOffset,offset,ComplexLogarithmRemainder.eval_re_code,ZT.toZ_sub,ZT.toZ_ofNat,
      GaussianRootAlgebra.re_one,Q.mk_succ,map_add,map_one]
    ring
  · simp only [unitOffset,offset,signedImag,ComplexLogarithmRemainder.eval_im_code,
      GaussianRootAlgebra.im_one]
    simp [ZT.toZ, natEq (RationalArithmetic.select_zero (Γ := Γ) zero zero zero (.eqRefl _))]

theorem unit_offset_bound (N : PTm n) :
    Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (unitOffset N) one := by
  exact le_congr ((GaussianRootAlgebra.normSq_equal (unit_offset N)).eqTrans normSq_one).eqSymm
    (one_mul one).eqSymm (le_refl one)

theorem half_disk_source (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithmMercatorHalfDisk.source (succ N) zero N zero one :=
  .andI (.andI (.andI (zero_lt_succ _) (.orI₁ (.eqRefl _))) (le_trans (le_succ_self one) hN))
    (.andI (unit_offset_bound N) (le_congr (by ipra_ring) (.eqRefl _) hN))

theorem original_logarithm_local (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] crossEquivalent logF GaussianLocalLogarithmName.pointF (data (succ N) N)
      (GaussianLocalLogarithmName.data (unitOffset N) one N) := by
  let F := GaussianRightHalfPlaneLogarithm.nameF
  let x := GaussianRightHalfPlaneLogarithm.data (succ N) zero N zero
  have hs := half_disk_source N hN
  have axis := GaussianRightHalfPlaneLogarithm.positive_axis (succ N) N zero hs.andE₁
  have localLog := GaussianRightHalfPlaneLogarithmHalfDiskBound.coincidence (succ N) zero N zero one hs
  exact cross_trans logF F GaussianLocalLogarithmName.pointF (data (succ N) N) x _
    (cross_symm F logF x (data (succ N) N) axis) localLog

theorem original_logarithm_rate (N m : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] independentRate logF constantF (data (succ N) N)
      (polynomial m oneCode N) (numerator one m) (denominator one N m) := by
  let F := GaussianLocalLogarithmName.pointF
  let x := GaussianLocalLogarithmName.data (unitOffset N) one N
  let y := polynomial m (unitOffset N) N
  let y' := polynomial m oneCode N
  have hs := GaussianRightHalfPlaneLogarithmMercatorHalfDisk.local_source (succ N) zero N zero one
    (half_disk_source N hN)
  have hp := GaussianLocalLogarithmTaylorRemainder.radius_strict (unitOffset N) one N hs
  have hr := GaussianLocalLogarithmTaylorRemainder.rate m (unitOffset N) one N hs
  have pointEqual := GaussianGammaFiniteValueProperness.fraction_equal _ _ N hs.andE₁ (unit_offset N)
  have polynomialEqual : Γ ⊢[PRAAx] y ≐ y' := by
    unfold y y' polynomial
    simpa using Prf.eqCongr1 (GaussianFiniteLogarithmPolynomial.value (Syn.shift m) (var 0)) pointEqual
  have values := GaussianGammaWeierstrassApproximant.constant_data_cross y y' polynomialEqual
  exact GaussianNamedRateTransport.transport F constantF logF constantF x y _ y'
    (numerator one m) (denominator one N m) (denominator_positive one N m hs.andE₁ hp) hr
    (original_logarithm_local N hN) (cross_symm constantF constantF y y' values)

theorem actual_Glaisher_logarithm_Mercator_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le two (var 0) ⟶ independentRate logF constantF (data (succ (var 0)) (var 0))
      (polynomial (var 1) oneCode (var 0)) (numerator one (var 1)) (denominator one (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_logarithm_rate _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherLogarithm
