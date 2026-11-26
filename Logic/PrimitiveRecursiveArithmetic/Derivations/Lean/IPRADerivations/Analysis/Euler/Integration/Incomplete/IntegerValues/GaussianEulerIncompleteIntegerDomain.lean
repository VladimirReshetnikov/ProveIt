import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteName
import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFactorialValues

/-!
# Original incomplete Euler inputs along the positive integer trajectory

The parameter is the actual native successor program already used for
Gamma factorial values. Its computed disk is derived by finite
induction, and its real part is the native value 1+i. Thus margin one
and the source of both original incomplete names hold at every internal
index. The base and successor input codes retain the literal original
shift constructor; no recurrence or integer-value formula is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteIntegerDomain

open_ipra
open GaussianGammaFactorialValues (argument radius)
open GaussianGammaEulerHeadShift (shifted)
open ComplexLogarithmRemainder (oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (a b : PTm n) : Fm PTm n := le one a ⋏ le one b
def data (i a b : PTm n) : PTm n :=
  GaussianEulerIncompleteName.data (argument i) (radius i) one one a b

ipra_subst source
ipra_subst data

theorem trajectory_source (i : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalExponent.source (argument i) (radius i) one :=
  GaussianGammaShiftTrajectory.point_source oneCode one one i GaussianGammaNormalization.unit_source

theorem native_real_lower (i : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.realLower (argument i) one one := by
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (argument i)
      (GaussianGammaEulerHeadLower.translated oneCode one i) :=
    GaussianGammaShiftTrajectory.point_native oneCode one i
  unfold GaussianEulerLowerPowerCoefficients.realLower
  apply zle_of_toZ i
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  rw [GaussianRootAlgebra.equal_re native]
  simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
  ipra_simps
  ring

theorem integer_integral_source (i : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerIntegralGammaIdentification.source (argument i) (radius i) one one := by
  have h := trajectory_source (Γ := Γ) i
  exact .andI (.andI (le_refl one) (.andI h.andE₂ (native_real_lower i))) h.andE₁

theorem original_source (i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteCofinalRate.source (argument i) (radius i) one one a b :=
  .andI (integer_integral_source i) h

private theorem fields_congr (z R w S a b : PTm n) (hz : Γ ⊢[PRAAx] z ≐ w) (hR : Γ ⊢[PRAAx] R ≐ S) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteName.data z R one one a b ≐ GaussianEulerIncompleteName.data w S one one a b := by
  ipra_congr (GaussianEulerIncompleteName.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [hz, hR, .eqRefl one, .eqRefl one, .eqRefl a, .eqRefl b]

theorem data_zero (a b : PTm n) : Γ ⊢[PRAAx]
    data zero a b ≐ GaussianEulerIncompleteName.data oneCode one one one a b :=
  fields_congr _ _ _ _ a b (GaussianGammaShiftTrajectory.point_zero oneCode one)
    (by unfold radius; ipra_ring)

theorem data_succ (i a b : PTm n) : Γ ⊢[PRAAx]
    data (succ i) a b ≐ GaussianEulerIncompleteName.data (shifted (argument i) one) (radius i+one) one one a b :=
  fields_congr _ _ _ _ a b (GaussianGammaShiftTrajectory.point_succ oneCode one i)
    (by unfold radius; ipra_ring)

theorem original_regular_names (i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN GaussianEulerIncompleteName.lowerF (data i a b) ⋏
      GaussianEuclideanDistanceName.pointCN GaussianEulerIncompleteName.upperF (data i a b) :=
  GaussianEulerIncompleteName.original_regular_names _ _ _ _ _ _ (original_source i a b h)

theorem actual_original_incomplete_Euler_integer_source_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 1) (var 2) ⟶
        GaussianEulerIncompleteCofinalRate.source (argument (var 0)) (radius (var 0)) one one (var 1) (var 2)) :=
  closeUniv 3 (.impI (original_source _ _ _ Prf.hyp0))

theorem actual_original_incomplete_Euler_integer_successor_data_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (data (succ (var 0)) (var 1) (var 2) ≐
        GaussianEulerIncompleteName.data (shifted (argument (var 0)) one) (radius (var 0)+one) one one (var 1) (var 2)) :=
  closeUniv 3 (data_succ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteIntegerDomain
