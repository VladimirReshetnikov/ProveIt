import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.FixedHorizons.GaussianBinetFixedHorizonDecay
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.LaplaceTransforms.GaussianBinetArctangentPoleLaplace

/-!
# Original pole Laplace sums on a denominator-independent horizon

The mesh and horizon are chosen independently. A lower bound on the
real cutoff exponent certifies the endpoint error before the actual
cleared antiderivative is divided by the separated pole.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFixedHorizonPole

open_ipra
open GaussianBinetArctangentResolvent (pole pole_lower)
open GaussianBinetArctangentSignedPole (argument_chart branch chart_source imagNumerator)
open GaussianBinetExponentialIntegral (uniformCost)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianInverseBinomialRows (negative_congr)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product qmul qmul_canonical qzero)
open GaussianRationalLowerBounds (inverse_bound)
open GaussianRationalMetric (bounded distanceBounded qnegative qnegative_canonical qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_canonical reciprocal_identity bounded_negative)
open GaussianRationalSyntheticDivision (qone qmul_congr qzero_add)
open GaussianReciprocalHorner (qmul_one_right qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "LV" => GaussianBinetExponentialIntegralGrid.value
local notation "E" => GaussianBinetLaplaceExponential.nameF
local notation "ed" => GaussianBinetLaplaceExponential.data

/-- Exact inverse algebra applied to the cleared original panel rate. -/
theorem invert_antiderivative (w v e K C P L V : PTm n)
    (hw : Γ ⊢[PRAAx] le one (GaussianRationalReciprocal.normNumerator w)) (hP : Γ ⊢[PRAAx] le one P)
    (hV : Γ ⊢[PRAAx] le one V) (hk : Γ ⊢[PRAAx] bounded (reciprocal w) K one)
    (hv : Γ ⊢[PRAAx] GaussianRationalHorner.canonical v) (he : Γ ⊢[PRAAx] bounded e L V)
    (hc : Γ ⊢[PRAAx] distanceBounded (qmul (qnegative w) v) (qsub e qone) C P) :
    Γ ⊢[PRAAx] distanceBounded v (reciprocal w) (K*C*V+K*L*P) (P*V) := by
  let k := reciprocal w
  let q := qnegative k
  let x := qmul q (qsub e qone)
  have hq : Γ ⊢[PRAAx] bounded q K one := bounded_negative _ _ _ (le_refl one) hk
  have cancel : Γ ⊢[PRAAx] qmul q (qmul (qnegative w) v) ≐ v :=
    ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr
      ((GaussianScalarColumnSelection.negative_both_product k w).eqTrans ((qmul_commutative _ _).eqTrans (reciprocal_identity w hw)))
      (.eqRefl _))).eqTrans ((qmul_commutative _ _).eqTrans (qmul_one_right v hv))
  have first : Γ ⊢[PRAAx] distanceBounded v x (K*C) P :=
    distance_congr cancel (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance q _ _ K C P hP hq hc)
  have z : Γ ⊢[PRAAx] distanceBounded e qzero L V :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hV).iffMpr he
  have diff : Γ ⊢[PRAAx] distanceBounded (qsub e qone) (qsub qzero qone) L V :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hV z
        (GaussianRationalPowerDifference.distance_refl_zero qone V hV))
  have endEq : Γ ⊢[PRAAx] qmul q (qsub qzero qone) ≐ k :=
    (qmul_congr (.eqRefl _) (qzero_add _ (qnegative_canonical qone))).eqTrans
      ((GaussianScalarColumnSelection.negative_both_product k qone).eqTrans (qmul_one_right k (reciprocal_canonical _)))
  have last : Γ ⊢[PRAAx] distanceBounded x k (K*L) V :=
    distance_congr (.eqRefl _) endEq (.eqRefl _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance q _ _ _ _ _ hV hq diff)
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hP hV first last

theorem pole_integral_error (s : Bool) (p X Y D sign A B R U K T L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (hU : Γ ⊢[PRAAx] le A (U*B)) (hm : Γ ⊢[PRAAx] le D (K*X))
    (hcut : Γ ⊢[PRAAx] le (L*D) (X*T)) (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+U)*T) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    let w := pole s X Y D sign A B
    Γ ⊢[PRAAx] distanceBounded (LV (p+N) (qnegative w) ((R+U)*T) T N) (reciprocal w)
      (K*uniformCost (R+U) T*unit L+K*num 10*unit p) (unit p*unit L) := by
  let X' := X*B
  let Y' := imagNumerator s X Y D sign A B
  let D' := D*B
  let s' := branch s X Y D sign A B
  let w := pole s X Y D sign A B
  let v := LV (p+N) (qnegative w) ((R+U)*T) T N
  let k := reciprocal w
  let e := ap2 E p (ed X' Y' D' s' (R+U) T T one)
  have hX := hz.andE₁.andE₁.andE₁
  have hD := hz.andE₁.andE₂
  have low := pole_lower s X Y D sign A B hD hB
  have np := GaussianRationalLowerBounds.norm_positive w X D hX hD low
  have bound : Γ ⊢[PRAAx] bounded k K one :=
    bounded_radius_mono _ _ _ _ _ hX (le_refl one) (le_congr (by ipra_ring) (.eqRefl _) hm) (inverse_bound w X D hX hD low)
  have same : Γ ⊢[PRAAx] qnegative (argument X' Y' D' s') ≐ qnegative w :=
    negative_congr (argument_chart s X Y D sign A B hD hB)
  have equal : Γ ⊢[PRAAx] LV (p+N) (qnegative (argument X' Y' D' s')) ((R+U)*T) T N ≐ v := by
    simpa only [GaussianBinetExponentialIntegralGrid.subst_value,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (LV (Syn.shift (p+N)) (var 0) (Syn.shift ((R+U)*T)) (Syn.shift T) (Syn.shift N)) same
  have h := chart_source s X Y D sign A B R U hz hB hU
  have main := distance_congr (qmul_congr same equal) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianBinetExponentialIntegral.original_cofinal_error p X' Y' D' s' (R+U) T N h hN hpN)
  have cut : Γ ⊢[PRAAx] le (L*D') (X'*T) := le_congr (by dsimp only [D']; ipra_ring) (by dsimp only [X']; ipra_ring)
    (mul_le_mul_right B hcut)
  have endBound : Γ ⊢[PRAAx] bounded e (num 10) (unit L) :=
    GaussianBinetFixedHorizonDecay.endpoint p X' Y' D' s' (R+U) T L h cut hL
  exact invert_antiderivative w v e K (uniformCost (R+U) T) (unit p) (num 10) (unit L) np
    (unit_positive p) (unit_positive L) bound (qmul_canonical _ _) endBound main

end LeanProofs.IPRA.Analysis.GaussianBinetFixedHorizonPole
