import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.GaussianBinetArctangentSignedPole
import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialIntegral
import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialRectangleEndpoint
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarColumnSelection

/-!
# Uniform Laplace evaluation at the two complex arctangent poles

The original finite Laplace sum at either signed pole approaches its
reciprocal with the same explicit clock for a compact frequency interval.
The common horizon uses the original denominator, independent of the
frequency denominator of each sampled row.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentPoleLaplace

open_ipra
open GaussianBinetArctangentResolvent (pole pole_lower)
open GaussianBinetArctangentSignedPole (argument_chart branch chart_source imagNumerator)
open GaussianBinetExponentialIntegral (uniformCost)
open GaussianBinetLaplaceStripTail (envelope_at)
open GaussianBinetLaplaceStripTailEnvelope (integer_cutoff_envelope)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianEulerDecayMesh (observation)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product qmul qmul_canonical qzero)
open GaussianRationalLowerBounds (inverse_bound name_lower)
open GaussianRationalMetric (bounded distanceBounded qnegative qnegative_canonical qsub subst_qnegative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_canonical reciprocal_identity bounded_negative bound_congr)
open GaussianRationalSyntheticDivision (qone qmul_congr qzero_add)
open GaussianReciprocalHorner (qmul_one_right qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "LV" => GaussianBinetExponentialIntegralGrid.value
local notation "E" => GaussianBinetLaplaceExponential.nameF
local notation "ed" => GaussianBinetLaplaceExponential.data

theorem pole_endpoint (s : Bool) (p X Y D sign A B R U L : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (hU : Γ ⊢[PRAAx] le A (U*B)) (hL : Γ ⊢[PRAAx] le L p) :
    Γ ⊢[PRAAx] bounded (ap2 E p (ed (X*B) (imagNumerator s X Y D sign A B) (D*B)
      (branch s X Y D sign A B) (R+U) (D*L) (D*L) one)) (num 5) (unit L) := by
  let T := D*L
  let V := unit L
  let P := unit p
  let q := ap2 E p (ed (X*B) (imagNumerator s X Y D sign A B) (D*B) (branch s X Y D sign A B) (R+U) T T one)
  have hp := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) L
  have hVP := positive_product _ _ hV hp
  have h := chart_source s X Y D sign A B R U hz hB hU
  have hr := envelope_at (X*(D*L*B)) (D*B) one V two p
    (integer_cutoff_envelope X D L B hz.andE₁.andE₁.andE₁ hz.andE₁.andE₂ hB)
  have en : Γ ⊢[PRAAx] observation (X*(D*L*B)) (D*B) p ≐ observation (X*B*T) (D*B*one) p := by
    simpa only [GaussianEulerDecayMesh.subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![X*(D*L*B),D*B,p]) (σ' := ![X*B*T,D*B*one,p])
        (fun i => by
          fin_cases i
          · change Γ ⊢[PRAAx] X*(D*L*B) ≐ X*B*(D*L)
            ipra_ring
          · change Γ ⊢[PRAAx] D*B ≐ D*B*one
            ipra_ring
          · exact .eqRefl p))
  have hInput : Γ ⊢[PRAAx] GaussianBinetLaplaceIntegrand.input (X*B) (imagNumerator s X Y D sign A B) (D*B)
      (branch s X Y D sign A B) (R+U) T T one :=
    .andI h (.andI (le_refl one) (le_of_eq_add (d := zero) (by ipra_ring)))
  have transferred := GaussianBinetLaplaceDecay.observation_bound p _ _ _ _ _ T T one (one*P+two*V) (V*P)
    hInput hVP (bound_congr en (.eqRefl _) (.eqRefl _) hr)
  exact bounded_radius_mono q _ _ _ _ (positive_product _ _ hVP hp) hV (by
    have grow := GaussianExponentialReference.unit_monotone hL
    dsimp only [V,P] at *
    ipra_le 4*𝔞(unit p)*𝔞(unit L)*sl grow) transferred

/-- Finite original panel integral converges to the reciprocal of either pole. -/
theorem pole_integral_error (s : Bool) (p X Y D sign A B R U K L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (hU : Γ ⊢[PRAAx] le A (U*B)) (hm : Γ ⊢[PRAAx] le D (K*X)) (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+U)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    let T := D*L
    let w := pole s X Y D sign A B
    Γ ⊢[PRAAx] distanceBounded (LV (p+N) (qnegative w) ((R+U)*T) T N) (reciprocal w)
      (K*uniformCost (R+U) T*unit L+K*num 5*unit p) (unit p*unit L) := by
  let T := D*L
  let X' := X*B
  let Y' := imagNumerator s X Y D sign A B
  let D' := D*B
  let s' := branch s X Y D sign A B
  let w := pole s X Y D sign A B
  let v := LV (p+N) (qnegative w) ((R+U)*T) T N
  let k := reciprocal w
  let q := qnegative k
  let e := ap2 E p (ed X' Y' D' s' (R+U) T T one)
  let C := uniformCost (R+U) T
  let P := unit p
  let V := unit L
  have pPos := unit_positive (Γ := Γ) p
  have lPos := unit_positive (Γ := Γ) L
  have hX := hz.andE₁.andE₁.andE₁
  have hD := hz.andE₁.andE₂
  have lower := pole_lower s X Y D sign A B hD hB
  have np := GaussianNameReciprocal.lower_norm_positive w D hD (name_lower w X D hX hD lower)
  have bound : Γ ⊢[PRAAx] bounded q K one := bounded_negative _ _ _ (le_refl one)
    (bounded_radius_mono _ _ _ _ _ hX (le_refl one) (le_congr (by ipra_ring) (.eqRefl _) hm)
      (inverse_bound w X D hX hD lower))
  have same := argument_chart s X Y D sign A B hD hB
  have ns : Γ ⊢[PRAAx] qnegative (argument X' Y' D' s') ≐ qnegative w := by
    simpa only [subst_qnegative,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (qnegative (var 0)) same
  have equal : Γ ⊢[PRAAx] LV (p+N) (qnegative (argument X' Y' D' s')) ((R+U)*T) T N ≐ v := by
    simpa only [GaussianBinetExponentialIntegralGrid.subst_value,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (LV (Syn.shift (p+N)) (var 0) (Syn.shift ((R+U)*T)) (Syn.shift T) (Syn.shift N)) ns
  have main := distance_congr (qmul_congr ns equal)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (GaussianBinetExponentialIntegral.original_cofinal_error p X' Y' D' s' (R+U) T N
      (chart_source s X Y D sign A B R U hz hB hU) hN hpN)
  have cancel : Γ ⊢[PRAAx] qmul q (qmul (qnegative w) v) ≐ v :=
    ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr
      ((GaussianScalarColumnSelection.negative_both_product k w).eqTrans ((qmul_commutative _ _).eqTrans (reciprocal_identity w np)))
      (.eqRefl _))).eqTrans ((qmul_commutative _ _).eqTrans (qmul_one_right v (qmul_canonical _ _)))
  have first : Γ ⊢[PRAAx] distanceBounded v (qmul q (qsub e qone)) (K*C) P :=
    distance_congr cancel (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance q _ _ K C P pPos bound main)
  have zero : Γ ⊢[PRAAx] distanceBounded e qzero (num 5) V :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ lPos).iffMpr (pole_endpoint s p X Y D sign A B R U L hz hB hU hL)
  have diff : Γ ⊢[PRAAx] distanceBounded (qsub e qone) (qsub qzero qone) (num 5) V :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ lPos zero
        (GaussianRationalPowerDifference.distance_refl_zero qone V lPos))
  have endEq : Γ ⊢[PRAAx] qmul q (qsub qzero qone) ≐ k :=
    (qmul_congr (.eqRefl _) (qzero_add _ (qnegative_canonical qone))).eqTrans
      ((GaussianScalarColumnSelection.negative_both_product k qone).eqTrans (qmul_one_right k (reciprocal_canonical _)))
  have last : Γ ⊢[PRAAx] distanceBounded (qmul q (qsub e qone)) k (K*num 5) V :=
    distance_congr (.eqRefl _) endEq (.eqRefl _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance q _ _ _ _ _ lPos bound diff)
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ pPos lPos first last

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentPoleLaplace
