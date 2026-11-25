import IPRADerivations.Analysis.GaussianBinetExponentialIntegral
import IPRADerivations.Analysis.GaussianBinetExponentialRectangleColumn
import IPRADerivations.Analysis.GaussianBinetExponentialRectangleEndpoint
import IPRADerivations.Analysis.GaussianScalarColumnSelection

/-!
# Uniform resolvent evaluation of the Binet rectangle columns

Divide the checked cleared antiderivative by the original shifted
parameter. The real margin bounds every reciprocal on the unit
mesh. The remaining two errors come from the actual finite time
quadrature and the exponentially small horizon endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangleResolvent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetExponentialRectangle (data matrix)
open GaussianBinetExponentialRectangleShift (realNumerator shifted_source shifted_margin)
open GaussianBinetExponentialIntegral (uniformCost)
open GaussianBinetWeightedExponentialAlgebra (tagWeight)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalFubini (column)
open GaussianRationalHorner (qmul qmul_canonical qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded qnegative qnegative_canonical qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_canonical reciprocal_identity bounded_negative)
open GaussianRationalSyntheticDivision (qone qmul_congr qzero_add)
open GaussianReciprocalHorner (qmul_one_right qmul_associative)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "LV" => GaussianBinetExponentialIntegralGrid.value
local notation "LP" => GaussianBinetLaplaceExponential.nameF
local notation "LD" => GaussianBinetLaplaceExponential.data

theorem inverse_bounds (X Y D sign R K M j : PTm n) (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hm : Γ ⊢[PRAAx] le D (K*X)) (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) :
    let A := realNumerator X D M j
    let w := argument A (M*Y) (M*D) sign
    Γ ⊢[PRAAx] bounded (reciprocal w) K one ⋏ (qmul (reciprocal w) w ≐ qone) := by
  let A := realNumerator X D M j
  let w := argument A (M*Y) (M*D) sign
  have h := (shifted_source X Y D sign R M j hz hM hj).andE₁
  have hA := h.andE₁.andE₁
  have hD := h.andE₂
  have lower := GaussianBinetReciprocalRows.real_part_lower A (M*Y) (M*D) sign h
  have norm := GaussianNameReciprocal.lower_norm_positive w (M*D) hD
    (GaussianRationalLowerBounds.name_lower w A (M*D) hA hD lower)
  have inverse := GaussianRationalLowerBounds.inverse_bound w A (M*D) hA hD lower
  exact .andI (bounded_radius_mono _ _ _ _ _ hA (le_refl one)
      (le_congr (by ipra_ring) (.eqRefl _) (shifted_margin X D K M j hm)) inverse)
    ((qmul_commutative _ _).eqTrans (reciprocal_identity w norm))

theorem shifted_integral_error (j p X Y D sign R K L N M : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hm : Γ ⊢[PRAAx] le D (K*X))
    (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M)
    (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+one)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    let T := D*L
    let w := argument (realNumerator X D M j) (M*Y) (M*D) sign
    Γ ⊢[PRAAx] distanceBounded (LV (p+N) (qnegative w) ((R+one)*T) T N) (reciprocal w)
      (K*uniformCost (R+one) T*unit L+K*num 20*unit p) (unit p*unit L) := by
  let T := D*L
  let A := realNumerator X D M j
  let B := M*Y
  let E := M*D
  let w := argument A B E sign
  let v := LV (p+N) (qnegative w) ((R+one)*T) T N
  let k := reciprocal w
  let q := qnegative k
  let e := ap2 LP p (LD A B E sign (R+one) T T one)
  let rhs := qmul q (qsub e qone)
  let C := uniformCost (R+one) T
  let P := unit p
  let U := unit L
  have pPos := unit_positive (Γ := Γ) p
  have lPos := unit_positive (Γ := Γ) L
  have bounds := inverse_bounds X Y D sign R K M j hz hm hM hj
  have bound : Γ ⊢[PRAAx] bounded q K one := bounded_negative _ _ _ (le_refl one) bounds.andE₁
  have main := GaussianBinetExponentialIntegral.original_cofinal_error p A B E sign (R+one) T N
    (shifted_source X Y D sign R M j hz hM hj) hN hpN
  have cancel : Γ ⊢[PRAAx] qmul q (qmul (qnegative w) v) ≐ v :=
    ((qmul_associative _ _ _).eqSymm.eqTrans
      (qmul_congr ((GaussianScalarColumnSelection.negative_both_product k w).eqTrans bounds.andE₂) (.eqRefl _))).eqTrans
      ((qmul_commutative _ _).eqTrans (qmul_one_right v (qmul_canonical _ _)))
  have first : Γ ⊢[PRAAx] distanceBounded v rhs (K*C) P :=
    distance_congr cancel (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance q _ _ K C P pPos bound main)
  have er := GaussianBinetExponentialRectangleEndpoint.shifted_endpoint p X Y D sign R L M j hz hM hj hL
  have zero : Γ ⊢[PRAAx] distanceBounded e qzero (num 20) U :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ lPos).iffMpr er
  have diff : Γ ⊢[PRAAx] distanceBounded (qsub e qone) (qsub qzero qone) (num 20) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ lPos zero
        (GaussianRationalPowerDifference.distance_refl_zero qone U lPos))
  have endEq : Γ ⊢[PRAAx] qmul q (qsub qzero qone) ≐ k :=
    (qmul_congr (.eqRefl _) (qzero_add _ (qnegative_canonical qone))).eqTrans
      ((GaussianScalarColumnSelection.negative_both_product k qone).eqTrans (qmul_one_right k (reciprocal_canonical _)))
  have last : Γ ⊢[PRAAx] distanceBounded rhs k (K*num 20) U :=
    distance_congr (.eqRefl _) endEq (.eqRefl _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance q _ _ _ _ _ lPos bound diff)
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ pPos lPos first last

def numerator (p R K T L : PTm n) : PTm n :=
  (num 20*T)*unit L+two*(K*uniformCost (R+one) T*unit L+K*num 20*unit p)

theorem column_resolvent (j p X Y D sign R K L N M : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hm : Γ ⊢[PRAAx] le D (K*X))
    (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+one)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    let T := D*L
    let w := argument (realNumerator X D M j) (M*Y) (M*D) sign
    Γ ⊢[PRAAx] distanceBounded
      (qmul (fraction T N) (column matrix j N (data (p+N) (qnegative (argument X Y D sign)) (R*T) T N M)))
      (qmul (tagWeight j M) (reciprocal w)) (numerator p R K T L) (unit p*unit L) := by
  let r := p+N
  let T := D*L
  let w := argument (realNumerator X D M j) (M*Y) (M*D) sign
  let k := reciprocal w
  let v := LV r (qnegative w) ((R+one)*T) T N
  let c := tagWeight j M
  let P := unit p
  let U := unit L
  let W := unit r
  let A := num 20*T
  have pPos := unit_positive (Γ := Γ) p
  have lPos := unit_positive (Γ := Γ) L
  have rPos := unit_positive (Γ := Γ) r
  have dPos := positive_product _ _ pPos lPos
  have hr : Γ ⊢[PRAAx] le p r := le_add_right _ _
  have grow := GaussianExponentialReference.unit_monotone hr
  have first : Γ ⊢[PRAAx] distanceBounded
      (qmul (fraction T N) (column matrix j N (data r (qnegative (argument X Y D sign)) (R*T) T N M)))
      (qmul c v) (A*U) (P*U) :=
    distance_radius_mono _ _ _ _ _ _ rPos dPos
      (by dsimp only [A,P]; ipra_le 20*𝔞(T)*𝔞(U)*sl grow)
      (GaussianBinetExponentialRectangleColumn.column_error j r X Y D sign R T N M hz (le_trans pPos hpN) hM hj)
  have last := GaussianApproximateInverseDistance.multiply_distance c v k two _ _ dPos
    (GaussianBinetExponentialRectangleColumn.weight_bound j M hM hj)
    (shifted_integral_error j p X Y D sign R K L N M hz hm hM hj hL hN hpN)
  exact distance_triangle_same _ _ _ _ _ _ dPos first last

end LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangleResolvent
