import IPRADerivations.Analysis.Stirling.AllOrders.Truncation.Algebra.GaussianStirlingAllOrderTruncationHorner
import IPRADerivations.Analysis.Stirling.Expansions.ExpansionErrors.GaussianStirlingExpansionConditionalError
import IPRADerivations.Analysis.Stirling.Bounds.Multiplicative.GaussianStirlingMultiplicativeBounds
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate

/-!
# Transport named logarithmic truncation bounds to the original rate

The two real-order bounds control the norm of the original normalized
difference. The finite integer-gap rule removes the error of the
intermediate observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderLogRateTransport

open_ipra
open GaussianStirlingAllOrderTruncationHorner (hornerErrorData truncation_even_horner truncation_odd_horner)
open GaussianStirlingAllOrderTruncationAlgebra (truncation correction)
open GaussianStirlingAllOrderLogTruncation (errorF)
open GaussianStirlingGlobalBounds (remainderF remainderData remainder_regular)
open GaussianStirlingNames (source)
open GaussianStirlingExpansionFiniteError (logPolynomial)
open GaussianStirlingAllOrderPanelPartsRows (scalar_order_bound)
open GaussianEuclideanDistanceName (fraction fraction_order pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianReconstructionRoots (distance_zero_iff)
open RationalGaussianEmbedding (embed embed_axis axis axis_add axis_zero canonical_axis_roundtrip)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_radius
  radius_of_upper radius_symmetric)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def upperPoint (A N : PTm n) : PTm n := embed (fraction A N)
def lowerPoint (A N : PTm n) : PTm n := qnegative (upperPoint A N)

def errorOrders (d : ℕ) (A B x R D : PTm n) : Fm PTm n :=
  realOrder constantF errorF (lowerPoint R D) (hornerErrorData d A B x) ⋏
    realOrder errorF constantF (hornerErrorData d A B x) (upperPoint R D)

ipra_subst upperPoint
ipra_subst lowerPoint
ipra_subst hornerErrorData [logPolynomial, GaussianStirlingExpansionFiniteError.query]

private theorem truncation_axis (m : ℕ) (A B : PTm n) : Γ ⊢[PRAAx] axis (truncation m A B) := by
  induction m with
  | zero => exact axis_zero
  | succ m ih => exact axis_add _ _ ih (embed_axis _)

theorem horner_axis (d : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] axis (logPolynomial d A B) := by
  let m := d/2
  have e : d=2*m ∨ d=2*m+1 := by unfold m; omega
  rcases e with ed | ed
  · rw [ed]
    exact RationalGaussianEmbedding.axis_congr (truncation_even_horner m A B hA) (truncation_axis m A B)
  · rw [ed]
    exact RationalGaussianEmbedding.axis_congr (truncation_odd_horner m A B hA) (truncation_axis (m+1) A B)

theorem horner_error_real (d : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    realSamples errorF (hornerErrorData d A B x) := by
  apply GaussianRealNameExponentialInjectivity.difference_real_samples
  · refine .allI ?_
    let a := Syn.shift A
    let b := Syn.shift B
    let z := Syn.shift x
    let Δ := Γ.map Fm.shift
    have h : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift
    simpa [GaussianRealNameExponentialInjectivity.axisSamples,a,b,z,Δ,Syn.shift] using
      (real_sample_at remainderF (remainderData a b z) (var 0)
        (GaussianStirlingMultiplicativeBounds.remainder_real a b z h)).andE₂
  · refine .allI ?_
    let a := Syn.shift A
    let b := Syn.shift B
    let Δ := Γ.map Fm.shift
    have ha : Δ ⊢[PRAAx] le one a := by simpa [Δ,a,Fm.shift,Syn.shift] using hs.andE₁.shift
    have e := RationalGaussianEmbedding.axis_congr (constant_at (var 0) (logPolynomial d a b)).eqSymm (horner_axis d a b ha)
    simpa [GaussianRealNameExponentialInjectivity.axisSamples,a,b,Δ,Syn.shift,logPolynomial,
      GaussianStirlingExpansionFiniteError.query] using e

private theorem bound_constants (R D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    bounded (upperPoint R D) R D ⋏ bounded (lowerPoint R D) R D := by
  have q := scalar_order_bound (fraction R D) R D hD
    (fraction_order zero one R D (le_refl one) hD (by ipra_le Groth.ι (IPRA.Q.mk Γ R))) (RationalArgmin.reflexive _)
  exact .andI q (GaussianRationalReciprocal.bounded_negative _ _ _ hD q)

theorem named_error_distance (F : PR 2) (z R D p : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (real : Γ ⊢[PRAAx] realSamples F z)
    (lo : Γ ⊢[PRAAx] realOrder constantF F (lowerPoint R D) z)
    (hi : Γ ⊢[PRAAx] realOrder F constantF z (upperPoint R D)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p z) qzero (R*unit p+two*D) (D*unit p) := by
  let u := unit p
  let a := fstT (ap2 F p z)
  let b := fstT (qzero : PTm n)
  let L := lowerPoint R D
  let U := upperPoint R D
  have hu := unit_positive (Γ := Γ) p
  have hU := positive_product _ _ hu hu
  have hDu := positive_product _ _ hD hu
  have base := bound_constants R D hD
  have ru := scalar_coordinate_distance U qzero R D hD ((distance_zero_iff _ _ _ hD).iffMpr base.andE₁)
  have rl := scalar_coordinate_distance L qzero R D hD ((distance_zero_iff _ _ _ hD).iffMpr base.andE₂)
  have dl : Γ ⊢[PRAAx] upper (fstT L) a two u :=
    upper_mono _ _ _ _ _ _ hU (upper_congr (congrFst (constant_at p L)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (real_order_at _ _ _ _ p p lo)) (by ipra_le 0)
  have du : Γ ⊢[PRAAx] upper a (fstT U) two u :=
    upper_mono _ _ _ _ _ _ hU (upper_congr (.eqRefl _) (congrFst (constant_at p U)) (.eqRefl _) (.eqRefl _)
      (real_order_at _ _ _ _ p p hi)) (by ipra_le 0)
  have left := upper_triangle _ _ _ _ _ _ _ (upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ rl)) dl
  have right := upper_triangle _ _ _ _ _ _ _ du (upper_of_radius _ _ _ _ ru)
  have radius := radius_of_upper a b (R*u+two*D) (D*u)
    (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) right) left
  have h := real_sample_at F z p real
  exact distance_congr (canonical_axis_roundtrip _ h.andE₁ h.andE₂)
    (canonical_axis_roundtrip _ GaussianRationalSyntheticDivision.qzero_canonical axis_zero) (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hDu radius)

private theorem distance_to_original (d : ℕ) (A B x R D p : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] errorOrders d A B x R D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 remainderF p (remainderData A B x)) (ap2 constantF p (logPolynomial d A B))
      (diagonalNumerator R D (num 8) p) (diagonalDenominator D p) := by
  let f := ap2 remainderF p (remainderData A B x)
  let g := ap2 constantF p (logPolynomial d A B)
  let u := unit p
  have hu := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hD hu
  have e := GaussianNamedDifference.sample_error remainderF constantF (remainderData A B x) (logPolynomial d A B) p
    (remainder_regular A B x hs) (constant_regular _)
  have e' := distance_radius_mono _ _ _ _ (num 6*D) (D*u) hu hd (by unfold u; ipra_le 0)
    (distance_symmetric _ _ _ _ hu e)
  have rb := named_error_distance errorF (hornerErrorData d A B x) R D p hD (horner_error_real d A B x hs) h.andE₁ h.andE₂
  have hb := distance_triangle_same _ _ _ _ _ _ hd e' rb
  exact (distance_zero_iff (qsub f g) _ _ hd).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalNumerator; ipra_ring) (.eqRefl _) hb)

theorem original_rate (d : ℕ) (A B x R D : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] errorOrders d A B x R D) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate remainderF constantF (remainderData A B x) (logPolynomial d A B) R D := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 8) hD
    (remainder_regular A B x hs) (constant_regular _)
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let z := Syn.shift x
  let r := Syn.shift R
  let e := Syn.shift D
  let Δ := Γ.map Fm.shift
  have ss : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift
  have sd : Δ ⊢[PRAAx] le one e := by simpa [Δ,e,Fm.shift,Syn.shift] using hD.shift
  have hh : Δ ⊢[PRAAx] errorOrders d a b z r e := by
    simpa [Δ,a,b,z,r,e,errorOrders,Fm.shift,Syn.shift] using h.shift
  simpa [diagonalEnvelope,a,b,z,r,e,Δ,Syn.shift,logPolynomial,GaussianStirlingExpansionFiniteError.query] using
    distance_to_original d a b z r e (var 0) ss sd hh

theorem log_rate_from_orders (d : ℕ) (A B x C : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (h : Γ ⊢[PRAAx] errorOrders d A B x (C*pw B (succ (num d))) (pw A (succ (num d)))) :
    Γ ⊢[PRAAx] GaussianStirlingExpansionConditionalError.logRate d A B x C :=
  original_rate d A B x _ _ hs (GaussianFactorBudget.power_positive _ _ hs.andE₁) h

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderLogRateTransport
