import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsBinding

/-!
# The actual digamma weighted-prefix recurrence

For the digamma exponents the two second-derivative coefficients
agree. The next weighted prefix is approximated by the signed
Bernoulli mean times the exact reciprocal primitive minus the
previous prefix, on the original common mesh and cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliRecurrence

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction)
open GaussianNamedDifference (difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianStirlingAllOrderPanelDerivative (degreeProduct signedMean)
open GaussianStirlingAllOrderPanelPartsBinding (meanPoint)
open GaussianStirlingAllOrderPanelPartsDensities (highScalar lowScalar)
open GaussianStirlingAllOrderPanelPartsNames (constantCap fixed_product_distance)
open GaussianStirlingAllOrderPanelPartsOuterFold (massPrefix panelPrefix)
open GaussianStirlingAllOrderPanelPartsRecurrence (errorCoefficient)
open GaussianStirlingAllOrderPanelPartsSolve (estimate ratio inverse_high_cancel embed_sub finite_solve_distance)
open GaussianStirlingAllOrderPowerIntegralCofinal (cofinal_mass_distance)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive)
open GaussianStirlingAllOrderReciprocalTaylor (secondCoefficient)
open GaussianStirlingAllOrderReciprocalWeightError (power coefficient)
open GaussianStirlingGlobalBounds (steps)
open GaussianStirlingNames (source)
open RationalAlgebra (multiply_commutative multiply_congr)
open RationalArithmetic (add_guard multiply)
open RationalGaussianEmbedding (embed embed_multiply)
open RationalGaussianRealPart (embed_congr)
open RationalSumConstants (multiply_one_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def exponent (m : ℕ) : ℕ := 2*m+3

def meshCost (m : ℕ) (A B p : PTm n) : PTm n :=
  steps p*errorCoefficient (m+1) (exponent m) (A+B*steps p) B

def prefixAt (m : ℕ) (A B Q p : PTm n) : PTm n :=
  embed (panelPrefix m (2*m+2) A B (B*Q) (steps p))

def weightedPrimitive (m : ℕ) (A B : PTm n) : PTm n :=
  embed (multiply (signedMean (m+1)) (primitive (exponent m) A B))

def stepRadius (m : ℕ) (B : PTm n) : PTm n :=
  one+constantCap (meanPoint m)*(power (exponent m) B+one)

ipra_subst prefixAt

ipra_subst weightedPrimitive [signedMean, GaussianStirlingAllOrderPanelDerivative.meanNumerator, BernoulliBounds.zint]

ipra_subst stepRadius [power, one, pw]

theorem ratio_one (m : ℕ) : Γ ⊢[PRAAx] (ratio (m+1) (exponent m) : PTm n) ≐ fraction one one := by
  have h : degreeProduct (m+1) = secondCoefficient (exponent m) := by
    unfold degreeProduct secondCoefficient exponent
    ring
  have e : (lowScalar (m+1) : PTm n) = highScalar (exponent m) := by
    simp [lowScalar,highScalar,coefficient,h]
  unfold ratio
  rw [e]
  exact inverse_high_cancel _ (by unfold exponent; omega)

private theorem finite_estimate (m : ℕ) (A B Q p : PTm n) :
    Γ ⊢[PRAAx] embed (estimate (m+1) (exponent m) A B (B*Q) (steps p)) ≐
      qsub (qmul (meanPoint m) (embed (massPrefix (exponent m) A B (B*Q) (steps p))))
        (prefixAt m A B Q p) := by
  let W := massPrefix (exponent m) A B (B*Q) (steps p)
  let V := panelPrefix m (2*m+2) A B (B*Q) (steps p)
  let x := sub (multiply (signedMean (m+1)) W) V
  have e : Γ ⊢[PRAAx] estimate (m+1) (exponent m) A B (B*Q) (steps p) ≐ x := by
    unfold estimate
    rw [Nat.succ_sub_one,show exponent m-1=2*m+2 by unfold exponent; omega]
    exact (multiply_congr (ratio_one m) (.eqRefl x)).eqTrans
      ((multiply_commutative _ _).eqTrans (multiply_one_right x (add_guard _ _)))
  exact (embed_congr e).eqTrans
    ((embed_sub (multiply (signedMean (m+1)) W) V).eqTrans (qsub_congr (embed_multiply _ _) (.eqRefl _)))

theorem step_distance (m : ℕ) (A B Q p : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hQ : Γ ⊢[PRAAx] le (unit p*succ (meshCost m A B p)) Q) :
    Γ ⊢[PRAAx] distanceBounded (prefixAt (m+1) A B Q p)
      (qsub (weightedPrimitive m A B) (prefixAt m A B Q p)) (stepRadius m B) (unit p) := by
  let e := exponent m
  let M := B*Q
  let L := steps p
  let cost := meshCost m A B p
  let V := prefixAt m A B Q p
  let W := massPrefix e A B M L
  let G := primitive e A B
  let C := meanPoint (n := n) m
  let R := constantCap C*(power e B+one)
  have hp := unit_positive (Γ := Γ) p
  have hL : Γ ⊢[PRAAx] le (unit p) L :=
    le_trans (GaussianStirlingIntegerLimit.index_dominates_unit p) (le_succ_self _)
  have qm : Γ ⊢[PRAAx] le Q M := by unfold M; ipra_le 𝔞 Q*sl hs.andE₂
  have b : Γ ⊢[PRAAx] le (unit p) (unit p*succ cost) := by ipra_le 𝔞 (unit p)*𝔞 cost
  have dm := le_trans b (le_trans hQ qm)
  have hM := le_trans hp dm
  have budget : Γ ⊢[PRAAx] le (cost*unit p) (one*M) := by
    have h := le_trans hQ qm
    ipra_le sl h+𝔞 (unit p)
  have he : 2≤e := by unfold e exponent; omega
  have ce : e+1=2*(m+1)+2 := by unfold e exponent; omega
  have finite := finite_solve_distance (m+1) e (by omega) he A B M L hs.andE₁ hM
  have raw : Γ ⊢[PRAAx] distanceBounded (prefixAt (m+1) A B Q p)
      (qsub (qmul C (embed W)) V) one (unit p) := by
    have complete := distance_radius_mono _ _ _ _ one (unit p) hM hp budget finite
    have row := distance_congr (finite_estimate m A B Q p) (.eqRefl _) (.eqRefl _) (.eqRefl _) complete
    simpa only [prefixAt,← ce,M,L,C,V,W] using distance_symmetric _ _ _ _ hp row
  have mass := cofinal_mass_distance e he A B M L (unit p) hs.andE₁ hp dm hL
  have scaled := fixed_product_distance C _ _ _ _ hp mass
  have ideal : Γ ⊢[PRAAx] distanceBounded (qmul C (embed W)) (weightedPrimitive m A B) R (unit p) :=
    distance_congr (.eqRefl _) (embed_multiply (signedMean (m+1)) G).eqSymm (.eqRefl _) (.eqRefl _) scaled
  have diff := difference_distance _ _ _ _ _ _ _ hp ideal (distance_refl_zero V (unit p) hp)
  have limits := distance_congr (.eqRefl _) (.eqRefl _) (LeanProofs.IPRA.add_zero R) (.eqRefl _) diff
  exact distance_triangle_same _ _ _ _ _ _ hp raw limits

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliRecurrence
