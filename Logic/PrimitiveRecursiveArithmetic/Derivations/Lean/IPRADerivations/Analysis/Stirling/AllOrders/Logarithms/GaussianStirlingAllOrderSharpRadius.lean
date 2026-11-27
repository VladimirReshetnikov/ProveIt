import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.SignedRemainder.GaussianStirlingAllOrderSignedLowerAlgebra
import IPRADerivations.Analysis.Stirling.AllOrders.Logarithms.GaussianStirlingAllOrderLogRateBudget

/-!
# The exact rational magnitude of the first omitted term

The literal oriented correction has the fixed integer Bernoulli
numerator times the original reciprocal power. A strict positivity
certificate chooses the nonnegative representative of that magnitude.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSharpRadius

open_ipra
open BernoulliBounds (zint toZ_zint bden bden_pos)
open GaussianStirlingAllOrderTruncationCoefficients (sign coefficientNumerator literalCoefficient literalPower literalTerm)
open GaussianStirlingAllOrderTruncationAlgebra (correction)
open GaussianStirlingAllOrderSignedLowerAlgebra (orientationCode orientationPoint)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingAllOrderLogRateTransport (upperPoint lowerPoint)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalHorner (qmul qzero positive_product)
open RationalArithmetic (negative multiply recode)
open RationalArgmin (rationalLE rationalLE_congr denominator_positive)
open RationalValueBounds (upper_of_order upper_congr)
open RationalGaussianEmbedding (embed embed_multiply embed_negative)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open RationalFiniteSum (canonical_equal)
open RationalGaussianRealPart (embed_congr)
open RationalRepresentations (represents_multiply represents_negative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def absoluteCoefficient (m : ℕ) : ℕ := (coefficientNumerator m).natAbs
def orientedNumerator (m : ℕ) : ℤ := sign m*coefficientNumerator m
def radiusNumerator (m : ℕ) (B : PTm n) : PTm n := num (absoluteCoefficient m)*power (2*m+1) B
def radiusDenominator (m : ℕ) (A : PTm n) : PTm n := num (bden (2*m+2))*power (2*m+1) A

def orientedTerm (m : ℕ) (A B : PTm n) : PTm n :=
  normalize (zint (orientedNumerator m)*ZT.ofNat (power (2*m+1) B)) (radiusDenominator m A)

theorem oriented_abs (m : ℕ) : (orientedNumerator m).natAbs = absoluteCoefficient m := by
  simp [orientedNumerator,absoluteCoefficient,sign,Int.natAbs_mul,Int.natAbs_pow]

theorem radius_denominator_positive (m : ℕ) (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (radiusDenominator m A) :=
  positive_product _ _
    (Foundations.NumeralPrimes.num_le (a := 1) (bden_pos _)) (GaussianFactorBudget.power_positive _ _ hA)

theorem oriented_term_at (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    qmul (orientationPoint m) (correction m A B) ≐ embed (orientedTerm m A B) := by
  let d : PTm n := num (bden (2*m+2))
  let U := power (2*m+1) B
  let V := power (2*m+1) A
  have hd : Γ ⊢[PRAAx] le one d := Foundations.NumeralPrimes.num_le (a := 1) (bden_pos _)
  have hv : Γ ⊢[PRAAx] le one V := GaussianFactorBudget.power_positive _ _ hA
  have hD := positive_product _ _ hd hv
  have rr : Γ ⊢[PRAAx] RationalArithmetic.represents (literalTerm m A B)
      (zint (coefficientNumerator m)*ZT.ofNat U) (d*V) :=
    represents_multiply _ _ _ _ _ _
      (normalize_preserves_value (zint (coefficientNumerator m)) d hd) (fraction_represents U V hv)
  have rf := represents_multiply _ _ _ _ _ _
    (normalize_preserves_value (zint (sign m)) one (le_refl one)) rr
  have den := positive_product _ _ (le_refl one) hD
  have e : Γ ⊢[PRAAx] multiply (orientationCode m) (literalTerm m A B) ≐ orientedTerm m A B := by
    apply canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _) (normalize_well_formed _ _ hD)
      rf (normalize_preserves_value _ _ hD) den hD
    apply ZT.derive
    simp only [orientedNumerator,ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint,Int.cast_mul]
    ipra_simps
    ring
  exact (embed_multiply _ _).eqSymm.eqTrans (embed_congr e)

private theorem positive_readback (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hz : 0≤orientedNumerator m) :
    Γ ⊢[PRAAx] orientedTerm m A B ≐ fraction (radiusNumerator m B) (radiusDenominator m A) := by
  let d := radiusDenominator m A
  let u := radiusNumerator m B
  let w := power (2*m+1) B
  have hd := radius_denominator_positive (Γ := Γ) m A hA
  have e : (orientedNumerator m : Groth (Q Γ)) = (absoluteCoefficient m : Groth (Q Γ)) := by
    rw [←oriented_abs]
    exact (BernoulliBounds.natAbs_cast_of_nonneg hz).symm
  apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hd) (normalize_well_formed _ _ hd)
    (normalize_preserves_value (zint (orientedNumerator m)*ZT.ofNat w) d hd) (fraction_represents u d hd) hd hd
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint,e]
  unfold u
  simp only [radiusNumerator]
  ipra_simps
  ring

private theorem negative_readback (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hz : orientedNumerator m<0) :
    Γ ⊢[PRAAx] orientedTerm m A B ≐ negative (fraction (radiusNumerator m B) (radiusDenominator m A)) := by
  let d := radiusDenominator m A
  let u := radiusNumerator m B
  let w := power (2*m+1) B
  have hd := radius_denominator_positive (Γ := Γ) m A hA
  have e : (orientedNumerator m : Groth (Q Γ)) = -(absoluteCoefficient m : Groth (Q Γ)) := by
    rw [←oriented_abs,BernoulliBounds.natAbs_cast_of_neg hz,neg_neg]
  apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hd) (RationalArithmetic.negative_guard _)
    (normalize_preserves_value (zint (orientedNumerator m)*ZT.ofNat w) d hd)
    (represents_negative _ _ _ (fraction_represents u d hd)) hd hd
  apply ZT.derive
  simp only [ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint,e]
  unfold u
  simp only [radiusNumerator]
  ipra_simps
  ring

private theorem scalar_negative_order (R D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] rationalLE (fstT (lowerPoint R D)) (fstT qzero) := by
  let q := fraction R D
  let d := denominator_positive (Γ := Γ) q
  have e : Γ ⊢[PRAAx] recode q ≐ q :=
    canonical_equal _ _ _ _ _ _ (RationalArithmetic.recode_guard q) (normalize_well_formed _ _ hD)
      (RationalArithmetic.recode_value q) (RationalRepresentations.represents_self q) d d (.eqRefl _)
  have fs : Γ ⊢[PRAAx] fstT (lowerPoint R D) ≐ negative q :=
    (fst_pair _ _).eqTrans (RationalAlgebra.negative_congr ((fst_pair _ _).eqTrans e))
  apply rationalLE_congr fs.eqSymm RationalGaussianRealPart.real_zero.eqSymm
  apply RationalArithmetic.order_of_representations _ _ _ _ D one
    (represents_negative _ _ _ (fraction_represents R D hD)) (fraction_represents zero one (le_refl one)) hD (le_refl one)
  apply zle_of_toZ R
  simp only [ZT.toZ_neg,ZT.toZ_ofNat,ZT.toZ_mul]
  ipra_simps
  ring

theorem negative_radius_order (R D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] realOrder constantF constantF (lowerPoint R D) qzero := by
  apply order_from_envelope _ _ _ _ zero (constant_regular _) (constant_regular _)
  refine .allI ?_
  let r := Syn.shift R
  let d := Syn.shift D
  let Δ := Γ.map Fm.shift
  have hd : Δ ⊢[PRAAx] le one d := by simpa [d,Δ,Fm.shift,Syn.shift] using hD.shift
  have e := scalar_negative_order r d hd
  have u := upper_of_order _ _ zero (unit (var 0)) e
  simpa [envelope,r,d,Δ,Syn.shift] using upper_congr (congrFst (constant_at _ _)).eqSymm
    (congrFst (constant_at _ _)).eqSymm (.eqRefl _) (.eqRefl _) u

theorem oriented_cap_radius (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (h : Γ ⊢[PRAAx] strictOrder constantF constantF qzero (qmul (orientationPoint m) (correction m A B))) :
    Γ ⊢[PRAAx] qmul (orientationPoint m) (correction m A B) ≐
      upperPoint (radiusNumerator m B) (radiusDenominator m A) := by
  let w := qmul (orientationPoint m) (correction m A B)
  let R := radiusNumerator m B
  let D := radiusDenominator m A
  have e := oriented_term_at m A B hA
  by_cases hz : 0≤orientedNumerator m
  · exact e.eqTrans (embed_congr (positive_readback m A B hA hz))
  · have he : Γ ⊢[PRAAx] w ≐ lowerPoint R D :=
      e.eqTrans ((embed_congr (negative_readback m A B hA (lt_of_not_ge hz))).eqTrans (embed_negative _))
    have hw := GaussianSignedNameExponentialOrder.constant_equal_cross _ _ he
    have hzero := GaussianNameEquivalence.cross_refl (Γ := Γ) constantF qzero (constant_regular _)
    have nn := GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ hw hzero
      (negative_radius_order R D (radius_denominator_positive m A hA))
    exact .botE _ (.impE h.andE₂ nn)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSharpRadius
