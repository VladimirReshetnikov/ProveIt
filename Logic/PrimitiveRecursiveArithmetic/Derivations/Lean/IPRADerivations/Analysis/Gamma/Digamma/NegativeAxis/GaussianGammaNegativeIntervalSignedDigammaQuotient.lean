import IPRADerivations.Analysis.Gamma.Digamma.NegativeAxis.GaussianGammaNegativeIntervalDigammaRate
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.Signs.GaussianGammaNegativeIntervalGammaSign
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.Signs.GaussianGammaNegativeIntervalNamedSign
import IPRADerivations.Analysis.Polynomials.Coefficients.NamedCoefficients.GaussianNamedConstantCoefficientDifferenceProduct

/-!
# Exact fixed-sign interpretation of the native Gamma unit quotient

Both endpoints are in one negative interval. Applying the same interval
sign to the two original Gamma names multiplies their unit quotient by
that sign. The reciprocal of the signed base is the signed original
reciprocal. Their product equals the original normalized Gamma quotient.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalSignedDigammaQuotient

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalDerivativeTarget (reciprocalData reciprocal_regular)
open GaussianGammaNegativeIntervalDigammaRate (quotientF quotientData cost minimumDenominator original_rate side_bound)
open GaussianGammaNegativeIntervalGammaSign (signedF signedData)
open GaussianGammaNegativeIntervalNamedSign (valueF valueData value_regular value_involution)
open GaussianGammaNegativeIntervalNative (argument negative_source negative_regular)
open GaussianGammaNegativeIntervalProductSign (signUnit)
open GaussianGammaNegativeIntervalStep (numerator denominator neighbor_guard quotient_input quotient_regular)
open GaussianGammaReciprocalInverse (gammaF gamma_product)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiply_at multiplyModulus recode_congr addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNameRingLaws (multiply_associative multiply_commutative oneF zeroF zero_at zero_fast)
open GaussianNamedConstantCoefficientDifferenceProduct (product_rule rhsF rhsData)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (qzero ofGaussian)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_left qmul_zero_right qzero_canonical)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaC7Name.nameF
local notation "Q" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "QD" => GaussianGammaNegativeIntervalStep.data
local notation "gd" => GaussianGammaNegativeIntervalNative.data
local notation "endF" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "endData" => GaussianGammaNegativeCriticalEndpoints.nameData

def signedQuotientF : PR 2 := GaussianNamedDifferenceQuotient.nameF signedF signedF
def signedQuotientData (a b N D : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data signedF signedF
    (signedData (numerator a b D) (denominator b D) N) (signedData a b N) oneCode D
def nameF : PR 2 := multiplyF (valueF P) signedQuotientF
def nameData (a b N D : PTm n) : PTm n :=
  multiplyData (valueF P) signedQuotientF (valueData P N (reciprocalData a b N)) (signedQuotientData a b N D)

theorem quotient_sign_cross (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hD : Γ ⊢[PRAAx] lt b D) :
    Γ ⊢[PRAAx] crossEquivalent signedQuotientF (valueF Q) (signedQuotientData a b N D) (valueData Q N (QD a b N D)) := by
  let s := signUnit (succ N)
  let x := gd (numerator a b D) (denominator b D) N
  let y := gd a b N
  let z := QD a b N D
  let v := valueData Q N z
  let w := multiplyData constantF gammaF qzero y
  have inp := quotient_input a b N D h hD
  have hp := inp.andE₁
  have hm := inp.andE₂.andE₁
  have hsep := inp.andE₂.andE₂
  have hc : Γ ⊢[PRAAx] GaussianRationalMetric.qsub s s ≐ GaussianRationalHorner.qmul (ofGaussian oneCode D) qzero :=
    (GaussianCoefficientNormOrder.qsub_self s).eqTrans (qmul_zero_right _).eqSymm
  have rule : Γ ⊢[PRAAx] crossEquivalent signedQuotientF (rhsF gammaF gammaF)
      (signedQuotientData a b N D) (rhsData gammaF gammaF s qzero x y oneCode D) :=
    product_rule gammaF gammaF s s qzero x y oneCode D hp hm hsep hc
  have hv := value_regular Q N z (quotient_regular a b N D h hD)
  have hw := multiply_fast constantF gammaF qzero y (constant_regular qzero) hm
  have discard : Γ ⊢[PRAAx] crossEquivalent (rhsF gammaF gammaF) (addF (valueF Q) zeroF)
      (addData v w) (addData v v) :=
    add_cross (valueF Q) (valueF Q) (valueF gammaF) zeroF v v w v hv hv hw (zero_fast v)
      (cross_refl _ _ hv) (GaussianNameRingLaws.constant_zero_multiply gammaF y v)
  exact cross_trans _ _ _ _ _ _ rule (cross_trans _ _ _ _ _ _ discard (GaussianNameRingLaws.add_zero (valueF Q) v hv))

theorem double_sign_product (f g : PR 2) (N x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (valueF f) (valueF g)) (multiplyF f g)
      (multiplyData (valueF f) (valueF g) (valueData f N x) (valueData g N y)) (multiplyData f g x y) := by
  let s := signUnit (succ N)
  let v := valueData g N y
  let z := multiplyData g f y x
  let u := multiplyData f (valueF g) x v
  have hs := constant_regular (Γ := Γ) s
  have hv := value_regular g N y hg
  have hz := multiply_fast g f y x hg hf
  have associate := multiply_associative constantF f (valueF g) s x v hs hf hv
  have inner : Γ ⊢[PRAAx] crossEquivalent (multiplyF f (valueF g)) (valueF (multiplyF g f)) u (valueData (multiplyF g f) N z) :=
    cross_trans _ _ _ _ _ _ (multiply_commutative f (valueF g) x v hf hv)
      (multiply_associative constantF g f s y x hs hg hf)
  have move := multiply_cross constantF constantF (multiplyF f (valueF g)) (valueF (multiplyF g f)) s s u
    (valueData (multiplyF g f) N z) hs hs (multiply_fast f (valueF g) x v hf hv)
    (value_regular (multiplyF g f) N z hz) (cross_refl _ _ hs) inner
  exact cross_trans _ _ _ _ _ _ associate
    (cross_trans _ _ _ _ _ _ move
      (cross_trans _ _ _ _ _ _ (value_involution (multiplyF g f) N z hz) (multiply_commutative g f y x hg hf)))

theorem signed_reciprocal_identity (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (valueF P) signedF) oneF
      (multiplyData (valueF P) signedF (valueData P N (reciprocalData a b N)) (signedData a b N)) (reciprocalData a b N) :=
  cross_trans _ _ _ _ _ _ (double_sign_product P gammaF N (reciprocalData a b N) (gd a b N)
    (reciprocal_regular a b N h) (negative_regular a b N h))
    (gamma_product (argument a b N) (succ (succ N)) b one b (negative_source a b N h))

theorem original_cross (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] lt b D) :
    Γ ⊢[PRAAx] crossEquivalent nameF quotientF (nameData a b N D) (quotientData a b N D) := by
  let x := reciprocalData a b N
  let y := QD a b N D
  let X := valueData P N x
  let Y := valueData Q N y
  have hx := reciprocal_regular a b N h
  have hy := quotient_regular a b N D h hD
  have hX := value_regular P N x hx
  have hY := value_regular Q N y hy
  have eq := quotient_sign_cross a b N D h hD
  have signedRegular : Γ ⊢[PRAAx] pointCN signedQuotientF (signedQuotientData a b N D) :=
    cross_trans _ _ _ _ _ _ eq (cross_symm _ _ _ _ eq)
  have move := multiply_cross (valueF P) (valueF P) signedQuotientF (valueF Q) X X (signedQuotientData a b N D) Y
    hX hX signedRegular hY (cross_refl _ _ hX) eq
  exact cross_trans _ _ _ _ _ _ move (double_sign_product P Q N x y hx hy)

theorem original_signed_rate (p a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) :
    Γ ⊢[PRAAx] independentRate nameF endF (nameData a b N D) (endData a b N) (cost a b N) (unit p) := by
  have inside := GaussianGammaNegativeIntervalInverseStepCoefficient.step_inside a b D h (side_bound p a b D hD)
  exact GaussianNamedRateTransport.transport quotientF endF nameF endF (quotientData a b N D) (endData a b N)
    (nameData a b N D) (endData a b N) (cost a b N) (unit p) (unit_positive p)
    (original_rate p a b N D h hD) (original_cross a b N D h inside)
    (cross_refl _ _ (GaussianGammaNegativeCriticalEndpoints.name_regular a b N h))

theorem actual_original_negative_interval_normalized_signed_quotient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((guard (var 0) (var 1) ⋏ lt (var 1) (var 3)) ⟶
        crossEquivalent nameF quotientF (nameData (var 0) (var 1) (var 2) (var 3)) (quotientData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_cross _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_negative_interval_signed_reciprocal_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶ crossEquivalent (multiplyF (valueF P) signedF) oneF
        (multiplyData (valueF P) signedF (valueData P (var 2) (reciprocalData (var 0) (var 1) (var 2)))
          (signedData (var 0) (var 1) (var 2))) (reciprocalData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (signed_reciprocal_identity _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalSignedDigammaQuotient
