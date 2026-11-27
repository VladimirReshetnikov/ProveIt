import IPRADerivations.Analysis.Polynomials.RootFinding.Characteristic.GaussianCharacteristicFactorBounds
import IPRADerivations.Analysis.Polynomials.Determinants.ErrorBounds.GaussianPolynomialDeterminantStageNorm
import IPRADerivations.Analysis.Polynomials.Determinants.ErrorBounds.GaussianPolynomialDeterminantNorm
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientNormEntries
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# Original matrix-entry bounds for actual characteristic coefficients

The numerical bound is 2^N N! (B+1)^N. Actual entry-to-factor bounds,
actual product-stage estimates and the retained determinant sum derive
the whole coefficient norm and every original coefficient's Euclidean
bound. No characteristic norm or coefficient magnitude law is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCharacteristicMagnitude

open_ipra
open GaussianRationalCharacteristicPolynomial (characteristicTable polynomial coefficient polynomial_length)
open GaussianCharacteristicFactorBounds (entryBounds)
open GaussianCoefficientL1 (coefficientNorm)
open GaussianRationalSyntheticBounds (natCode natCode_multiply natCode_congr)
open LeanProofs.IPRA.Foundations.RuntimePermutationFactorialBound (factorial)
open RationalArgmin (rationalLE rationalLE_congr)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def magnitude (N B : PTm n) : PTm n := pw two N*factorial N*pw (B+one) N
def input (A N B : PTm n) : Fm PTm n := GaussianRationalRowElimination.shape A N N ⋏ entryBounds A N B
ipra_subst magnitude
ipra_subst input

theorem word_factor_bounds (A N B w : PTm n) (h : Γ ⊢[PRAAx] entryBounds A N B) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantStageNorm.factorBounds (characteristicTable A N) N w (two*(B+one)) := by
  simpa [GaussianPolynomialDeterminantStageNorm.factorBounds,Syn.shift] using GaussianCharacteristicFactorBounds.factor_bounds A N B w h

theorem signed_word_norm (A N B w : PTm n) (h : Γ ⊢[PRAAx] entryBounds A N B) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (GaussianPolynomialDeterminantTerms.term (characteristicTable A N) N one w))
      (natCode (pw (two*(B+one)) N)) :=
  GaussianPolynomialDeterminantStageNorm.signed_term_norm _ _ _ _ _
    (GaussianRationalCharacteristicPolynomial.table_shape A N) (word_factor_bounds A N B w h)

theorem signed_summand_bounds (A N B : PTm n) (h : Γ ⊢[PRAAx] entryBounds A N B) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantNorm.summandBounds (characteristicTable A N) N one (natCode (pw (two*(B+one)) N)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] entryBounds (Syn.shift A) (Syn.shift N) (Syn.shift B) := by
    simpa only [Fm.shift,GaussianCharacteristicFactorBounds.subst_entryBounds,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  have actual := signed_word_norm (Γ := lt (var 0) (Foundations.RuntimePermutationWords.count (Syn.shift N)) :: Γ.map Fm.shift)
    (Syn.shift A) (Syn.shift N) (Syn.shift B) (GaussianPolynomialDeterminant.wordCode (Syn.shift N) (var 0)) hs.wk
  simpa only [GaussianPolynomialDeterminant.summand,Syn.shift,
    GaussianRationalCharacteristicPolynomial.subst_characteristicTable,GaussianRationalSyntheticBounds.subst_natCode,
    pw,subst_ap2,PTm.subst_mul,PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using actual

theorem magnitude_identity (N B : PTm n) : Γ ⊢[PRAAx] factorial N*pw (two*(B+one)) N ≐ magnitude N B :=
  (congrMul (.eqRefl _) (AnalyticNumberTheory.LocalFactor.pw_mul_base two (B+one) N)).eqTrans (by unfold magnitude; ipra_ring)

theorem coefficient_norm_bound (A N B : PTm n) (h : Γ ⊢[PRAAx] entryBounds A N B) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (polynomial A N)) (natCode (magnitude N B)) :=
  rationalLE_congr (.eqRefl _)
    ((natCode_multiply _ _).eqTrans (natCode_congr (magnitude_identity N B)))
    (GaussianPolynomialDeterminantNorm.determinant_norm_bound _ _ _ _ (signed_summand_bounds A N B h))

theorem coefficient_l1_bound (A N B i : PTm n) (h : Γ ⊢[PRAAx] entryBounds A N B) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] rationalLE (GaussianRationalL1.qL1 (coefficient A N i)) (natCode (magnitude N B)) :=
  RationalArgmin.transitive (GaussianCoefficientNormEntries.coefficient_entry_bound (polynomial A N) i
    (lt_congr (.eqRefl _) (polynomial_length A N).eqSymm ((succ_monus_succ _ _).eqTrans hi)))
      (coefficient_norm_bound A N B h)

theorem coefficient_magnitude_bound (A N B i : PTm n) (h : Γ ⊢[PRAAx] entryBounds A N B) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] bounded (coefficient A N i) (magnitude N B) one :=
  GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (le_refl one) (coefficient_l1_bound A N B i h hi)

theorem source_coefficient_magnitude (A N B i : PTm n) (h : Γ ⊢[PRAAx] input A N B) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] bounded (coefficient A N i) (magnitude N B) one := coefficient_magnitude_bound A N B i (.andE₂ h) hi

theorem returned_coefficient_magnitude (A N B i : PTm n) (h : Γ ⊢[PRAAx] entryBounds A N B) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] bounded (Foundations.MasterCertificate.entry (GaussianRationalCharacteristicPolynomial.run A N) i) (magnitude N B) one :=
  GaussianRationalReciprocal.bound_congr
    (Foundations.SequenceComposition.entry_congr (GaussianRationalCharacteristicPolynomial.program_at A N) (.eqRefl _)).eqSymm
    (.eqRefl _) (.eqRefl _) (coefficient_magnitude_bound A N B i h hi)

def magnitudeF : PR 2 := PTm.toPR (magnitude (var 0) (var 1))
theorem magnitude_at (N B : PTm n) : Γ ⊢[PRAAx] ap2 magnitudeF N B ≐ magnitude N B := by
  simpa [magnitudeF,ap2] using toPR_eq (Γ := Γ) (magnitude (var 0) (var 1) : PTm 2) ![N,B]

theorem actual_characteristic_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (entryBounds (var 0) (var 1) (var 2) ⟶ rationalLE (coefficientNorm (polynomial (var 0) (var 1)))
      (natCode (magnitude (var 1) (var 2)))) := closeUniv 3 (.impI (coefficient_norm_bound _ _ _ Prf.hyp0))
theorem actual_characteristic_coefficient_l1_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entryBounds (var 0) (var 1) (var 2) ⟶ le (var 3) (var 1) ⟶
      rationalLE (GaussianRationalL1.qL1 (coefficient (var 0) (var 1) (var 3))) (natCode (magnitude (var 1) (var 2)))) :=
  closeUniv 4 (.impI (.impI (coefficient_l1_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_characteristic_coefficient_magnitude_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) ⟶ le (var 3) (var 1) ⟶
      bounded (coefficient (var 0) (var 1) (var 3)) (magnitude (var 1) (var 2)) one) :=
  closeUniv 4 (.impI (.impI (source_coefficient_magnitude _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_coefficient_magnitude_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entryBounds (var 0) (var 1) (var 2) ⟶ le (var 3) (var 1) ⟶ bounded
      (Foundations.MasterCertificate.entry (GaussianRationalCharacteristicPolynomial.run (var 0) (var 1)) (var 3))
      (magnitude (var 1) (var 2)) one) :=
  closeUniv 4 (.impI (.impI (returned_coefficient_magnitude _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_magnitude_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 magnitudeF (var 0) (var 1) ≐ magnitude (var 0) (var 1)) := closeUniv 2 (magnitude_at _ _)

end LeanProofs.IPRA.Analysis.GaussianCharacteristicMagnitude
