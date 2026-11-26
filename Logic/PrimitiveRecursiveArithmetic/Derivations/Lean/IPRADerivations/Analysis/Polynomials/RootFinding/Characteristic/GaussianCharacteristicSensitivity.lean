import IPRADerivations.Analysis.Polynomials.RootFinding.Characteristic.GaussianCharacteristicFactorBounds
import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantStageError
import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantError
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNormEntries
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# Exact sensitivity of the original characteristic coefficients

The original Euclidean entry errors determine the coefficient errors of
the literal `det(XI - A)` producer. The two in the L1 entry error and the
power of two in the factor bound combine into the source constant
`2^N N! N (B+1)^(N-1)`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCharacteristicSensitivity

open_ipra
open GaussianCharacteristicFactorBounds (entryBounds entryDistances input)
open GaussianRationalCharacteristicPolynomial (characteristicTable table_shape polynomial coefficient run)
open GaussianCoefficientL1 (coefficientNorm subCoefficients)
open GaussianCoefficientNormOrder (coefficientNorm_congr subCoefficients_congr)
open GaussianRationalSyntheticBounds (natCode natCode_multiply natCode_represents)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalPowerDifference (budget)
open GaussianPolynomialDeterminantStageNorm (factorBounds)
open GaussianPolynomialDeterminantStageError (factorDifferences signed_term_error)
open GaussianPolynomialDeterminant (wordCode)
open RationalIntegerNormalization (normalize)
open RationalArithmetic (multiply)
open RationalArgmin (rationalLE rationalLE_congr)
open LeanProofs.IPRA.Foundations.RuntimePermutationFactorialBound (factorial)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sensitivity (N B : PTm n) : PTm n := pw two N*factorial N*N*pw (B+one) (pred N)

ipra_subst sensitivity [pw]

theorem integer_times_radius (K P Q : PTm n) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    multiply (natCode K) (normalize (ZT.ofNat P) Q) ≐ normalize (ZT.ofNat (K*P)) Q := by
  have left := RationalRepresentations.represents_multiply (Γ := Γ) (natCode K) (normalize (ZT.ofNat P) Q) _ _ _ _
    (natCode_represents K) (RationalIntegerNormalization.normalize_preserves_value _ _ hQ)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hQ) left
    (RationalIntegerNormalization.normalize_preserves_value _ _ hQ)
    (RationalAlgebra.positive_product (le_refl one) hQ) hQ
  ipra_lc

theorem sensitivity_identity (N B P : PTm n) : Γ ⊢[PRAAx]
    (factorial N*budget (two*(B+one)) one N)*(two*P) ≐ sensitivity N B*P := by
  refine .orE (zero_or_succ N) ?_ ?_
  · have empty := natEq (Prf.hyp0 : (N ≐ zero) :: Γ ⊢[PRAAx] N ≐ zero)
    apply deriveNat
    unfold sensitivity budget
    ipra_simps
    rw [empty]
    ring
  · have successor : (N ≐ succ (pred N)) :: Γ ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
    have expSplit := natEq ((congrAp2 powF successor (.eqRefl two)).eqTrans (pw_succ two (pred N)))
    have baseSplit := natEq (AnalyticNumberTheory.LocalFactor.pw_mul_base
      (Γ := (N ≐ succ (pred N)) :: Γ) two (B+one) (pred N))
    apply deriveNat
    unfold sensitivity budget
    ipra_simps
    rw [expSplit, baseSplit]
    ring

def wordRadius (N B P Q : PTm n) : PTm n :=
  multiply (natCode (budget (two*(B+one)) one N)) (normalize (ZT.ofNat (two*P)) Q)

ipra_subst wordRadius

theorem word_error (A C N B P Q w : PTm n) (ha : Γ ⊢[PRAAx] entryBounds A N B)
    (hc : Γ ⊢[PRAAx] entryBounds C N B) (hq : Γ ⊢[PRAAx] le one Q)
    (hd : Γ ⊢[PRAAx] entryDistances A C N P Q) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (subCoefficients
      (GaussianPolynomialDeterminantTerms.term (characteristicTable A N) N one w)
      (GaussianPolynomialDeterminantTerms.term (characteristicTable C N) N one w) (succ (N*one)))) (wordRadius N B P Q) := by
  have fa : Γ ⊢[PRAAx] factorBounds (characteristicTable A N) N w (two*(B+one)) := by
    simpa [factorBounds,Syn.shift] using GaussianCharacteristicFactorBounds.factor_bounds A N B w ha
  have fc : Γ ⊢[PRAAx] factorBounds (characteristicTable C N) N w (two*(B+one)) := by
    simpa [factorBounds,Syn.shift] using GaussianCharacteristicFactorBounds.factor_bounds C N B w hc
  have fd : Γ ⊢[PRAAx] factorDifferences (characteristicTable A N) (characteristicTable C N) N one w
        (normalize (ZT.ofNat (two*P)) Q) := by
    simpa [factorDifferences, GaussianPolynomialDeterminantStageError.factorDifference, Syn.shift] using
      GaussianCharacteristicFactorBounds.factor_difference_bounds A C N P Q w hq hd
  exact signed_term_error _ _ _ _ _ _ _ (table_shape A N) (table_shape C N) fa fc fd

theorem word_errors (A C N B P Q : PTm n) (ha : Γ ⊢[PRAAx] entryBounds A N B)
    (hc : Γ ⊢[PRAAx] entryBounds C N B) (hq : Γ ⊢[PRAAx] le one Q)
    (hd : Γ ⊢[PRAAx] entryDistances A C N P Q) : Γ ⊢[PRAAx] GaussianPolynomialDeterminantError.summandBounds
      (characteristicTable A N) (characteristicTable C N) N one (wordRadius N B P Q) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Foundations.RuntimePermutationWords.count (Syn.shift N)) :: Γ.map Fm.shift
  have ha' : Δ ⊢[PRAAx] entryBounds (Syn.shift A) (Syn.shift N) (Syn.shift B) := by
    simpa [Δ,Fm.shift,Syn.shift] using ha.shift.wk
  have hc' : Δ ⊢[PRAAx] entryBounds (Syn.shift C) (Syn.shift N) (Syn.shift B) := by
    simpa [Δ,Fm.shift,Syn.shift] using hc.shift.wk
  have hq' : Δ ⊢[PRAAx] le one (Syn.shift Q) := by
    simpa [Δ,Fm.shift,Syn.shift,one] using hq.shift.wk
  have hd' : Δ ⊢[PRAAx] entryDistances (Syn.shift A) (Syn.shift C) (Syn.shift N) (Syn.shift P) (Syn.shift Q) := by
    simpa [Δ,Fm.shift,Syn.shift] using hd.shift.wk
  have value := word_error _ _ _ _ _ _ (wordCode (Syn.shift N) (var 0)) ha' hc' hq' hd'
  simpa [Δ,GaussianPolynomialDeterminantError.termDifference, GaussianPolynomialDeterminant.summand,
    GaussianPolynomialDeterminant.width,Syn.shift,one] using value

theorem coefficient_norm_error (A C N B P Q : PTm n) (ha : Γ ⊢[PRAAx] entryBounds A N B)
    (hc : Γ ⊢[PRAAx] entryBounds C N B) (hq : Γ ⊢[PRAAx] le one Q) (hd : Γ ⊢[PRAAx] entryDistances A C N P Q) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (subCoefficients (polynomial A N) (polynomial C N) (succ N)))
      (normalize (ZT.ofNat (sensitivity N B*P)) Q) := by
  have estimate := GaussianPolynomialDeterminantError.determinant_error_bound _ _ _ _ _ (word_errors A C N B P Q ha hc hq hd)
  have width : Γ ⊢[PRAAx] succ (N*one) ≐ succ N := congrSucc ((mul_comm N one).eqTrans (one_mul N))
  have rhs : Γ ⊢[PRAAx] multiply (natCode (factorial N)) (wordRadius N B P Q) ≐ normalize (ZT.ofNat (sensitivity N B*P)) Q := by
    unfold wordRadius
    refine (RationalAlgebra.multiply_associative _ _ _).eqSymm.eqTrans ?_
    refine (RationalAlgebra.multiply_congr (natCode_multiply _ _) (.eqRefl _)).eqTrans ?_
    refine (integer_times_radius _ _ _ hq).eqTrans ?_
    ipra_congr (normalize (ZT.ofNat (var 0)) (var 1) : PTm 2) with [sensitivity_identity N B P, .eqRefl Q]
  exact rationalLE_congr (coefficientNorm_congr (subCoefficients_congr (.eqRefl _) (.eqRefl _) width)) rhs estimate

theorem coefficient_error (A C N B P Q i : PTm n) (h : Γ ⊢[PRAAx] input A C N B P Q)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] distanceBounded (coefficient A N i) (coefficient C N i) (sensitivity N B*P) Q := by
  have bounds := Prf.andE₂ (Prf.andE₂ h)
  have errors := Prf.andE₂ (Prf.andE₂ bounds)
  have hq := Prf.andE₁ errors
  exact GaussianCoefficientNormEntries.bounded_coefficient_difference _ _ _ _ _ _ hq
    (coefficient_norm_error A C N B P Q (.andE₁ bounds) (.andE₁ (.andE₂ bounds)) hq (.andE₂ errors))
    ((succ_monus_succ _ _).eqTrans hi)

theorem returned_coefficient_error (A C N B P Q i : PTm n) (h : Γ ⊢[PRAAx] input A C N B P Q)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] distanceBounded (entry (run A N) i) (entry (run C N) i) (sensitivity N B*P) Q := by
  have a := Foundations.SequenceComposition.entry_congr (GaussianRationalCharacteristicPolynomial.program_at (Γ := Γ) A N) (.eqRefl i)
  have c := Foundations.SequenceComposition.entry_congr (GaussianRationalCharacteristicPolynomial.program_at (Γ := Γ) C N) (.eqRefl i)
  exact GaussianRationalReciprocal.bound_congr (GaussianRationalSyntheticDivision.qsub_congr a c).eqSymm
    (.eqRefl _) (.eqRefl _) (coefficient_error A C N B P Q i h hi)

theorem actual_characteristic_sensitivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ le (var 6) (var 2) ⟶
      distanceBounded (coefficient (var 0) (var 2) (var 6)) (coefficient (var 1) (var 2) (var 6))
        (sensitivity (var 2) (var 3)*var 4) (var 5)) :=
  closeUniv 7 (.impI (.impI (coefficient_error _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_returned_characteristic_sensitivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ le (var 6) (var 2) ⟶
      distanceBounded (entry (run (var 0) (var 2)) (var 6)) (entry (run (var 1) (var 2)) (var 6))
        (sensitivity (var 2) (var 3)*var 4) (var 5)) :=
  closeUniv 7 (.impI (.impI (returned_coefficient_error _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

def sensitivityF : PR 2 := PTm.toPR (sensitivity (var 0) (var 1))

theorem sensitivity_at (N B : PTm n) : Γ ⊢[PRAAx] ap2 sensitivityF N B ≐ sensitivity N B := by
  simpa [sensitivityF,ap2] using toPR_eq (Γ := Γ) (sensitivity (var 0) (var 1) : PTm 2) ![N,B]

theorem actual_sensitivity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 sensitivityF (var 0) (var 1) ≐ sensitivity (var 0) (var 1)) :=
  closeUniv 2 (sensitivity_at _ _)

end LeanProofs.IPRA.Analysis.GaussianCharacteristicSensitivity
