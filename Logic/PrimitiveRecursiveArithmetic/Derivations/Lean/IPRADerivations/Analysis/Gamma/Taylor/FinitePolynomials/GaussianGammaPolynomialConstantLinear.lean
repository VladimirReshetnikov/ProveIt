import IPRADerivations.Analysis.Polynomials.Coefficients.Operations.GaussianPolynomialFirstCoefficients
import IPRADerivations.Analysis.Gamma.Taylor.NamedCoefficients.GaussianGammaCofinalCoefficientName
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponentialStability

/-!
# Actual zero constant and unit linear coefficients of Gamma polynomials

Original buffer lookup proves the exponent input has zero constant and
the literal sampled gamma-H_N linear coefficient. Original convolution
and genuine internal induction give zero constant and unit linear
coefficient for the original Euler head. The actual finite exponential
has constant one. Consequently the whole original finite polynomial has
constant zero and, at every positive exponential cutoff, linear one.
This identifies the first nonzero cofinal coefficient with the regular
constant-one name. The quadratic gamma coefficient remains separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPolynomialConstantLinear

open_ipra
open GaussianRationalHorner (qzero qmul qadd)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qzero_canonical qone_canonical)
open GaussianRationalPolynomialBuffers (leftPad)
open GaussianRationalMonicReduction (singleton)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaLinearCoefficient (coefficient)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianRationalPolynomialExponentialStability (exponent_congr)
open GaussianRationalPolynomialExponential (polynomial)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem linear_buffer_constant (q N L : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianGammaExponentCoefficientPolynomial.linear q N L) (degree L) ≐ qzero := by
  have len := GaussianGammaLinearCoefficient.monomial_length (Γ := Γ) (coefficient q N)
  exact (entry_congr (.eqRefl _)
    (show Γ ⊢[PRAAx] degree L ≐ succ L+one by unfold degree; ipra_ring)).eqTrans
      ((GaussianRationalPolynomialBuffers.pad_tail _ (succ L) one
        (le_congr (.eqRefl two) len.eqSymm (le_refl two))).eqTrans
          (GaussianGammaLinearCoefficient.monomial_constant _))

theorem linear_buffer_linear (q N L : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianGammaExponentCoefficientPolynomial.linear q N L) (succ L) ≐ coefficient q N := by
  have len := GaussianGammaLinearCoefficient.monomial_length (Γ := Γ) (coefficient q N)
  exact (entry_congr (.eqRefl _)
    (show Γ ⊢[PRAAx] succ L ≐ succ L+zero by ipra_ring)).eqTrans
      ((GaussianRationalPolynomialBuffers.pad_tail _ (succ L) zero
        (le_congr (.eqRefl one) len.eqSymm (le_succ_self one))).eqTrans
          (GaussianGammaLinearCoefficient.monomial_leading _))

theorem input_constant (q N L : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianGammaExponentCoefficientPolynomial.polynomial q N L) (degree L) ≐ qzero :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ (le_refl (succ (degree L)))).eqTrans
    ((qadd_congr (linear_buffer_constant q N L) (GaussianGammaZetaCoefficientPolynomial.polynomial_constant q N L)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add qzero qzero_canonical))

theorem input_linear (q N L : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianGammaExponentCoefficientPolynomial.polynomial q N L) (monus (degree L) one) ≐ coefficient q N := by
  have idx : Γ ⊢[PRAAx] monus (degree L) one ≐ succ L :=
    (succ_monus_succ (succ L) zero).eqTrans (monus_zero (succ L))
  have tail : Γ ⊢[PRAAx] entry (GaussianGammaZetaCoefficientPolynomial.polynomial q N L) (succ L) ≐ qzero :=
    (entry_congr (.eqRefl _) idx.eqSymm).eqTrans (GaussianGammaZetaCoefficientPolynomial.polynomial_linear q N L)
  exact (entry_congr (.eqRefl _) idx).eqTrans
    ((GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ (le_succ_self (degree L))).eqTrans
      ((qadd_congr (linear_buffer_linear q N L) tail).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalMetric.qsub_canonical _ _))))

theorem factor_constant (N : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianGammaEulerFactorPolynomial.polynomial N) one ≐ qone := by
  have len := GaussianRationalMonicReduction.singleton_length (Γ := Γ) qone
  have point : Γ ⊢[PRAAx] entry (GaussianGammaEulerFactorPolynomial.constant : PTm n) one ≐ qone :=
    (entry_congr (.eqRefl _) (show Γ ⊢[PRAAx] one ≐ one+zero by ipra_ring)).eqTrans
      ((GaussianRationalPolynomialBuffers.pad_tail (singleton qone) one zero
        (le_congr (.eqRefl one) len.eqSymm (le_refl one))).eqTrans
          (GaussianRationalMonicReduction.singleton_lookup qone))
  exact (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ (le_refl two)).eqTrans
    ((qadd_congr (GaussianGammaLinearCoefficient.monomial_constant _) point).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add qone qone_canonical))

def headLowLaw (N : PTm n) : Fm PTm n :=
  entry (GaussianGammaEulerHeadPolynomial.polynomial N) (succ N) ≐ qzero ⋏
    entry (GaussianGammaEulerHeadPolynomial.polynomial N) (monus (succ N) one) ≐ qone
ipra_subst headLowLaw

theorem head_low_zero : Γ ⊢[PRAAx] headLowLaw (zero : PTm n) :=
  .andI ((entry_congr GaussianGammaEulerHeadPolynomial.polynomial_zero (.eqRefl one)).eqTrans
    (GaussianGammaLinearCoefficient.monomial_constant qone))
    ((entry_congr GaussianGammaEulerHeadPolynomial.polynomial_zero (monus_self one)).eqTrans
      (GaussianGammaLinearCoefficient.monomial_leading qone))

theorem head_low_step (N : PTm n) (ih : Γ ⊢[PRAAx] headLowLaw N) : Γ ⊢[PRAAx] headLowLaw (succ N) := by
  have deg : Γ ⊢[PRAAx] succ (succ N) ≐ succ N+one := by ipra_ring
  have constant := (entry_congr (GaussianGammaEulerHeadPolynomial.polynomial_succ N) deg).eqTrans
    ((GaussianPolynomialFirstCoefficients.constant_value _ _ _ _).eqTrans
      ((qmul_congr ih.andE₁ (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)))
  have linear := (entry_congr (GaussianGammaEulerHeadPolynomial.polynomial_succ N) (congrMonus deg (.eqRefl one))).eqTrans
    ((GaussianPolynomialFirstCoefficients.linear_value _ _ _ _ (zero_lt_succ N) (le_refl one)).eqTrans
      ((qadd_congr ((qmul_congr ih.andE₁ (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _))
        ((qmul_congr ih.andE₂ (factor_constant N)).eqTrans (GaussianPolynomialDeterminantTerms.one_mul_canonical qone qone_canonical))).eqTrans
          (GaussianRationalSyntheticDivision.qzero_add qone qone_canonical)))
  exact .andI constant linear

theorem head_low (N : PTm n) : Γ ⊢[PRAAx] headLowLaw N := by
  have all : Γ ⊢[PRAAx] .all (headLowLaw (var 0)) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_headLowLaw]
    · exact head_low_zero
    · exact head_low_step _ Prf.hyp0
  simpa only [subst_headLowLaw,Syn.subst_var,Syn.inst_zero] using all.allE N

theorem constant_reader (C N : PTm n) : Γ ⊢[PRAAx] exponentCoefficient C N zero ≐ entry C N :=
  (exponent_inside C N zero (zero_le N)).eqTrans (entry_congr (.eqRefl _) (monus_zero N))

/-- The actual finite exponential constant is one at every internal
cutoff, derived from zero constant support and the original stage zero. -/
theorem exponential_constant (C N K : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero) : Γ ⊢[PRAAx]
    entry (polynomial C N K) (K*N) ≐ qone := by
  have cut := GaussianRationalPolynomialExponentialStability.finite_exponential_cutoff C N K zero hC (zero_le N) (zero_le K)
  have initial := (exponent_congr (Γ := Γ) (GaussianRationalPolynomialExponential.stage_zero C N K) (zero_mul N) (.eqRefl zero)).eqTrans
    ((constant_reader (singleton qone) zero).eqTrans (GaussianRationalMonicReduction.singleton_lookup qone))
  exact (constant_reader (polynomial C N K) (K*N)).eqSymm.eqTrans (cut.eqTrans initial)

theorem whole_constant (q R L K : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianGammaFiniteCoefficientPolynomial.polynomial q R L K) (GaussianGammaFiniteCoefficientPolynomial.totalDegree R L K) ≐ qzero :=
  (GaussianPolynomialFirstCoefficients.constant_value _ _ _ _).eqTrans
    ((qmul_congr (head_low (two*R)).andE₁ (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _))

theorem whole_linear (q R L K : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    entry (GaussianGammaFiniteCoefficientPolynomial.polynomial q R L K)
      (monus (GaussianGammaFiniteCoefficientPolynomial.totalDegree R L K) one) ≐ qone := by
  have hD := le_trans (le_succ_self one) (GaussianGammaZetaDegreeName.degree_positive (Γ := Γ) L)
  have expDegree : Γ ⊢[PRAAx] le one (K*degree L) :=
    le_congr (by ipra_ring) (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hK hD)
  have expConst := exponential_constant (Γ := Γ) _ _ K (input_constant q (two*R) L)
  exact (GaussianPolynomialFirstCoefficients.linear_value _ _ _ _ (zero_lt_succ (two*R)) expDegree).eqTrans
    ((qadd_congr ((qmul_congr (head_low (two*R)).andE₁ (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _))
      ((qmul_congr (head_low (two*R)).andE₂ expConst).eqTrans (GaussianPolynomialDeterminantTerms.one_mul_canonical qone qone_canonical))).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add qone qone_canonical))

def firstObservation (p R : PTm n) : PTm n := entry
  (GaussianGammaFiniteCoefficientPolynomial.polynomial
    (GaussianGammaCofinalCoefficientName.coefficientPrecision (succ p) R) R
    (GaussianGammaCofinalCoefficientName.degreeCutoff (succ p) R) (GaussianGammaCofinalCoefficientName.exponentialCutoff (succ p) R))
  (monus (GaussianGammaFiniteCoefficientPolynomial.totalDegree R
    (GaussianGammaCofinalCoefficientName.degreeCutoff (succ p) R) (GaussianGammaCofinalCoefficientName.exponentialCutoff (succ p) R)) one)

theorem first_observation_one (p R : PTm n) : Γ ⊢[PRAAx] firstObservation p R ≐ qone :=
  whole_linear _ _ _ _ (le_trans (zero_lt_succ p) (GaussianGammaCofinalCoefficientName.exponential_cutoff_cofinal (succ p) R))
theorem first_coefficient_named (p R : PTm n) : Γ ⊢[PRAAx] firstObservation p R ≐ ap2 GaussianNameRingLaws.oneF p R :=
  (first_observation_one p R).eqTrans (GaussianNameRingLaws.one_at p R).eqSymm

theorem original_finite_Gamma_zero_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entry (GaussianGammaFiniteCoefficientPolynomial.polynomial (var 0) (var 1) (var 2) (var 3))
      (GaussianGammaFiniteCoefficientPolynomial.totalDegree (var 1) (var 2) (var 3)) ≐ qzero) :=
  closeUniv 4 (whole_constant _ _ _ _)
theorem original_cofinal_Gamma_first_coefficient_is_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (firstObservation (var 0) (var 1) ≐ ap2 GaussianNameRingLaws.oneF (var 0) (var 1)) :=
  closeUniv 2 (first_coefficient_named _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaPolynomialConstantLinear
