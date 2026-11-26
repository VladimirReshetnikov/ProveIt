import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponential
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.GaussianBivariatePowerExpansion
import IPRADerivations.Analysis.Exponential.Polynomials.LogarithmExponentialCoefficients

/-!
# Literal logarithm coefficient polynomials and finite exponential composition

The original finite logarithm in Gamma (C3)--(C4) is
`H_d(w)=sum_{k<d} (-1)^k*w^(k+1)/(k+1)`.  Its actual descending
coefficient list is constructed below, including its zero constant term.
The normalized coefficient has its genuine signed rational representation.
The existing actual power expansion proves its literal finite sum value,
then the verified exponential polynomial is specialized to THIS buffer.

All degrees, factorial cutoffs and raw Gaussian query codes are numerical.
No logarithm, power-series coefficient, or composition value law is a
premise.  Comparison with the older cleared-integer logarithm sampler and
the analytic C4 tail/error conclusion remain separate bridges.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul canonical evaluate ofGaussian represents)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qzero_add qzero_canonical canonicalCoefficients)
open GaussianRationalReciprocal (power)
open LogarithmExponentialCoefficients (evenBit oddBit)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def signNumerator (k : PTm n) : PTm n :=
  ComplexLogarithmRemainder.code (⟨evenBit k,oddBit k⟩ : ZT n) (ZT.ofNat zero)
def coefficient (k : PTm n) : PTm n := ofGaussian (signNumerator k) (succ k)
def sourceCoefficient (e : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg e) qzero (coefficient (pred e))
def rowBody : PTm 2 := sourceCoefficient (monus (var 1) (var 0))
def polynomial (d : PTm n) : PTm n := sequence rowBody (succ d) d

@[simp] theorem subst_signNumerator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (signNumerator k) = signNumerator (Syn.subst σ k) := by simp [signNumerator,ZT.subst,ZT.ofNat,evenBit,oddBit]
@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (coefficient k) = coefficient (Syn.subst σ k) := by simp [coefficient]
@[simp] theorem subst_sourceCoefficient {m : ℕ} (σ : Fin n → PTm m) (e : PTm n) :
    Syn.subst σ (sourceCoefficient e) = sourceCoefficient (Syn.subst σ e) := by simp [sourceCoefficient,Signum.sg]
@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (d : PTm n) :
    Syn.subst σ (polynomial d) = polynomial (Syn.subst σ d) := by simp [polynomial]

theorem coefficient_represents (k : PTm n) : Γ ⊢[PRAAx] represents (coefficient k) (signNumerator k) (succ k) :=
  GaussianRationalHorner.ofGaussian_represents _ _ (zero_lt_succ _)
theorem coefficient_canonical (k : PTm n) : Γ ⊢[PRAAx] canonical (coefficient k) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (zero_lt_succ _)

/-- The same logarithmic coefficient in the earlier actual factorial/kernel
encoding.  The native cross identity is derived from its proved kernel,
then the two actual normalized codes are compared at one common divisor. -/
def kernelNumerator (k : PTm n) : PTm n :=
  ComplexLogarithmRemainder.code (LogarithmExponentialCoefficients.kernel k) (ZT.ofNat zero)
def kernelCoefficient (k : PTm n) : PTm n :=
  ofGaussian (kernelNumerator k) (Products.fact (succ k))
@[simp] theorem subst_kernelNumerator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (kernelNumerator k) = kernelNumerator (Syn.subst σ k) := by
  simp [kernelNumerator,LogarithmExponentialCoefficients.kernel,LogarithmExponentialCoefficients.value,ZT.subst,ZT.ofNat]
@[simp] theorem subst_kernelCoefficient {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (kernelCoefficient k) = kernelCoefficient (Syn.subst σ k) := by
  simp [kernelCoefficient,Products.fact]

theorem coefficient_kernel_cross (k : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
    (ComplexLogarithmRemainder.scale (Products.fact (succ k)) (signNumerator k))
    (ComplexLogarithmRemainder.scale (succ k) (kernelNumerator k)) := by
  apply GaussianRootAlgebra.equal_of_values
  · have h := ZT.toZ_eq (LogarithmExponentialCoefficients.logarithmic_coefficient (Γ := Γ) k)
    simpa only [kernelNumerator,signNumerator,ComplexLogarithmRemainder.scale,
      ComplexLogarithmRemainder.eval_re_code,ZT.toZ_mul,ZT.toZ_ofNat] using h.symm
  · simp only [kernelNumerator,signNumerator,ComplexLogarithmRemainder.scale,
      ComplexLogarithmRemainder.eval_im_code,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_zero,map_zero]
    ring

theorem coefficient_kernel (k : PTm n) : Γ ⊢[PRAAx] coefficient k ≐ kernelCoefficient k := by
  let D := succ k*Products.fact (succ k)
  have hf := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) (succ k)
  have hD : Γ ⊢[PRAAx] le one D := GaussianRationalHorner.positive_product _ _ (zero_lt_succ k) hf
  have left : Γ ⊢[PRAAx] represents (coefficient k)
      (ComplexLogarithmRemainder.scale (Products.fact (succ k)) (signNumerator k)) D :=
    GaussianRationalSyntheticDivision.rescale_to _ _ _ _ _ (coefficient_represents k) (.eqRefl _)
  have right : Γ ⊢[PRAAx] represents (kernelCoefficient k)
      (ComplexLogarithmRemainder.scale (succ k) (kernelNumerator k)) D :=
    GaussianRationalSyntheticDivision.rescale_to _ _ _ _ _
      (GaussianRationalHorner.ofGaussian_represents (kernelNumerator k) (Products.fact (succ k)) hf)
      (mul_comm _ _)
  have right' : Γ ⊢[PRAAx] represents (kernelCoefficient k)
      (ComplexLogarithmRemainder.scale (Products.fact (succ k)) (signNumerator k)) D :=
    GaussianRationalHorner.represents_congr (.eqRefl _)
      (GaussianRootAlgebra.equal_symm (coefficient_kernel_cross k)) (.eqRefl _) right
  exact GaussianRationalHorner.canonical_unique (coefficient k) (kernelCoefficient k) _ D
    (coefficient_canonical k) (GaussianRationalHorner.ofGaussian_canonical _ _ hf) hD left right'

theorem coefficient_congr {k l : PTm n} (h : Γ ⊢[PRAAx] k ≐ l) : Γ ⊢[PRAAx] coefficient k ≐ coefficient l := by
  simpa only [subst_coefficient,Syn.subst_var,Matrix.cons_val_zero,Matrix.head_cons] using
    (Prf.eqCongr (Γ := Γ) (coefficient (var 0) : PTm 1) (σ := ![k]) (σ' := ![l]) (fun i => by fin_cases i; exact h))
theorem source_congr {e f : PTm n} (h : Γ ⊢[PRAAx] e ≐ f) : Γ ⊢[PRAAx] sourceCoefficient e ≐ sourceCoefficient f := by
  simpa only [subst_sourceCoefficient,Syn.subst_var,Matrix.cons_val_zero,Matrix.head_cons] using
    (Prf.eqCongr (Γ := Γ) (sourceCoefficient (var 0) : PTm 1) (σ := ![e]) (σ' := ![f]) (fun i => by fin_cases i; exact h))
theorem source_zero : Γ ⊢[PRAAx] sourceCoefficient (zero : PTm n) ≐ qzero :=
  RationalArithmetic.select_zero _ _ _ Signum.sg_zero
theorem source_succ (k : PTm n) : Γ ⊢[PRAAx] sourceCoefficient (succ k) ≐ coefficient k :=
  (RationalArithmetic.select_one _ _ _ (Signum.sg_succ k)).eqTrans (coefficient_congr (pred_succ k))
theorem source_canonical (e : PTm n) : Γ ⊢[PRAAx] canonical (sourceCoefficient e) := by
  refine .orE (zero_or_succ e) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr ((source_congr Prf.hyp0).eqTrans source_zero) qzero_canonical
  · exact GaussianRationalHorner.canonical_congr ((source_congr Prf.hyp0).eqTrans (source_succ _)) (coefficient_canonical _)

theorem polynomial_length (d : PTm n) : Γ ⊢[PRAAx] length (polynomial d) ≐ succ d := sequence_length _ _ _
theorem row_body_at (d i : PTm n) : inst2 rowBody i d = sourceCoefficient (monus d i) := by simp [rowBody,inst2]
theorem polynomial_lookup (d i : PTm n) (hi : Γ ⊢[PRAAx] le i d) : Γ ⊢[PRAAx]
    entry (polynomial d) i ≐ sourceCoefficient (monus d i) := by
  simpa only [polynomial,row_body_at] using sequence_decode (Γ := Γ) rowBody (x := d) ((succ_monus_succ _ _).eqTrans hi)
theorem polynomial_exponent (d e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    entry (polynomial d) (monus d e) ≐ sourceCoefficient e :=
  (polynomial_lookup _ _ (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
    (source_congr (GaussianRationalMonicReconstruction.complement d e he))
theorem polynomial_constant (d : PTm n) : Γ ⊢[PRAAx] entry (polynomial d) d ≐ qzero :=
  (polynomial_lookup d d (le_refl _)).eqTrans ((source_congr (monus_self d)).eqTrans source_zero)
theorem polynomial_positive_coefficient (d k : PTm n) (hk : Γ ⊢[PRAAx] lt k d) : Γ ⊢[PRAAx]
    entry (polynomial d) (monus d (succ k)) ≐ coefficient k :=
  (polynomial_exponent d (succ k) hk).eqTrans (source_succ k)
theorem polynomial_kernel_coefficient (d k : PTm n) (hk : Γ ⊢[PRAAx] lt k d) : Γ ⊢[PRAAx]
    entry (polynomial d) (monus d (succ k)) ≐ kernelCoefficient k :=
  (polynomial_positive_coefficient d k hk).eqTrans (coefficient_kernel k)
theorem polynomial_canonical (d : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (polynomial d) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (polynomial d))) :: Γ.map Fm.shift
  have hd : Δ ⊢[PRAAx] le (var 0) (Syn.shift d) :=
    (succ_monus_succ _ _).eqSymm.eqTrans
      (lt_congr (.eqRefl _) (polynomial_length (Syn.shift d))
        (by simpa only [Δ,Syn.shift,subst_polynomial] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (polynomial d))))))
  simpa only [Δ,Syn.shift,subst_polynomial] using GaussianRationalHorner.canonical_congr
    (polynomial_lookup (Syn.shift d) (var 0) hd) (source_canonical _)

def allTerm : PTm 2 := qmul (sourceCoefficient (var 0)) (power (var 1) (var 0))
def sourceTerm : PTm 2 := qmul (coefficient (var 0)) (power (var 1) (succ (var 0)))
def value (d w : PTm n) : PTm n := GaussianRationalFiniteSum.sum sourceTerm d w
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (d w : PTm n) :
    Syn.subst σ (value d w) = value (Syn.subst σ d) (Syn.subst σ w) := by simp [value]
theorem all_term_at (w e : PTm n) : inst2 allTerm e w = qmul (sourceCoefficient e) (power w e) := by simp [allTerm,inst2]
theorem source_term_at (w k : PTm n) : inst2 sourceTerm k w = qmul (coefficient k) (power w (succ k)) := by simp [sourceTerm,inst2]

theorem evaluation_with_zero (d w : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial d) w ≐ GaussianRationalFiniteSum.sum allTerm (succ d) w := by
  refine (GaussianBivariatePowerExpansion.evaluate_power_sum (polynomial d) d w (polynomial_length d)).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded GaussianRationalPowerExpansion.termBody allTerm (succ d)
      (GaussianRationalPowerExpansion.data (polynomial d) d w) w (.allI (.impI ?_)))
  let Δ := lt (var 0) (succ (Syn.shift d)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift d) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have source : Δ ⊢[PRAAx]
      inst2 GaussianRationalPowerExpansion.termBody (var 0)
        (GaussianRationalPowerExpansion.data (polynomial (Syn.shift d)) (Syn.shift d) (Syn.shift w)) ≐
          qmul (sourceCoefficient (var 0)) (power (Syn.shift w) (var 0)) :=
    (GaussianRationalPowerExpansion.term_body_at (Γ := Δ) (polynomial (Syn.shift d)) (Syn.shift d) (Syn.shift w) (var 0)).eqTrans
    (qmul_congr (polynomial_exponent (Syn.shift d) (var 0) hi) (.eqRefl _))
  simpa only [Δ,Syn.shift,subst_polynomial,GaussianRationalPowerExpansion.subst_data,ConciseIPRA.PTm.subst_succ,all_term_at] using source

/-- The original finite logarithm sum, not a supplied evaluation formula. -/
theorem polynomial_evaluation (d w : PTm n) : Γ ⊢[PRAAx] evaluate (polynomial d) w ≐ value d w := by
  have first : Γ ⊢[PRAAx] inst2 allTerm zero w ≐ qzero := by
    rw [all_term_at]
    exact (qmul_congr source_zero (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)
  have tail : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum (shiftBody allTerm) d w ≐ value d w := by
    refine GaussianRationalFiniteSum.sum_congr_bounded (shiftBody allTerm) sourceTerm d w w (.allI (.impI ?_))
    simp only [inst2_shiftBody,all_term_at,source_term_at]
    exact qmul_congr (source_succ _) (.eqRefl _)
  exact (evaluation_with_zero d w).eqTrans ((GaussianRationalFiniteSum.sum_shift_first allTerm d w).eqTrans
    ((qadd_congr first tail).eqTrans (qzero_add (value d w) (GaussianRationalFiniteSum.sum_canonical sourceTerm d w))))

def composition (d K : PTm n) : PTm n := GaussianRationalPolynomialExponential.polynomial (polynomial d) d K
@[simp] theorem subst_composition {m : ℕ} (σ : Fin n → PTm m) (d K : PTm n) :
    Syn.subst σ (composition d K) = composition (Syn.subst σ d) (Syn.subst σ K) := by simp [composition]
theorem composition_length (d K : PTm n) : Γ ⊢[PRAAx] length (composition d K) ≐ succ (K*d) :=
  GaussianRationalPolynomialExponential.polynomial_length (polynomial d) d K
theorem composition_canonical (d K : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (composition d K) :=
  GaussianRationalPolynomialExponential.polynomial_canonical (polynomial d) d K
theorem composition_evaluation (d K w : PTm n) : Γ ⊢[PRAAx]
    evaluate (composition d K) w ≐ GaussianRationalPolynomialExponential.scalarSum (value d w) K := by
  have base : Γ ⊢[PRAAx] evaluate (composition d K) w ≐
      GaussianRationalPolynomialExponential.scalarSum (evaluate (polynomial d) w) K :=
    GaussianRationalPolynomialExponential.polynomial_evaluation (polynomial d) d K w (polynomial_length d)
  exact base.eqTrans (GaussianRationalFiniteSum.sum_index_congr
    GaussianRationalPolynomialExponential.scalarBody (.eqRefl (succ K)) (polynomial_evaluation d w))

def polynomialF : PR 1 := PTm.toPR (polynomial (var 0))
def compositionF : PR 2 := PTm.toPR (composition (var 0) (var 1))
def valueF : PR 2 := PTm.toPR (value (var 0) (var 1))
def run (d K : PTm n) : PTm n := ap2 compositionF d K
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (d K : PTm n) :
    Syn.subst σ (run d K) = run (Syn.subst σ d) (Syn.subst σ K) := by simp [run]

theorem polynomial_program_at (d : PTm n) : Γ ⊢[PRAAx] ap1 polynomialF d ≐ polynomial d := by
  simpa [polynomialF,ap1] using toPR_eq (Γ := Γ) (polynomial (var 0) : PTm 1) ![d]
theorem value_program_at (d w : PTm n) : Γ ⊢[PRAAx] ap2 valueF d w ≐ value d w := by
  simpa [valueF,ap2] using toPR_eq (Γ := Γ) (value (var 0) (var 1) : PTm 2) ![d,w]
theorem program_at (d K : PTm n) : Γ ⊢[PRAAx] run d K ≐ composition d K := by
  simpa [run,compositionF,ap2] using toPR_eq (Γ := Γ) (composition (var 0) (var 1) : PTm 2) ![d,K]
theorem returned_length (d K : PTm n) : Γ ⊢[PRAAx] length (run d K) ≐ succ (K*d) :=
  (congrFst (program_at d K)).eqTrans (composition_length d K)
theorem returned_canonical (d K : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (run d K) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr (program_at d K) (composition_canonical d K)
theorem returned_evaluation (d K w : PTm n) : Γ ⊢[PRAAx]
    evaluate (run d K) w ≐ ap2 GaussianRationalPolynomialExponential.scalarF (ap2 valueF d w) K := by
  have hRun : Γ ⊢[PRAAx] evaluate (run d K) w ≐ evaluate (composition d K) w :=
    GaussianRationalMonicReduction.evaluate_congr (program_at d K) (.eqRefl w)
  have hValue : Γ ⊢[PRAAx]
      GaussianRationalPolynomialExponential.scalarSum (value d w) K ≐
        GaussianRationalPolynomialExponential.scalarSum (ap2 valueF d w) K :=
    GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (.eqRefl (succ K)) (value_program_at d w).eqSymm
  exact hRun.eqTrans ((composition_evaluation d K w).eqTrans
    (hValue.eqTrans (GaussianRationalPolynomialExponential.scalar_program_at (ap2 valueF d w) K).eqSymm))

theorem original_logarithm_coefficient_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (represents (coefficient (var 0)) (signNumerator (var 0)) (succ (var 0)) ⋏
      canonical (coefficient (var 0))) :=
  closeUniv 1 (.andI (coefficient_represents _) (coefficient_canonical _))
theorem actual_factorial_kernel_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (coefficient (var 0) ≐ kernelCoefficient (var 0)) := closeUniv 1 (coefficient_kernel _)
theorem actual_logarithm_polynomial_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (length (polynomial (var 0)) ≐ succ (var 0) ⋏ canonicalCoefficients (polynomial (var 0))) :=
  closeUniv 1 (.andI (polynomial_length _) (polynomial_canonical _))
theorem actual_zero_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (entry (polynomial (var 0)) (var 0) ≐ qzero) := closeUniv 1 (polynomial_constant _)
theorem actual_original_logarithm_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (var 0) ⟶ entry (polynomial (var 0)) (monus (var 0) (succ (var 1))) ≐ coefficient (var 1)) :=
  closeUniv 2 (.impI (polynomial_positive_coefficient _ _ Prf.hyp0))
theorem actual_stored_factorial_kernel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (var 0) ⟶ entry (polynomial (var 0)) (monus (var 0) (succ (var 1))) ≐ kernelCoefficient (var 1)) :=
  closeUniv 2 (.impI (polynomial_kernel_coefficient _ _ Prf.hyp0))
theorem literal_finite_logarithm_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (evaluate (polynomial (var 0)) (var 1) ≐ value (var 0) (var 1)) :=
  closeUniv 2 (polynomial_evaluation _ _)
theorem actual_finite_composition_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (composition (var 0) (var 1)) ≐ succ (var 1*var 0) ⋏
      canonicalCoefficients (composition (var 0) (var 1))) :=
  closeUniv 2 (.andI (composition_length _ _) (composition_canonical _ _))
theorem literal_finite_exponential_of_logarithm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (composition (var 0) (var 1)) (var 2) ≐
      GaussianRationalPolynomialExponential.scalarSum (value (var 0) (var 2)) (var 1)) :=
  closeUniv 3 (composition_evaluation _ _ _)
theorem actual_finite_composition_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ composition (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_finite_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (run (var 0) (var 1)) (var 2) ≐
      ap2 GaussianRationalPolynomialExponential.scalarF (ap2 valueF (var 0) (var 2)) (var 1)) :=
  closeUniv 3 (returned_evaluation _ _ _)

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmPolynomial
