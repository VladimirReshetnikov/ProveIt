import IPRADerivations.Analysis.Polynomials.Coefficients.Operations.GaussianRationalCoefficientRecursion
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianIntegerFractionPowers

/-!
# The concrete polynomial 1+X has the original logarithmic recursion

A real two-entry coefficient program is used. Original parity numerators
prove cancellation of the only two surviving previous-coefficient terms;
the remaining actual finite sum is zero by original stored lookups. No
linear-output or Bell recurrence is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmLinearRecursion

open_ipra
open GaussianRationalHorner (qzero qadd qmul canonical ofGaussian represents canonical_unique)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr qadd_congr canonicalCoefficients)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside exponent_outside data)
open GaussianRationalCoefficientRecursion (priorTerm priorBody priorSum recursion)
open GaussianRationalEulerCoefficients (euler parityPoint)
open GaussianRationalNaturalScale (natScale)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence sequence_decode sequence_length entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def linear : PTm n := sequence (qone : PTm 2) two zero
ipra_subst linear [two, one]
theorem linear_length : Γ ⊢[PRAAx] length (linear : PTm n) ≐ succ one := sequence_length _ _ _
theorem linear_lookup (i : PTm n) (hi : Γ ⊢[PRAAx] le i one) : Γ ⊢[PRAAx] entry linear i ≐ qone := by
  simpa only [linear,inst2,GaussianRationalSyntheticDivision.qone,GaussianRationalHorner.subst_ofGaussian,
    ComplexLogarithmRemainder.subst_oneCode,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
      sequence_decode (qone : PTm 2) (x := zero) ((succ_monus_succ _ _).eqTrans hi)
theorem linear_canonical : Γ ⊢[PRAAx] canonicalCoefficients (linear : PTm n) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (linear : PTm n))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) one :=
    (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) (linear_length (Γ := Δ))
      (by simpa only [Δ,Syn.shift,subst_linear] using
        (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (linear : PTm n))))))
  simpa only [Δ,Syn.shift,subst_linear] using GaussianRationalHorner.canonical_congr (linear_lookup (var 0) hi) qone_canonical

theorem linear_low (e : PTm n) (he : Γ ⊢[PRAAx] le e one) : Γ ⊢[PRAAx] exponentCoefficient linear one e ≐ qone :=
  (exponent_inside _ one e he).eqTrans (linear_lookup _ (GaussianRationalMonicReconstruction.monus_le_left _ _))
theorem linear_high (e : PTm n) (he : Γ ⊢[PRAAx] le two e) : Γ ⊢[PRAAx] exponentCoefficient linear one e ≐ qzero :=
  exponent_outside _ one e he

theorem parity_canonical (k : PTm n) : Γ ⊢[PRAAx] canonical (parityPoint k) :=
  GaussianRationalHorner.ofGaussian_canonical _ one (le_refl one)
theorem parity_zero : Γ ⊢[PRAAx] parityPoint (zero : PTm n) ≐ qone :=
  canonical_unique _ _ _ one (parity_canonical zero) qone_canonical (le_refl one)
    (GaussianRationalHorner.represents_congr (.eqRefl _)
      (GaussianIntegerFractionPowers.parity_scalar_zero (Γ := Γ) (n := n)) (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ one (le_refl one)))
    (GaussianRationalHorner.ofGaussian_represents _ one (le_refl one))
theorem parity_sum (k : PTm n) : Γ ⊢[PRAAx] qadd (parityPoint (succ k)) (parityPoint k) ≐ qzero := by
  have rep : Γ ⊢[PRAAx] represents (qadd (parityPoint (succ k)) (parityPoint k))
      (ComplexLogarithmRemainder.add (GaussianFiniteLogarithmPolynomial.signNumerator (succ k))
        (GaussianFiniteLogarithmPolynomial.signNumerator k)) one :=
    GaussianRationalHorner.qadd_represents (Γ := Γ) _ _ _ _ one (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents _ one (le_refl one))
    (GaussianRationalHorner.ofGaussian_represents _ one (le_refl one))
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.add (GaussianFiniteLogarithmPolynomial.signNumerator (succ k))
        (GaussianFiniteLogarithmPolynomial.signNumerator k)) ComplexLogarithmRemainder.zeroCode := by
    have h : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (GaussianFiniteLogarithmPolynomial.signNumerator (succ k))
        (ComplexLogarithmRemainder.neg (GaussianFiniteLogarithmPolynomial.signNumerator k)) :=
      GaussianIntegerFractionPowers.parity_scalar_succ (Γ := Γ) k
    apply GaussianRootAlgebra.equal_of_values
    · rw [GaussianRootAlgebra.re_add,GaussianRootAlgebra.equal_re h,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_zero]
      ring
    · rw [GaussianRootAlgebra.im_add,GaussianRootAlgebra.equal_im h,GaussianRootAlgebra.im_neg,GaussianRootAlgebra.im_zero]
      ring
  exact canonical_unique _ _ _ one (GaussianRationalHorner.qadd_canonical _ _)
    GaussianRationalSyntheticDivision.qzero_canonical (le_refl one)
    (GaussianRationalHorner.represents_congr (.eqRefl _) native (.eqRefl _) rep)
    (GaussianRationalHorner.zero_represents one)

theorem euler_positive (d k : PTm n) (hk : Γ ⊢[PRAAx] lt k d) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d (succ k) ≐ parityPoint k :=
  (exponent_inside _ d (succ k) hk).eqTrans (GaussianRationalEulerCoefficients.logarithm_euler_positive d k hk)

theorem high_prior_term (P D e j : PTm n) (hj : Γ ⊢[PRAAx] le two j) : Γ ⊢[PRAAx]
    priorTerm P D linear one e j ≐ qzero :=
  (qmul_congr (linear_high j hj) (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)

theorem prior_tail_zero (P D e N : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (offB priorBody) N (pairT two (data P linear D one e)) ≐ qzero := by
  refine GaussianRationalMatrixFiniteSums.sum_zero_of_terms _ _ _ (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have h := (GaussianRationalFiniteProduct.offset_at (Γ := Δ) priorBody two (var 0)
    (data (Syn.shift P) linear (Syn.shift D) one (Syn.shift e))).eqTrans
      ((GaussianRationalCoefficientRecursion.prior_at _ _ _ _ _ _).eqTrans
        (high_prior_term _ _ _ _ (le_add_right two (var 0))))
  simpa only [Δ,Syn.shift,subst_pairT,GaussianRationalLowCoefficientConvolution.subst_data,subst_linear,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,one,two] using h

alias unit_multiply := GaussianPolynomialDeterminantTerms.one_mul_canonical

theorem prior_zero (d e : PTm n) (he : Γ ⊢[PRAAx] le (succ e) d) : Γ ⊢[PRAAx]
    priorTerm (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d linear one (succ e) zero ≐ parityPoint e :=
  (qmul_congr (linear_low zero (zero_le one))
    ((GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) (monus_zero _)).eqTrans
      (euler_positive d e he))).eqTrans (unit_multiply _ (parity_canonical _))

theorem prior_one (d e : PTm n) (he : Γ ⊢[PRAAx] le (succ (succ e)) d) : Γ ⊢[PRAAx]
    priorTerm (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d linear one (succ (succ e)) one ≐ parityPoint e :=
  (qmul_congr (linear_low one (le_refl one))
    ((GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _)
      ((succ_monus_succ (succ e) zero).eqTrans (monus_zero (succ e)))).eqTrans
        (euler_positive d e (le_trans (le_succ_self (succ e)) he)))).eqTrans (unit_multiply _ (parity_canonical _))

theorem first_two (P D e : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum priorBody two (data P linear D one e) ≐
      qadd (priorTerm P D linear one e zero) (priorTerm P D linear one e one) :=
  (GaussianRationalFiniteSum.sum_succ priorBody one _).eqTrans
    (qadd_congr
      (GaussianRationalFiniteSum.sum_singleton priorBody _
        (GaussianRationalCoefficientRecursion.prior_at _ _ _ _ _ _)
        (GaussianRationalHorner.qmul_canonical _ _))
      (GaussianRationalCoefficientRecursion.prior_at _ _ _ _ _ _))

theorem higher_prior_zero (d k : PTm n) (hk : Γ ⊢[PRAAx] le (succ (succ k)) d) : Γ ⊢[PRAAx]
    priorSum (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d linear one (succ (succ k)) ≐ qzero :=
  (GaussianRationalFiniteSum.sum_index_congr priorBody (by ipra_ring : Γ ⊢[PRAAx] succ (succ k) ≐ two+k) (.eqRefl _)).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_split priorBody two k _).eqTrans
      ((qadd_congr ((first_two _ _ _).eqTrans
        ((qadd_congr (prior_zero d (succ k) hk) (prior_one d k hk)).eqTrans (parity_sum k)))
        (prior_tail_zero _ _ _ _)).eqTrans (GaussianRationalSyntheticDivision.qzero_add _ GaussianRationalSyntheticDivision.qzero_canonical)))

def point (d e : PTm n) : Fm PTm n := natScale e (exponentCoefficient linear one e) ≐
  priorSum (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d linear one e
ipra_subst point [one]
theorem point_congr (d : PTm n) {e f : PTm n} (h : Γ ⊢[PRAAx] e ≐ f) (hp : Γ ⊢[PRAAx] point d e) : Γ ⊢[PRAAx] point d f := by
  have result := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (point (var 0) (var 1) : Fm PTm 2) ![d,e] ![d,f]
    (fun i => by fin_cases i; exact .eqRefl _; exact h) (by simpa only [subst_point,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using hp)
  simpa only [subst_point,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using result

theorem point_zero (d : PTm n) : Γ ⊢[PRAAx] point d zero :=
  (GaussianRationalNaturalScale.natScale_zero _).eqTrans (GaussianRationalFiniteSum.sum_zero priorBody _).eqSymm
theorem point_one (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] point d one := by
  have left : Γ ⊢[PRAAx] natScale one (exponentCoefficient linear one one) ≐ qone :=
    (GaussianRationalNaturalScale.natScale_congr (.eqRefl _) (linear_low one (le_refl one))).eqTrans
      (GaussianRationalNaturalScale.natScale_one_canonical qone qone_canonical)
  have right : Γ ⊢[PRAAx] priorSum (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d linear one one ≐ qone :=
    GaussianRationalFiniteSum.sum_singleton priorBody _
      ((GaussianRationalCoefficientRecursion.prior_at _ _ _ _ _ _).eqTrans
        ((prior_zero d zero hd).eqTrans parity_zero)) qone_canonical
  exact left.eqTrans right.eqSymm

theorem point_higher (d k : PTm n) (hk : Γ ⊢[PRAAx] le (succ (succ k)) d) : Γ ⊢[PRAAx] point d (succ (succ k)) :=
  ((GaussianRationalNaturalScale.natScale_congr (.eqRefl _) (linear_high _ (le_of_eq_add (d := k) (by ipra_ring)))).eqTrans
    (GaussianRationalFactorialEulerSums.scale_zero_value _)).eqTrans (higher_prior_zero d k hk).eqSymm

theorem point_at (d e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx] point d e := by
  refine .orE (zero_or_succ e) ?_ ?_
  · exact point_congr d Prf.hyp0.eqSymm (point_zero d)
  · refine .orE (zero_or_succ (pred e)) ?_ ?_
    · have hE : ((pred e ≐ zero) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have hd := le_congr hE (.eqRefl _) he.wk.wk
      exact point_congr d hE.eqSymm (point_one d hd)
    · have hE : ((pred e ≐ succ (pred (pred e))) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx]
          e ≐ succ (succ (pred (pred e))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have hd := le_congr hE (.eqRefl _) he.wk.wk
      exact point_congr d hE.eqSymm (point_higher d _ hd)

theorem linear_recursion (d R : PTm n) (hR : Γ ⊢[PRAAx] le R d) : Γ ⊢[PRAAx]
    recursion (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d linear one R := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift R) (Syn.shift d) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hR.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift R)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift R) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [point,Δ,Syn.shift,GaussianRationalEulerCoefficients.subst_euler,GaussianFiniteLogarithmPolynomial.subst_polynomial,
    subst_linear,one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using point_at (Syn.shift d) (var 0) (le_trans hi hs.wk)

def output (d e : PTm n) : PTm n := pairT linear
  (priorSum (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d linear one e)
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (d e : PTm n) : PTm n := ap2 outputF d e
ipra_subst output [one]
ipra_subst run

theorem program_at (d e : PTm n) : Γ ⊢[PRAAx] run d e ≐ output d e := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![d,e]
theorem returned_linear (d e : PTm n) : Γ ⊢[PRAAx] fstT (run d e) ≐ linear :=
  (program_at d e).fstE
theorem returned_prior (d e : PTm n) : Γ ⊢[PRAAx] sndT (run d e) ≐
    priorSum (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d linear one e :=
  (program_at d e).sndE
theorem returned_recursion (d e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    natScale e (exponentCoefficient (fstT (run d e)) one e) ≐ sndT (run d e) :=
  (GaussianRationalNaturalScale.natScale_congr (.eqRefl _)
    (GaussianRationalPolynomialExponentialStability.exponent_congr (returned_linear d e) (.eqRefl _) (.eqRefl _))).eqTrans
      ((point_at d e he).eqTrans (returned_prior d e).eqSymm)

theorem actual_linear_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (length (linear : PTm 0) ≐ succ one ⋏ canonicalCoefficients (linear : PTm 0)) := .andI linear_length linear_canonical
theorem actual_original_parity_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qadd (parityPoint (succ (var 0))) (parityPoint (var 0)) ≐ qzero) := closeUniv 1 (parity_sum _)
theorem actual_linear_low_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (var 0) one ⟶ exponentCoefficient linear one (var 0) ≐ qone) := closeUniv 1 (.impI (linear_low _ Prf.hyp0))
theorem actual_linear_high_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le two (var 0) ⟶ exponentCoefficient linear one (var 0) ≐ qzero) := closeUniv 1 (.impI (linear_high _ Prf.hyp0))
theorem original_linear_prior_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (var 0) ⟶ point (var 0) (var 1)) := closeUniv 2 (.impI (point_at _ _ Prf.hyp0))
theorem original_linear_bounded_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (var 0) ⟶ recursion (euler (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0)) (var 0) linear one (var 1)) :=
  closeUniv 2 (.impI (linear_recursion _ _ Prf.hyp0))
theorem actual_linear_recursion_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_linear_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (var 0) ⟶ natScale (var 1) (exponentCoefficient (fstT (run (var 0) (var 1))) one (var 1)) ≐ sndT (run (var 0) (var 1))) :=
  closeUniv 2 (.impI (returned_recursion _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmLinearRecursion
