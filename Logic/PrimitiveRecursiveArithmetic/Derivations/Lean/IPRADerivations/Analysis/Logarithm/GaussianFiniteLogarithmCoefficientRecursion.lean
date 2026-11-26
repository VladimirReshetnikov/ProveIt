import IPRADerivations.Analysis.Polynomials.GaussianRationalCoefficientRecursion

/-!
# The original finite logarithm exponential has the actual prior recursion

The existing finite Euler identity is read through the SAME real Product
program. Actual product commutation and bounded original Cauchy lookup
produce the explicit previous-coefficient sum. Its last Euler-constant
term is proved zero. The source polynomial H_d discharges all original
input shape, canonicality and zero-constant guards internally.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmCoefficientRecursion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul)
open GaussianRationalSyntheticDivision (qmul_congr canonicalCoefficients)
open GaussianRationalPolynomialProduct (product)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside cauchySum term termBody data)
open GaussianRationalCoefficientRecursion (priorTerm priorBody priorSum recursion)
open GaussianRationalPolynomialExponential (polynomial)
open GaussianRationalEulerCoefficients (euler)
open GaussianRationalNaturalScale (natScale)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem product_commuted_exponent (P D C B e : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hC : Γ ⊢[PRAAx] length C ≐ succ B)
    (he : Γ ⊢[PRAAx] le e D) : Γ ⊢[PRAAx]
    exponentCoefficient (product P C D B) (D+B) e ≐ exponentCoefficient (product C P B D) (B+D) e := by
  let I := monus (D+B) e
  have hSum := le_trans he (le_add_right D B)
  have hI : Γ ⊢[PRAAx] le I (D+B) := GaussianRationalMonicReconstruction.monus_le_left _ _
  exact (exponent_inside _ (D+B) e hSum).eqTrans
    ((GaussianRationalPolynomialPowerEuler.product_commutative_coefficient P C D B I hP hC hI).eqTrans
      ((entry_congr (.eqRefl _) (congrMonus (add_comm _ _) (.eqRefl _))).eqTrans
        (exponent_inside _ (B+D) e (le_trans he (le_add_left _ _))).eqSymm))

theorem cauchy_to_prior_term (P D C B e j : PTm n)
    (heD : Γ ⊢[PRAAx] le e D) (heB : Γ ⊢[PRAAx] le e B) (hj : Γ ⊢[PRAAx] le j e) : Γ ⊢[PRAAx]
    term C P B D e j ≐ priorTerm P D C B e j :=
  qmul_congr (exponent_inside C B j (le_trans hj heB)).eqSymm
    (exponent_inside P D (monus e j)
      (le_trans (GaussianRationalMonicReconstruction.monus_le_left _ _) heD)).eqSymm

theorem cauchy_to_prior (P D C B e : PTm n) (heD : Γ ⊢[PRAAx] le e D) (heB : Γ ⊢[PRAAx] le e B) : Γ ⊢[PRAAx]
    cauchySum C P B D e ≐ GaussianRationalFiniteSum.sum priorBody (succ e) (data P C D B e) := by
  have hd : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift D) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using heD.shift
  have hb : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using heB.shift
  refine GaussianRationalFiniteSum.sum_congr_bounded termBody priorBody (succ e)
    (data C P B D e) (data P C D B e) (.allI (.impI ?_))
  let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have h := (GaussianRationalLowCoefficientConvolution.term_at (Γ := Δ) (Syn.shift C) (Syn.shift P)
      (Syn.shift B) (Syn.shift D) (Syn.shift e) (var 0)).eqTrans
    ((cauchy_to_prior_term _ _ _ _ _ _ hd.wk hb.wk hi).eqTrans
      (GaussianRationalCoefficientRecursion.prior_at _ _ _ _ _ _).eqSymm)
  simpa only [Δ,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,ConciseIPRA.PTm.subst_succ] using h

theorem last_prior_zero (P D C B e : PTm n) (hP : Γ ⊢[PRAAx] entry P D ≐ qzero) : Γ ⊢[PRAAx]
    priorTerm P D C B e e ≐ qzero := by
  have hKernel : Γ ⊢[PRAAx] exponentCoefficient P D (monus e e) ≐ qzero :=
    (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) (monus_self e)).eqTrans
      ((exponent_inside P D zero (zero_le D)).eqTrans ((entry_congr (.eqRefl _) (monus_zero D)).eqTrans hP))
  exact (qmul_congr (.eqRefl _) hKernel).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem product_prior (P D C B e : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hC : Γ ⊢[PRAAx] length C ≐ succ B)
    (hZero : Γ ⊢[PRAAx] entry P D ≐ qzero) (heD : Γ ⊢[PRAAx] le e D) (heB : Γ ⊢[PRAAx] le e B) : Γ ⊢[PRAAx]
    exponentCoefficient (product P C D B) (D+B) e ≐ priorSum P D C B e :=
  (product_commuted_exponent P D C B e hP hC heD).eqTrans
    ((GaussianRationalLowCoefficientConvolution.product_exponent C P B D e heB heD).eqTrans
      ((cauchy_to_prior P D C B e heD heB).eqTrans
        ((GaussianRationalFiniteSum.sum_succ priorBody e (data P C D B e)).eqTrans
          ((GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _)
            ((GaussianRationalCoefficientRecursion.prior_at P D C B e e).eqTrans (last_prior_zero P D C B e hZero))).eqTrans
              (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalFiniteSum.sum_canonical _ _ _))))))

theorem finite_recursion_point (C N K e : PTm n) (hL : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    natScale e (exponentCoefficient (polynomial C N K) (K*N) e) ≐ priorSum (euler C N) N (polynomial C N K) (K*N) e :=
  (GaussianRationalFiniteExponentialEuler.finite_euler_scaled C N K e hL hCan hC he hK).eqTrans
    (product_prior _ _ _ _ _ (GaussianRationalEulerCoefficients.euler_length C N)
      (GaussianRationalPolynomialExponential.polynomial_length C N K) (GaussianRationalEulerCoefficients.euler_constant C N)
      he (GaussianRationalPolynomialPowerSupport.min_product e K N he hK))

theorem logarithm_recursion_point (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    natScale e (exponentCoefficient (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) e) ≐
      priorSum (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) e :=
  finite_recursion_point _ _ _ _ (GaussianFiniteLogarithmPolynomial.polynomial_length d)
    (GaussianFiniteLogarithmPolynomial.polynomial_canonical d) (GaussianFiniteLogarithmPolynomial.polynomial_constant d) he hK

theorem logarithm_recursion (d K R : PTm n) (hd : Γ ⊢[PRAAx] le R d) (hk : Γ ⊢[PRAAx] le R K) : Γ ⊢[PRAAx]
    recursion (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d
      (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) R := by
  have ds : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift R) (Syn.shift d) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hd.shift
  have ks : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift R) (Syn.shift K) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hk.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift R)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift R) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Δ,Syn.shift,GaussianRationalEulerCoefficients.subst_euler,GaussianFiniteLogarithmPolynomial.subst_polynomial,
    GaussianFiniteLogarithmPolynomial.subst_composition,PTm.subst_mul] using
    logarithm_recursion_point (Syn.shift d) (Syn.shift K) (var 0) (le_trans hi ds.wk) (le_trans hi ks.wk)

theorem finite_constant (C N K : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial C N K) (K*N) zero ≐ GaussianRationalSyntheticDivision.qone :=
  (GaussianRationalPolynomialExponentialStability.finite_exponential_cutoff C N K zero hC (zero_le _) (zero_le _)).eqTrans
    ((GaussianRationalPolynomialExponentialStability.exponent_congr (GaussianRationalPolynomialExponential.stage_zero C N K)
      (zero_mul N) (.eqRefl _)).eqTrans
        ((exponent_inside _ zero zero (le_refl _)).eqTrans
          ((entry_congr (.eqRefl _) (monus_self zero)).eqTrans (GaussianRationalMonicReduction.singleton_lookup _))))
theorem logarithm_constant (d K : PTm n) : Γ ⊢[PRAAx]
    exponentCoefficient (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) zero ≐ GaussianRationalSyntheticDivision.qone :=
  finite_constant _ _ _ (GaussianFiniteLogarithmPolynomial.polynomial_constant d)

def output (d K e : PTm n) : PTm n := pairT (GaussianFiniteLogarithmPolynomial.composition d K)
  (priorSum (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) e)
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (d K e : PTm n) : PTm n := ap3 outputF d K e
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (d K e : PTm n) :
    Syn.subst σ (output d K e) = output (Syn.subst σ d) (Syn.subst σ K) (Syn.subst σ e) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (d K e : PTm n) :
    Syn.subst σ (run d K e) = run (Syn.subst σ d) (Syn.subst σ K) (Syn.subst σ e) := by simp [run]

theorem program_at (d K e : PTm n) : Γ ⊢[PRAAx] run d K e ≐ output d K e := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![d,K,e]
theorem returned_polynomial (d K e : PTm n) : Γ ⊢[PRAAx] fstT (run d K e) ≐ GaussianFiniteLogarithmPolynomial.composition d K :=
  (congrFst (program_at d K e)).eqTrans (fst_pair _ _)
theorem returned_prior (d K e : PTm n) : Γ ⊢[PRAAx] sndT (run d K e) ≐
    priorSum (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) d (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) e :=
  (congrSnd (program_at d K e)).eqTrans (snd_pair _ _)
theorem returned_recursion (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    natScale e (exponentCoefficient (fstT (run d K e)) (K*d) e) ≐ sndT (run d K e) :=
  (GaussianRationalNaturalScale.natScale_congr (.eqRefl _)
    (GaussianRationalPolynomialExponentialStability.exponent_congr (returned_polynomial d K e) (.eqRefl _) (.eqRefl _))).eqTrans
      ((logarithm_recursion_point d K e he hK).eqTrans (returned_prior d K e).eqSymm)

theorem actual_zero_constant_product_prior_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ length (var 2) ≐ succ (var 3) ⟶ entry (var 0) (var 1) ≐ qzero ⟶
      le (var 4) (var 1) ⟶ le (var 4) (var 3) ⟶ exponentCoefficient (product (var 0) (var 2) (var 1) (var 3)) (var 1+var 3) (var 4) ≐
        priorSum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI
    (product_prior _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem original_logarithm_prior_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ natScale (var 2)
      (exponentCoefficient (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 1*var 0) (var 2)) ≐
        priorSum (euler (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0)) (var 0)
          (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 1*var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (logarithm_recursion_point _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_logarithm_bounded_prior_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ recursion
      (euler (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0)) (var 0)
      (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 1*var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (logarithm_recursion _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_logarithm_exponential_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (exponentCoefficient (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 1*var 0) zero ≐ GaussianRationalSyntheticDivision.qone) :=
  closeUniv 2 (logarithm_constant _ _)
theorem original_logarithm_coefficient_recursion_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem original_returned_logarithm_coefficient_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ natScale (var 2)
      (exponentCoefficient (fstT (run (var 0) (var 1) (var 2))) (var 1*var 0) (var 2)) ≐ sndT (run (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (returned_recursion _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmCoefficientRecursion
