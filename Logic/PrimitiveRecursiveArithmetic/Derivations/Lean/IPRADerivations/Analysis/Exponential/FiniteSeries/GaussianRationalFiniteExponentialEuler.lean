import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalFactorialEulerSums
import IPRADerivations.Analysis.Exponential.FiniteSeries.GaussianRationalExponentialProductCoefficients

/-!
# The actual finite exponential satisfies the low Euler identity

Original zero constant and proved power support kill the actual high-power
summands of E(C)*C^r. The actual factorial-weighted coefficient sum can
therefore be joined to the SAME stored product with the finite exponential.
Only original input shape/canonicality and explicit numerical cutoffs are
used; no Bell or exponential derivative law is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFiniteExponentialEuler

open_ipra
open GaussianRationalHorner (qzero qmul)
open GaussianRationalSyntheticDivision (qmul_congr canonicalCoefficients)
open GaussianRationalPolynomialPowers (powerPrefix prefix_length)
open GaussianRationalEulerCoefficients (euler euler_length)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside cauchySum term termBody data term_at)
open GaussianRationalFactorialEulerSums (shiftedTerm shiftedBody shiftedSum)
open GaussianRationalFiniteSum (sum)
open GaussianRationalNaturalScale (natScale natScale_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem cauchy_term_zero (C N K r e i : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hr : Γ ⊢[PRAAx] le r K) (he : Γ ⊢[PRAAx] le e N) (her : Γ ⊢[PRAAx] le e r)
    (hi : Γ ⊢[PRAAx] le i e) : Γ ⊢[PRAAx]
    term (powerPrefix C N K r) (euler C N) (r*N) N e i ≐ qzero := by
  refine .orE (lt_or_eq_of_le hi) ?_ ?_
  · have hip : ((lt i e) :: Γ) ⊢[PRAAx] le i (r*N) :=
      le_trans (le_of_lt Prf.hyp0) (GaussianRationalPolynomialPowerSupport.min_product e r N he.wk her.wk)
    have hz := GaussianRationalPolynomialPowerSupport.low_power_zero C N K r i hC.wk hr.wk
      (le_trans (le_of_lt Prf.hyp0) he.wk) (lt_of_lt_of_le Prf.hyp0 her.wk)
    have hEntry := (exponent_inside (powerPrefix C N K r) (r*N) i hip).eqSymm.eqTrans hz
    exact (qmul_congr hEntry (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)
  · have hIndex : ((i ≐ e) :: Γ) ⊢[PRAAx] monus N (monus e i) ≐ N :=
      (congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self e))).eqTrans (monus_zero N)
    exact (qmul_congr (.eqRefl _) ((entry_congr (.eqRefl _) hIndex).eqTrans
      (GaussianRationalEulerCoefficients.euler_constant C N))).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem cauchy_zero (C N K r e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hr : Γ ⊢[PRAAx] le r K) (he : Γ ⊢[PRAAx] le e N) (her : Γ ⊢[PRAAx] le e r) : Γ ⊢[PRAAx]
    cauchySum (powerPrefix C N K r) (euler C N) (r*N) N e ≐ qzero := by
  have hc : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) (Syn.shift N) ≐ qzero := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.MasterCertificate.subst_entry,GaussianRationalHorner.subst_qzero,Syn.shift] using hC.shift
  have hk : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift r) (Syn.shift K) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hr.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift
  have hh : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift r) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using her.shift
  refine GaussianRationalMatrixFiniteSums.sum_zero_of_terms termBody (succ e)
    (data (powerPrefix C N K r) (euler C N) (r*N) N e) (.allI (.impI ?_))
  let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have h := (term_at (Γ := Δ) (powerPrefix (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift r))
    (euler (Syn.shift C) (Syn.shift N)) (Syn.shift r*Syn.shift N) (Syn.shift N) (Syn.shift e) (var 0)).eqTrans
      (cauchy_term_zero _ _ _ _ _ _ hc.wk hk.wk hn.wk hh.wk hi)
  simpa only [Δ,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,
    GaussianRationalPolynomialPowers.subst_prefix,GaussianRationalEulerCoefficients.subst_euler,
    PTm.subst_mul,ConciseIPRA.PTm.subst_succ,GaussianRationalHorner.subst_qzero] using h

theorem high_product_zero (C N K r e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hr : Γ ⊢[PRAAx] le r K) (he : Γ ⊢[PRAAx] le e N) (her : Γ ⊢[PRAAx] le e r) : Γ ⊢[PRAAx]
    exponentCoefficient (GaussianRationalPolynomialProduct.product (euler C N) (powerPrefix C N K r) N (r*N)) (N+r*N) e ≐ qzero := by
  let I := monus (N+r*N) e
  have hp := GaussianRationalPolynomialPowerSupport.min_product e r N he her
  have hSum : Γ ⊢[PRAAx] le e (N+r*N) := le_trans he (le_add_right _ _)
  have hI : Γ ⊢[PRAAx] le I (N+r*N) := GaussianRationalMonicReconstruction.monus_le_left _ _
  have hComm : Γ ⊢[PRAAx]
      entry (GaussianRationalPolynomialProduct.product (euler C N) (powerPrefix C N K r) N (r*N)) I ≐
        exponentCoefficient (GaussianRationalPolynomialProduct.product (powerPrefix C N K r) (euler C N) (r*N) N) (r*N+N) e :=
    (GaussianRationalPolynomialPowerEuler.product_commutative_coefficient _ _ _ _ I
      (euler_length C N) (prefix_length C N K r) hI).eqTrans
        ((entry_congr (.eqRefl _) (congrMonus (add_comm _ _) (.eqRefl _))).eqTrans
          (exponent_inside _ (r*N+N) e (le_trans he (le_add_left _ _))).eqSymm)
  exact (exponent_inside _ (N+r*N) e hSum).eqTrans
    (hComm.eqTrans ((GaussianRationalLowCoefficientConvolution.product_exponent _ _ _ _ e hp he).eqTrans
      (cauchy_zero C N K r e hC hr he her)))

theorem high_term_zero (C N K r e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hr : Γ ⊢[PRAAx] le r K) (he : Γ ⊢[PRAAx] le e N) (her : Γ ⊢[PRAAx] le e r) : Γ ⊢[PRAAx]
    shiftedTerm C N K e r ≐ qzero :=
  (qmul_congr (.eqRefl _) (high_product_zero C N K r e hC hr he her)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

def tailLaw (C N K e r : PTm n) : Fm PTm n := le (e+r) K ⟶ shiftedSum C N K e (succ (e+r)) ≐ shiftedSum C N K e e
ipra_subst tailLaw

theorem sum_successor (C N K e j : PTm n) : Γ ⊢[PRAAx]
    shiftedSum C N K e (succ j) ≐ GaussianRationalHorner.qadd (shiftedSum C N K e j) (shiftedTerm C N K e j) :=
  (GaussianRationalFiniteSum.sum_succ shiftedBody j (GaussianRationalPolynomialExponentialCoefficients.data C N K e)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (GaussianRationalFactorialEulerSums.shifted_body_at _ _ _ _ _))

theorem tail_zero (C N K e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx] tailLaw C N K e zero := by
  refine .impI ?_
  have hk : (le (e+zero) K :: Γ) ⊢[PRAAx] le e K := le_congr (add_zero e) (.eqRefl _) Prf.hyp0
  exact (GaussianRationalFiniteSum.sum_index_congr shiftedBody (congrSucc (add_zero e)) (.eqRefl _)).eqTrans
    ((sum_successor C N K e e).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (high_term_zero C N K e e hC.wk hk he.wk (le_refl e))).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalFiniteSum.sum_canonical _ _ _))))

theorem tail_step (C N K e r : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (ih : Γ ⊢[PRAAx] tailLaw C N K e r) : Γ ⊢[PRAAx] tailLaw C N K e (succ r) := by
  refine .impI ?_
  have hPrev : (le (e+succ r) K :: Γ) ⊢[PRAAx] le (e+r) K :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring : (le (e+succ r) K :: Γ) ⊢[PRAAx] succ (e+r) ≐ e+succ r)
      (le_succ_self (e+r))) Prf.hyp0
  have hz := high_term_zero C N K (e+succ r) e hC.wk Prf.hyp0 he.wk (le_add_right e (succ r))
  have hMid : (le (e+succ r) K :: Γ) ⊢[PRAAx] shiftedSum C N K e (e+succ r) ≐ shiftedSum C N K e e :=
    (GaussianRationalFiniteSum.sum_index_congr shiftedBody (by ipra_ring) (.eqRefl _)).eqTrans (.impE ih.wk hPrev)
  exact (sum_successor C N K e (e+succ r)).eqTrans
    ((GaussianRationalSyntheticDivision.qadd_congr hMid hz).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalFiniteSum.sum_canonical _ _ _)))

theorem tail_cutoff (C N K e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    shiftedSum C N K e (succ K) ≐ shiftedSum C N K e e := by
  have hc : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) (Syn.shift N) ≐ qzero := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.MasterCertificate.subst_entry,GaussianRationalHorner.subst_qzero,Syn.shift] using hC.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift
  have all : Γ ⊢[PRAAx] .all (tailLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift e) (var 0)) := by
    ipra_qfind (by trivial) [subst_tailLaw]
    · exact tail_zero C N K e hC he
    · exact tail_step _ _ _ _ _ hc.wk hn.wk Prf.hyp0
  have gate : Γ ⊢[PRAAx] tailLaw C N K e (monus K e) := by
    simpa only [subst_tailLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE (monus K e)
  have hEq := (eq_add_of_le hK).eqSymm
  have hRange : Γ ⊢[PRAAx] le (e+monus K e) K := le_congr hEq.eqSymm (.eqRefl _) (le_refl K)
  exact (GaussianRationalFiniteSum.sum_index_congr shiftedBody (congrSucc hEq.eqSymm) (.eqRefl _)).eqTrans (.impE gate hRange)

open GaussianRationalPolynomialExponential (polynomial)
open GaussianRationalPolynomialProduct (product)

theorem finite_euler_scaled (C N K e : PTm n) (hL : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    natScale e (exponentCoefficient (polynomial C N K) (K*N) e) ≐
      exponentCoefficient (product (euler C N) (polynomial C N K) N (K*N)) (N+K*N) e :=
  (natScale_congr (.eqRefl _) (GaussianRationalPolynomialExponentialCoefficients.finite_low_expansion C N K e hC he hK)).eqTrans
    ((GaussianRationalFactorialEulerSums.factorial_euler_sum C N K e e hL hCan hK he).eqTrans
      ((tail_cutoff C N K e hC he hK).eqSymm.eqTrans
        (GaussianRationalExponentialProductCoefficients.product_coefficient_sum C N K e K he).eqSymm))

theorem finite_euler (C N K e : PTm n) (hL : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (polynomial C N K) (K*N)) (K*N) e ≐
      exponentCoefficient (product (euler C N) (polynomial C N K) N (K*N)) (N+K*N) e :=
  (GaussianRationalFactorialEulerSums.euler_exponent_total _ _ _).eqTrans
    (finite_euler_scaled C N K e hL hCan hC he hK)

theorem logarithm_finite_euler (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (GaussianFiniteLogarithmPolynomial.composition d K) (K*d)) (K*d) e ≐
      exponentCoefficient (product (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d)
        (GaussianFiniteLogarithmPolynomial.composition d K) d (K*d)) (d+K*d) e :=
  finite_euler _ _ _ _ (GaussianFiniteLogarithmPolynomial.polynomial_length d)
    (GaussianFiniteLogarithmPolynomial.polynomial_canonical d) (GaussianFiniteLogarithmPolynomial.polynomial_constant d) he hK

def output (C N K : PTm n) : PTm n := pairT (euler (polynomial C N K) (K*N))
  (product (euler C N) (polynomial C N K) N (K*N))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N K : PTm n) : PTm n := ap3 outputF C N K
ipra_subst output
ipra_subst run

theorem program_at (C N K : PTm n) : Γ ⊢[PRAAx] run C N K ≐ output C N K := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,K]
theorem returned_euler (C N K : PTm n) : Γ ⊢[PRAAx] fstT (run C N K) ≐ euler (polynomial C N K) (K*N) :=
  (program_at C N K).fstE
theorem returned_product (C N K : PTm n) : Γ ⊢[PRAAx] sndT (run C N K) ≐ product (euler C N) (polynomial C N K) N (K*N) :=
  (program_at C N K).sndE
theorem returned_finite_euler (C N K e : PTm n) (hL : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (fstT (run C N K)) (K*N) e ≐ exponentCoefficient (sndT (run C N K)) (N+K*N) e :=
  (GaussianRationalPolynomialExponentialStability.exponent_congr (returned_euler C N K) (.eqRefl _) (.eqRefl _)).eqTrans
    ((finite_euler C N K e hL hCan hC he hK).eqTrans
      (GaussianRationalPolynomialExponentialStability.exponent_congr (returned_product C N K).eqSymm (.eqRefl _) (.eqRefl _)))

theorem actual_high_euler_product_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 3) (var 2) ⟶ le (var 4) (var 1) ⟶ le (var 4) (var 3) ⟶
      exponentCoefficient (product (euler (var 0) (var 1)) (powerPrefix (var 0) (var 1) (var 2) (var 3)) (var 1) (var 3*var 1))
        (var 1+var 3*var 1) (var 4) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (high_product_zero _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_high_euler_summand_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 3) (var 2) ⟶ le (var 4) (var 1) ⟶ le (var 4) (var 3) ⟶
      shiftedTerm (var 0) (var 1) (var 2) (var 4) (var 3) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (high_term_zero _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_euler_sum_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 3) (var 1) ⟶ le (var 3) (var 2) ⟶
      shiftedSum (var 0) (var 1) (var 2) (var 3) (succ (var 2)) ≐ shiftedSum (var 0) (var 1) (var 2) (var 3) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (tail_cutoff _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_scaled_finite_exponential_euler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ canonicalCoefficients (var 0) ⟶ entry (var 0) (var 1) ≐ qzero ⟶
      le (var 3) (var 1) ⟶ le (var 3) (var 2) ⟶ natScale (var 3) (exponentCoefficient (polynomial (var 0) (var 1) (var 2)) (var 2*var 1) (var 3)) ≐
      exponentCoefficient (product (euler (var 0) (var 1)) (polynomial (var 0) (var 1) (var 2)) (var 1) (var 2*var 1))
        (var 1+var 2*var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI
    (finite_euler_scaled _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_finite_exponential_euler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ canonicalCoefficients (var 0) ⟶ entry (var 0) (var 1) ≐ qzero ⟶
      le (var 3) (var 1) ⟶ le (var 3) (var 2) ⟶
      exponentCoefficient (euler (polynomial (var 0) (var 1) (var 2)) (var 2*var 1)) (var 2*var 1) (var 3) ≐
      exponentCoefficient (product (euler (var 0) (var 1)) (polynomial (var 0) (var 1) (var 2)) (var 1) (var 2*var 1))
        (var 1+var 2*var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI
    (finite_euler _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem original_logarithm_finite_exponential_euler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      exponentCoefficient (euler (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 1*var 0)) (var 1*var 0) (var 2) ≐
      exponentCoefficient (product (euler (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0))
        (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 0) (var 1*var 0)) (var 0+var 1*var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (logarithm_finite_euler _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_finite_exponential_euler_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_finite_exponential_euler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ canonicalCoefficients (var 0) ⟶ entry (var 0) (var 1) ≐ qzero ⟶
      le (var 3) (var 1) ⟶ le (var 3) (var 2) ⟶ exponentCoefficient (fstT (run (var 0) (var 1) (var 2))) (var 2*var 1) (var 3) ≐
      exponentCoefficient (sndT (run (var 0) (var 1) (var 2))) (var 1+var 2*var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI
    (returned_finite_euler _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianRationalFiniteExponentialEuler
