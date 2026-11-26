import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialPowerEuler
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponentialCoefficients
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual factorial-weighted Euler sums

The original factorial weights cancel the actual positive-power Euler
multiplier. The SAME finite coefficient sum, with its original power cap,
therefore has Euler coefficients equal to a shifted finite sum of actual
E(C)*C^r product coefficients. Original polynomial shape/canonicality and
explicit numerical low-coefficient ranges are the only input guards.
No exponential derivative, Bell recurrence, or desired sum law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFactorialEulerSums

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul canonical represents canonical_unique)
open GaussianRationalSyntheticDivision (qmul_congr canonicalCoefficients rescale_to)
open GaussianRationalPolynomialExponential (inverseFactorial inverse_factorial_represents inverse_factorial_canonical factorial_positive)
open GaussianRationalNaturalScale (naturalPoint natScale natScale_congr)
open GaussianRationalPolynomialPowers (powerPrefix)
open GaussianRationalEulerCoefficients (euler)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside exponent_outside)
open GaussianRationalPolynomialProduct (product product_length)
open GaussianRationalPolynomialExponentialCoefficients (coefficientSum data term termBody term_at)
open GaussianRationalFiniteSum (sum)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem inverse_factorial_scale (r : PTm n) : Γ ⊢[PRAAx]
    natScale (succ r) (inverseFactorial (succ r)) ≐ inverseFactorial r := by
  have hL := GaussianRationalNaturalScale.natScale_represents (Γ := Γ) (succ r) (inverseFactorial (succ r))
    ComplexLogarithmRemainder.oneCode (fact (succ r)) (factorial_positive _) (inverse_factorial_represents _)
  have hR : Γ ⊢[PRAAx] represents (inverseFactorial r)
      (ComplexLogarithmRemainder.scale (succ r) ComplexLogarithmRemainder.oneCode) (fact (succ r)) :=
    rescale_to _ _ _ _ _ (inverse_factorial_represents r) (fact_succ r zero).eqSymm
  exact canonical_unique _ _ _ _ (GaussianRationalNaturalScale.natScale_canonical _ _)
    (inverse_factorial_canonical r) (factorial_positive _) hL hR

theorem inverse_factorial_multiplier (r : PTm n) : Γ ⊢[PRAAx]
    qmul (inverseFactorial (succ r)) (naturalPoint (succ r)) ≐ inverseFactorial r :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm.eqTrans (inverse_factorial_scale r))

theorem inverse_factorial_cancel (r q : PTm n) : Γ ⊢[PRAAx]
    qmul (inverseFactorial (succ r)) (qmul (naturalPoint (succ r)) q) ≐ qmul (inverseFactorial r) q :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    (qmul_congr (inverse_factorial_multiplier r) (.eqRefl _))

theorem scale_zero_value (e : PTm n) : Γ ⊢[PRAAx] natScale e qzero ≐ qzero :=
  (GaussianRationalNaturalScale.natScale_as_product _ _).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem euler_exponent_total (P D e : PTm n) : Γ ⊢[PRAAx]
    exponentCoefficient (euler P D) D e ≐ natScale e (exponentCoefficient P D e) := by
  refine .orE (lt_or_le D e) ?_ ?_
  · exact (exponent_outside _ _ _ Prf.hyp0).eqTrans
      ((natScale_congr (.eqRefl _) (exponent_outside P D e Prf.hyp0)).eqTrans (scale_zero_value e)).eqSymm
  · exact GaussianRationalEulerCoefficients.euler_exponent P D e Prf.hyp0

def getE (x : PTm n) : PTm n := sndT (sndT (sndT x))
@[simp] theorem subst_getE {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    Syn.subst σ (getE x) = getE (Syn.subst σ x) := by simp [getE]
theorem get_e (C N K e : PTm n) : Γ ⊢[PRAAx] getE (data C N K e) ≐ e := by
  have h1 := snd_pair (Γ := Γ) C (pairT N (pairT K e))
  have h2 := (congrSnd h1).eqTrans (snd_pair N (pairT K e))
  exact (congrSnd h2).eqTrans (snd_pair K e)

def eulerBody : PTm 2 := natScale (getE (var 1)) (inst2 termBody (var 0) (var 1))
def eulerSum (C N K e j : PTm n) : PTm n := sum eulerBody (succ j) (data C N K e)
@[simp] theorem subst_eulerSum {l : ℕ} (σ : Fin n → PTm l) (C N K e j : PTm n) :
    Syn.subst σ (eulerSum C N K e j) = eulerSum (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ K) (Syn.subst σ e) (Syn.subst σ j) := by simp [eulerSum]
theorem euler_body_at (C N K e k : PTm n) : Γ ⊢[PRAAx]
    inst2 eulerBody k (data C N K e) ≐ natScale e (term C N K e k) := by
  have h : inst2 eulerBody k (data C N K e) = natScale (getE (data C N K e)) (inst2 termBody k (data C N K e)) := by
    simp only [eulerBody,inst2,GaussianRationalNaturalScale.subst_natScale,subst_getE,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Syn.subst_subst]
    congr 2
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact natScale_congr (get_e C N K e) (term_at C N K e k)

theorem weighted_euler_term (C N K e k : PTm n) : Γ ⊢[PRAAx]
    natScale e (term C N K e k) ≐ qmul (inverseFactorial k)
      (exponentCoefficient (euler (powerPrefix C N K k) (k*N)) (k*N) e) :=
  (GaussianRationalNaturalScale.natScale_product e (inverseFactorial k)
    (exponentCoefficient (powerPrefix C N K k) (k*N) e)).eqSymm.eqTrans
      (qmul_congr (.eqRefl _) (euler_exponent_total _ _ _).eqSymm)

theorem coefficient_sum_euler (C N K e j : PTm n) : Γ ⊢[PRAAx]
    natScale e (coefficientSum C N K e j) ≐ eulerSum C N K e j := by
  have heq : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual
      (GaussianRationalFiniteSum.multiplyBody termBody) eulerBody (succ j)
      (pairT (naturalPoint e) (data C N K e)) (data C N K e) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift j)) :: Γ.map Fm.shift
    have h := (GaussianRationalFiniteSum.multiply_body_at (Γ := Δ) termBody (naturalPoint (Syn.shift e)) (var 0)
      (data (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift e))).eqTrans
        ((qmul_congr (.eqRefl _) (term_at _ _ _ _ _)).eqTrans
          ((GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm.eqTrans
            (euler_body_at _ _ _ _ _).eqSymm))
    simpa only [Δ,Syn.shift,GaussianRationalPolynomialExponentialCoefficients.subst_data,
      GaussianRationalNaturalScale.subst_naturalPoint,subst_pairT,ConciseIPRA.PTm.subst_succ] using h
  exact (GaussianRationalNaturalScale.natScale_as_product _ _).eqTrans
    ((GaussianRationalFiniteSum.sum_multiply termBody (naturalPoint e) (succ j) (data C N K e)).eqSymm.eqTrans
      (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ heq))

def shiftedTerm (C N K e r : PTm n) : PTm n := qmul (inverseFactorial r)
  (exponentCoefficient (product (euler C N) (powerPrefix C N K r) N (r*N)) (N+r*N) e)
def shiftedBody : PTm 2 := shiftedTerm (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (getE (var 1)) (var 0)
def shiftedSum (C N K e j : PTm n) : PTm n := sum shiftedBody j (data C N K e)
@[simp] theorem subst_shiftedTerm {l : ℕ} (σ : Fin n → PTm l) (C N K e r : PTm n) :
    Syn.subst σ (shiftedTerm C N K e r) = shiftedTerm (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ K) (Syn.subst σ e) (Syn.subst σ r) := by simp [shiftedTerm]
@[simp] theorem subst_shiftedSum {l : ℕ} (σ : Fin n → PTm l) (C N K e j : PTm n) :
    Syn.subst σ (shiftedSum C N K e j) = shiftedSum (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ K) (Syn.subst σ e) (Syn.subst σ j) := by simp [shiftedSum]
theorem shifted_term_congr {C C' N N' K K' e e' r r' : PTm n} (hC : Γ ⊢[PRAAx] C ≐ C')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hK : Γ ⊢[PRAAx] K ≐ K') (he : Γ ⊢[PRAAx] e ≐ e')
    (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx] shiftedTerm C N K e r ≐ shiftedTerm C' N' K' e' r' := by
  ipra_congr (shiftedTerm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hC, hN, hK, he, hr]
theorem shifted_body_at (C N K e r : PTm n) : Γ ⊢[PRAAx]
    inst2 shiftedBody r (data C N K e) ≐ shiftedTerm C N K e r := by
  simp only [shiftedBody,inst2,subst_shiftedTerm,subst_fstT,subst_sndT,subst_getE,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have h1 := snd_pair (Γ := Γ) C (pairT N (pairT K e))
  have h2 := (congrSnd h1).eqTrans (snd_pair N (pairT K e))
  exact shifted_term_congr (fst_pair _ _) ((congrFst h1).eqTrans (fst_pair _ _))
    ((congrFst h2).eqTrans (fst_pair _ _)) (get_e C N K e) (.eqRefl _)

theorem positive_term (C N K e r : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hr : Γ ⊢[PRAAx] lt r K)
    (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    natScale e (term C N K e (succ r)) ≐ shiftedTerm C N K e r := by
  let P := product (euler C N) (powerPrefix C N K r) N (r*N)
  let D := N+r*N
  have hD : Γ ⊢[PRAAx] le e D := le_trans he (le_add_right N (r*N))
  have hI : Γ ⊢[PRAAx] lt (monus D e) (length P) :=
    lt_congr (.eqRefl _) (product_length _ _ _ _).eqSymm
      ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))
  have hTarget : Γ ⊢[PRAAx]
      exponentCoefficient (GaussianRationalPolynomialPowerEuler.powerEuler C N K r) (succ r*N) e ≐
        qmul (naturalPoint (succ r)) (exponentCoefficient P D e) :=
    (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (by unfold D; ipra_ring) (.eqRefl _)).eqTrans
      ((exponent_inside _ D e hD).eqTrans
        ((GaussianRationalCoefficientScaling.scaled_lookup P _ (monus D e) hI).eqTrans
          (qmul_congr (.eqRefl _) (exponent_inside P D e hD).eqSymm)))
  exact (weighted_euler_term C N K e (succ r)).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianRationalPolynomialPowerEuler.power_euler_coefficient C N K r e hC hCan hr he)).eqTrans
      ((qmul_congr (.eqRefl _) hTarget).eqTrans (inverse_factorial_cancel r (exponentCoefficient P D e))))

theorem zero_term (C N K e : PTm n) : Γ ⊢[PRAAx] natScale e (term C N K e zero) ≐ qzero :=
  (weighted_euler_term C N K e zero).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianRationalPolynomialPowerEuler.zero_power_euler C N K e)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_right _))

theorem positive_sum (C N K e j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hj : Γ ⊢[PRAAx] le j K)
    (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    eulerSum C N K e j ≐ shiftedSum C N K e j := by
  have hc := GaussianRationalPolynomialPowerEuler.shift_length C N hC
  have hh : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by
    simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hCan.shift
  have hk : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift j) (Syn.shift K) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hj.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift
  have hTerms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (shiftBody eulerBody) shiftedBody j
      (data C N K e) (data C N K e) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift j) :: Γ.map Fm.shift
    have hr : Δ ⊢[PRAAx] lt (var 0) (Syn.shift K) := le_trans Prf.hyp0 hk.wk
    have h := (euler_body_at (Γ := Δ) (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift e) (succ (var 0))).eqTrans
      ((positive_term _ _ _ _ _ hc.wk hh.wk hr hn.wk).eqTrans (shifted_body_at _ _ _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,GaussianRationalPolynomialExponentialCoefficients.subst_data,inst2_shiftBody] using h
  exact (GaussianRationalFiniteSum.sum_shift_first eulerBody j (data C N K e)).eqTrans
    ((GaussianRationalSyntheticDivision.qadd_congr ((euler_body_at C N K e zero).eqTrans (zero_term C N K e))
      (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ hTerms)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalFiniteSum.sum_canonical _ _ _)))

theorem factorial_euler_sum (C N K e j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hj : Γ ⊢[PRAAx] le j K)
    (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    natScale e (coefficientSum C N K e j) ≐ shiftedSum C N K e j :=
  (coefficient_sum_euler C N K e j).eqTrans (positive_sum C N K e j hC hCan hj he)

theorem logarithm_euler_sum (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    natScale e (exponentCoefficient (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) e) ≐
      shiftedSum (GaussianFiniteLogarithmPolynomial.polynomial d) d K e e :=
  (natScale_congr (.eqRefl _) (GaussianRationalPolynomialExponentialCoefficients.logarithm_low_expansion d K e he hK)).eqTrans
    (factorial_euler_sum _ _ _ _ _ (GaussianFiniteLogarithmPolynomial.polynomial_length d)
      (GaussianFiniteLogarithmPolynomial.polynomial_canonical d) hK he)

def output (C N K e j : PTm n) : PTm n := pairT
  (natScale e (coefficientSum C N K e j)) (shiftedSum C N K e j)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (C N K e j : PTm n) : PTm n := PTm.app outputF ![C,N,K,e,j]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C N K e j : PTm n) :
    Syn.subst σ (output C N K e j) = output (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ K) (Syn.subst σ e) (Syn.subst σ j) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C N K e j : PTm n) :
    Syn.subst σ (run C N K e j) = run (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ K) (Syn.subst σ e) (Syn.subst σ j) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (C N K e j : PTm n) : Γ ⊢[PRAAx] run C N K e j ≐ output C N K e j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,K,e,j]
theorem returned_euler_sum (C N K e j : PTm n) : Γ ⊢[PRAAx]
    fstT (run C N K e j) ≐ natScale e (coefficientSum C N K e j) :=
  (congrFst (program_at C N K e j)).eqTrans (fst_pair _ _)
theorem returned_shifted_sum (C N K e j : PTm n) : Γ ⊢[PRAAx]
    sndT (run C N K e j) ≐ shiftedSum C N K e j :=
  (congrSnd (program_at C N K e j)).eqTrans (snd_pair _ _)
theorem returned_agreement (C N K e j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hj : Γ ⊢[PRAAx] le j K)
    (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx] fstT (run C N K e j) ≐ sndT (run C N K e j) :=
  (returned_euler_sum C N K e j).eqTrans
    ((factorial_euler_sum C N K e j hC hCan hj he).eqTrans (returned_shifted_sum C N K e j).eqSymm)

theorem actual_inverse_factorial_multiplier_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qmul (inverseFactorial (succ (var 0))) (naturalPoint (succ (var 0))) ≐ inverseFactorial (var 0)) :=
  closeUniv 1 (inverse_factorial_multiplier _)
theorem actual_inverse_factorial_cancel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qmul (inverseFactorial (succ (var 0))) (qmul (naturalPoint (succ (var 0))) (var 1)) ≐
      qmul (inverseFactorial (var 0)) (var 1)) := closeUniv 2 (inverse_factorial_cancel _ _)
theorem actual_total_euler_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (exponentCoefficient (euler (var 0) (var 1)) (var 1) (var 2) ≐
      natScale (var 2) (exponentCoefficient (var 0) (var 1) (var 2))) := closeUniv 3 (euler_exponent_total _ _ _)
theorem actual_coefficient_sum_euler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (natScale (var 3) (coefficientSum (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
      eulerSum (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (coefficient_sum_euler _ _ _ _ _)
theorem actual_factorial_euler_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ canonicalCoefficients (var 0) ⟶ le (var 4) (var 2) ⟶ le (var 3) (var 1) ⟶
      natScale (var 3) (coefficientSum (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
        shiftedSum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (factorial_euler_sum _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem original_logarithm_factorial_euler_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      natScale (var 2) (exponentCoefficient (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 1*var 0) (var 2)) ≐
        shiftedSum (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (var 2) (var 2)) :=
  closeUniv 3 (.impI (.impI (logarithm_euler_sum _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_factorial_euler_sum_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_factorial_euler_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ canonicalCoefficients (var 0) ⟶ le (var 4) (var 2) ⟶ le (var 3) (var 1) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (returned_agreement _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalFactorialEulerSums
