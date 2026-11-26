import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaPowerHorizonCoherence
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponentialCoefficients

/-!
# Original Gamma exponential coefficients at a fixed finite horizon

Actual original power reader coherence identifies each original finite
factorial sum through exponent e. Original zero-constant power support
therefore identifies the SAME exponential coefficient across two unrelated
degree horizons and ambient exponential cutoffs, whenever e fits both.
An actual PR3 program computes the fixed expression using horizon e and
cutoff e. This removes those two cutoff dependencies exactly; convergence
as the original sample precision q changes remains a separate task.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaExponentialHorizonCoherence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaExponentCoefficientPolynomial (polynomial)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalPolynomialExponentialCoefficients (coefficientSum termBody data term_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_power_coefficient (q N L M K T e j : PTm n)
    (hL : Γ ⊢[PRAAx] le e (degree L)) (hM : Γ ⊢[PRAAx] le e (degree M))
    (hK : Γ ⊢[PRAAx] le j K) (hT : Γ ⊢[PRAAx] le j T) : Γ ⊢[PRAAx]
    exponentCoefficient (GaussianRationalPolynomialPowers.powerPrefix (polynomial q N L) (degree L) K j) (j*degree L) e ≐
      exponentCoefficient (GaussianRationalPolynomialPowers.powerPrefix (polynomial q N M) (degree M) T j) (j*degree M) e :=
  GaussianPolynomialLowJetProduct.jet_at _ _ _ _ _ _
    (GaussianGammaPowerHorizonCoherence.original_power_horizon q N L M K T e j hL hM hK hT) (le_refl e)

theorem factorial_sum_coherence (q N L M K T e : PTm n)
    (hL : Γ ⊢[PRAAx] le e (degree L)) (hM : Γ ⊢[PRAAx] le e (degree M))
    (hK : Γ ⊢[PRAAx] le e K) (hT : Γ ⊢[PRAAx] le e T) : Γ ⊢[PRAAx]
    coefficientSum (polynomial q N L) (degree L) K e e ≐ coefficientSum (polynomial q N M) (degree M) T e e := by
  have hl : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (degree (Syn.shift L)) := by simpa [Fm.shift,Syn.shift] using hL.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (degree (Syn.shift M)) := by simpa [Fm.shift,Syn.shift] using hM.shift
  have hk : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift K) := by simpa [Fm.shift,Syn.shift] using hK.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using hT.shift
  refine GaussianRationalFiniteSum.sum_congr_bounded termBody termBody (succ e)
    (data (polynomial q N L) (degree L) K e) (data (polynomial q N M) (degree M) T e) (.allI (.impI ?_))
  let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have powers := original_power_coefficient (Syn.shift q) (Syn.shift N) (Syn.shift L) (Syn.shift M) (Syn.shift K) (Syn.shift T)
    (Syn.shift e) (var 0) hl.wk hm.wk (le_trans hi hk.wk) (le_trans hi ht.wk)
  simpa only [Δ,GaussianRationalPolynomialExponentialCoefficients.subst_data,
    GaussianGammaExponentCoefficientPolynomial.subst_polynomial,GaussianGammaReciprocalDegreeCells.subst_degree,PTm.subst_succ,Syn.shift] using
    (term_at (Γ := Δ) (polynomial (Syn.shift q) (Syn.shift N) (Syn.shift L)) (degree (Syn.shift L))
      (Syn.shift K) (Syn.shift e) (var 0)).eqTrans
        ((qmul_congr (.eqRefl _) powers).eqTrans
          (term_at (polynomial (Syn.shift q) (Syn.shift N) (Syn.shift M)) (degree (Syn.shift M))
            (Syn.shift T) (Syn.shift e) (var 0)).eqSymm)

theorem original_exponential_horizon (q N L M K T e : PTm n)
    (hL : Γ ⊢[PRAAx] le e (degree L)) (hM : Γ ⊢[PRAAx] le e (degree M))
    (hK : Γ ⊢[PRAAx] le e K) (hT : Γ ⊢[PRAAx] le e T) : Γ ⊢[PRAAx]
    exponentCoefficient (GaussianRationalPolynomialExponential.polynomial (polynomial q N L) (degree L) K) (K*degree L) e ≐
      exponentCoefficient (GaussianRationalPolynomialExponential.polynomial (polynomial q N M) (degree M) T) (T*degree M) e :=
  (GaussianRationalPolynomialExponentialCoefficients.finite_low_expansion _ _ _ _
    (GaussianGammaPolynomialConstantLinear.input_constant q N L) hL hK).eqTrans
      ((factorial_sum_coherence q N L M K T e hL hM hK hT).eqTrans
        (GaussianRationalPolynomialExponentialCoefficients.finite_low_expansion _ _ _ _
          (GaussianGammaPolynomialConstantLinear.input_constant q N M) hM hT).eqSymm)

def fixedCoefficient (q N e : PTm n) : PTm n :=
  exponentCoefficient (GaussianRationalPolynomialExponential.polynomial (polynomial q N e) (degree e) e) (e*degree e) e
@[simp] theorem subst_fixedCoefficient {m : ℕ} (σ : Fin n → PTm m) (q N e : PTm n) :
    Syn.subst σ (fixedCoefficient q N e) = fixedCoefficient (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ e) := by simp [fixedCoefficient]

theorem canonical_horizon (q N L K e : PTm n)
    (hL : Γ ⊢[PRAAx] le e (degree L)) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (GaussianRationalPolynomialExponential.polynomial (polynomial q N L) (degree L) K) (K*degree L) e ≐
      fixedCoefficient q N e :=
  original_exponential_horizon q N L e K e e hL
    (le_of_eq_add (d := two) (by unfold degree; ipra_ring)) hK (le_refl e)

def coefficientF : PR 3 := PTm.toPR (fixedCoefficient (var 0) (var 1) (var 2))
theorem coefficient_program (q N e : PTm n) : Γ ⊢[PRAAx] PTm.app coefficientF ![q,N,e] ≐ fixedCoefficient q N e := by
  simpa only [coefficientF,subst_fixedCoefficient,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (fixedCoefficient (var 0) (var 1) (var 2) : PTm 3) ![q,N,e]

theorem original_Gamma_exponential_fixed_horizon_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (degree (var 2)) ⟶ le (var 4) (var 3) ⟶
      exponentCoefficient (GaussianRationalPolynomialExponential.polynomial (polynomial (var 0) (var 1) (var 2))
        (degree (var 2)) (var 3)) (var 3*degree (var 2)) (var 4) ≐ fixedCoefficient (var 0) (var 1) (var 4)) :=
  closeUniv 5 (.impI (.impI (canonical_horizon _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_Gamma_fixed_exponential_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (PTm.app coefficientF ![var 0,var 1,var 2] ≐ fixedCoefficient (var 0) (var 1) (var 2)) :=
  closeUniv 3 (coefficient_program _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaExponentialHorizonCoherence
