import IPRADerivations.Analysis.GaussianGammaCombinedEulerKernelPolynomial
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CommonLemmas

/-!
# Literal original Gamma recurrence weights independent of the horizon

A real finite selector program returns one at degree zero, the SAME
sampled gamma at degree one, and the SAME signed reconstructed zeta
sample at every higher degree. Actual original combined-kernel exponent
readers equal this program whenever the requested degree fits. All
numeric degree cases, including zero, are derived internally; no wanted
coefficient or output equation is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRecurrenceWeights

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaCombinedEulerKernelPolynomial (polynomial)
open RationalGaussianEmbedding (embed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weight (q N m : PTm n) : PTm n := RationalArithmetic.select (Signum.sg m) qone
  (RationalArithmetic.select (Signum.sg (pred m)) (embed (GammaEulerConstantName.gammaSample q zero))
    (qmul (parityPoint (pred m)) (embed (RationalReciprocalPowerName.reconstructedSample q m N))))
@[simp] theorem subst_weight {l : ℕ} (σ : Fin n → PTm l) (q N m : PTm n) :
    Syn.subst σ (weight q N m) = weight (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ m) := by simp [weight,Signum.sg]

theorem weight_congr {q p N M m k : PTm n} (hq : Γ ⊢[PRAAx] q ≐ p)
    (hN : Γ ⊢[PRAAx] N ≐ M) (hm : Γ ⊢[PRAAx] m ≐ k) : Γ ⊢[PRAAx] weight q N m ≐ weight p M k := by
  ipra_congr (weight (var 0) (var 1) (var 2) : PTm 3) with [hq, hN, hm]

theorem weight_zero (q N : PTm n) : Γ ⊢[PRAAx] weight q N zero ≐ qone :=
  RationalArithmetic.select_zero _ _ _ Signum.sg_zero

alias sg_congr := Common.congrSg

theorem weight_one (q N : PTm n) : Γ ⊢[PRAAx]
    weight q N one ≐ embed (GammaEulerConstantName.gammaSample q zero) :=
  (RationalArithmetic.select_one _ _ _ (Signum.sg_succ zero)).eqTrans
    (RationalArithmetic.select_zero _ _ _ ((sg_congr (pred_succ zero)).eqTrans Signum.sg_zero))

theorem weight_high (q N j : PTm n) : Γ ⊢[PRAAx] weight q N (degree j) ≐
    qmul (parityPoint (succ j)) (embed (RationalReciprocalPowerName.reconstructedSample q (degree j) N)) :=
  (RationalArithmetic.select_one _ _ _ (Signum.sg_succ (succ j))).eqTrans
    ((RationalArithmetic.select_one _ _ _ ((sg_congr (pred_succ (succ j))).eqTrans (Signum.sg_succ j))).eqTrans
      (qmul_congr (GaussianGammaEulerHeadLogarithmicKernel.parity_congr (pred_succ (succ j))) (.eqRefl _)))

theorem original_kernel_reader (q N L m : PTm n) (hm : Γ ⊢[PRAAx] le m (degree L)) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial q N L) (degree L) m ≐ weight q N m := by
  refine .orE (zero_or_succ m) ?_ ?_
  · exact (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      ((GaussianGammaPolynomialConstantLinear.constant_reader _ _).eqTrans
        ((GaussianGammaCombinedEulerKernelPolynomial.constant q N L).eqTrans
          ((weight_zero q N).eqSymm.eqTrans (weight_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))))
  · refine .orE (zero_or_succ (pred m)) ?_ ?_
    · have form : ((pred m ≐ zero) :: (m ≐ succ (pred m)) :: Γ) ⊢[PRAAx] m ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have bound := le_congr form (.eqRefl _) hm.wk.wk
      exact (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) form).eqTrans
        ((exponent_inside _ _ _ bound).eqTrans
          ((GaussianGammaCombinedEulerKernelPolynomial.linear q N L).eqTrans
            ((weight_one q N).eqSymm.eqTrans (weight_congr (.eqRefl _) (.eqRefl _) form.eqSymm))))
    · have form : ((pred m ≐ succ (pred (pred m))) :: (m ≐ succ (pred m)) :: Γ) ⊢[PRAAx]
          m ≐ degree (pred (pred m)) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have bound := le_congr form (.eqRefl _) hm.wk.wk
      have index : ((pred m ≐ succ (pred (pred m))) :: (m ≐ succ (pred m)) :: Γ) ⊢[PRAAx] le (pred (pred m)) L :=
        (succ_monus_succ _ _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans bound)
      exact (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) form).eqTrans
        ((exponent_inside _ _ _ bound).eqTrans
          ((GaussianGammaCombinedEulerKernelPolynomial.high q N L _ index).eqTrans
            ((weight_high q N _).eqSymm.eqTrans (weight_congr (.eqRefl _) (.eqRefl _) form.eqSymm))))

def weightF : PR 3 := PTm.toPR (weight (var 0) (var 1) (var 2))
theorem weight_program (q N m : PTm n) : Γ ⊢[PRAAx] ap3 weightF q N m ≐ weight q N m := by
  simpa [weightF,ap3] using toPR_eq (Γ := Γ) (weight (var 0) (var 1) (var 2) : PTm 3) ![q,N,m]

theorem original_Gamma_combined_kernel_reader_is_literal_recurrence_weight_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le (var 3) (degree (var 2)) ⟶
        exponentCoefficient (polynomial (var 0) (var 1) (var 2)) (degree (var 2)) (var 3) ≐
          weight (var 0) (var 1) (var 3)) := closeUniv 4 (.impI (original_kernel_reader _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaRecurrenceWeights
