import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerHeadCoefficientStep

/-!
# Unrestricted original Euler-head exponent-reader step

The actual original head reader is zero extended. Its successor factor
therefore gives A_(N+1)(e+1)=A_N(e+1)+a_N A_N(e) for EVERY numerical N,e,
including the leading degree, the zero stage, and every outside degree.
This discharges the range cases needed to use the real neighboring-row
rule in the Newton coefficient induction. No recurrence law is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadExponentStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside exponent_outside)
open GaussianGammaEulerHeadPolynomial (polynomial)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def reader (N e : PTm n) : PTm n := exponentCoefficient (polynomial N) (succ N) e
@[simp] theorem subst_reader {l : ℕ} (σ : Fin n → PTm l) (N e : PTm n) :
    Syn.subst σ (reader N e) = reader (Syn.subst σ N) (Syn.subst σ e) := by simp [reader]

theorem reader_congr {N M e f : PTm n} (hN : Γ ⊢[PRAAx] N ≐ M) (he : Γ ⊢[PRAAx] e ≐ f) :
    Γ ⊢[PRAAx] reader N e ≐ reader M f :=
  GaussianRationalPolynomialExponentialStability.exponent_congr
    (congrAp2 GaussianGammaEulerHeadPolynomial.headF hN (.eqRefl zero)) (congrSucc hN) he

theorem reader_zero (N : PTm n) : Γ ⊢[PRAAx] reader N zero ≐ qzero :=
  (exponent_inside _ _ _ (zero_le _)).eqTrans
    ((entry_congr (.eqRefl _) (monus_zero (succ N))).eqTrans
      (GaussianGammaEulerHeadCoefficientStep.constant_zero N))

theorem interior_step (N e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    reader (succ N) (succ e) ≐ qadd (reader N (succ e)) (qmul (reciprocalPoint N) (reader N e)) := by
  have idx := GaussianRationalPowerExpansion.remaining_before (Γ := Γ) N e he
  have oldHigh : Γ ⊢[PRAAx] reader N (succ e) ≐ entry (polynomial N) (monus N e) :=
    (exponent_inside _ _ _ ((succ_monus_succ _ _).eqTrans he)).eqTrans
      (entry_congr (.eqRefl _) (succ_monus_succ N e))
  have oldLow : Γ ⊢[PRAAx] reader N e ≐ entry (polynomial N) (succ (monus N e)) :=
    (exponent_inside _ _ _ (le_trans he (le_succ_self N))).eqTrans (entry_congr (.eqRefl _) idx)
  have nextIdx : Γ ⊢[PRAAx] monus (succ (succ N)) (succ e) ≐ succ (monus N e) :=
    (succ_monus_succ (succ N) e).eqTrans idx
  exact (exponent_inside _ _ _ (le_trans ((succ_monus_succ _ _).eqTrans he) (le_succ_self _))).eqTrans
    ((entry_congr (.eqRefl _) nextIdx).eqTrans
      ((GaussianGammaEulerHeadCoefficientStep.interior_step N (monus N e)
        (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
          (qadd_congr oldHigh.eqSymm
            ((qmul_congr oldLow.eqSymm (.eqRefl _)).eqTrans
              (GaussianRationalPowerAlgebra.qmul_commutative _ _)))))

theorem leading_reader (N : PTm n) : Γ ⊢[PRAAx]
    reader N (succ N) ≐ entry (polynomial N) zero :=
  (exponent_inside _ _ _ (le_refl _)).eqTrans (entry_congr (.eqRefl _) (monus_self _))

theorem leading_step (N : PTm n) : Γ ⊢[PRAAx]
    reader (succ N) (succ (succ N)) ≐
      qadd (reader N (succ (succ N))) (qmul (reciprocalPoint N) (reader N (succ N))) := by
  have oldZero : Γ ⊢[PRAAx] reader N (succ (succ N)) ≐ qzero :=
    exponent_outside _ _ _ (le_refl _)
  have value : Γ ⊢[PRAAx] reader (succ N) (succ (succ N)) ≐ qmul (reciprocalPoint N) (reader N (succ N)) :=
    (leading_reader (succ N)).eqTrans ((GaussianGammaEulerHeadCoefficientStep.leading_step N).eqTrans
      ((qmul_congr (leading_reader N).eqSymm (.eqRefl _)).eqTrans
        (GaussianRationalPowerAlgebra.qmul_commutative _ _)))
  exact value.eqTrans ((GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalHorner.qmul_canonical _ _)).eqSymm.eqTrans
    (qadd_congr oldZero.eqSymm (.eqRefl _)))

theorem outside_step (N e : PTm n) (he : Γ ⊢[PRAAx] lt (succ N) e) : Γ ⊢[PRAAx]
    reader (succ N) (succ e) ≐ qadd (reader N (succ e)) (qmul (reciprocalPoint N) (reader N e)) := by
  have nextZero : Γ ⊢[PRAAx] reader (succ N) (succ e) ≐ qzero :=
    exponent_outside _ _ _ ((succ_monus_succ _ _).eqTrans he)
  have oldHigh : Γ ⊢[PRAAx] reader N (succ e) ≐ qzero :=
    exponent_outside _ _ _ (le_trans he (le_succ_self e))
  have oldLow : Γ ⊢[PRAAx] reader N e ≐ qzero := exponent_outside _ _ _ he
  have value : Γ ⊢[PRAAx] qadd (reader N (succ e)) (qmul (reciprocalPoint N) (reader N e)) ≐ qzero :=
    (qadd_congr oldHigh ((qmul_congr (.eqRefl _) oldLow).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _))).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ GaussianRationalSyntheticDivision.qzero_canonical)
  exact nextZero.eqTrans value.eqSymm

theorem original_reader_step (N e : PTm n) : Γ ⊢[PRAAx]
    reader (succ N) (succ e) ≐ qadd (reader N (succ e)) (qmul (reciprocalPoint N) (reader N e)) := by
  refine .orE (lt_or_le N e) ?_ ?_
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · exact outside_step N e Prf.hyp0
    · have h : ((succ N ≐ e) :: (lt N e) :: Γ) ⊢[PRAAx]
          reader (succ N) (succ e) ≐ reader (succ N) (succ (succ N)) :=
        reader_congr (.eqRefl _) (congrSucc Prf.hyp0.eqSymm)
      exact h.eqTrans ((leading_step N).eqTrans (qadd_congr
        (reader_congr (.eqRefl _) (congrSucc Prf.hyp0))
        (qmul_congr (.eqRefl _) (reader_congr (.eqRefl _) Prf.hyp0))))
  · exact interior_step N e Prf.hyp0

theorem original_Euler_head_unrestricted_exponent_reader_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (reader (succ (var 0)) (succ (var 1)) ≐
      qadd (reader (var 0) (succ (var 1))) (qmul (reciprocalPoint (var 0)) (reader (var 0) (var 1)))) :=
  closeUniv 2 (original_reader_step _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadExponentStep
