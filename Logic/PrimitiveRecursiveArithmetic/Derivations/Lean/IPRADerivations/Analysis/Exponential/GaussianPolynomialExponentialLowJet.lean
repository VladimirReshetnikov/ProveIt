import IPRADerivations.Analysis.Gamma.GaussianGammaPowerHorizonCoherence
import IPRADerivations.Analysis.Exponential.GaussianRationalPolynomialExponentialCoefficients

/-!
# Agreement of low coefficients in the original finite exponential

The original power-prefix programs agree on the retained input degrees.
Their actual factorial-weighted sums agree through the same degrees.
With zero input constants, the original finite exponential coefficients
are those sums even when the operand degrees and exponential cutoffs differ.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialExponentialLowJet

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPolynomialLowJetProduct (jetEqual jet_at subst_jetEqual)
open GaussianRationalHorner (qzero)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalPolynomialExponential (polynomial)
open GaussianRationalPolynomialExponentialCoefficients (coefficientSum data term_at termBody subst_data)
open GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem factorial_sum_agreement (C N D M K T e : PTm n)
    (h : Γ ⊢[PRAAx] jetEqual C N D M e)
    (hN : Γ ⊢[PRAAx] le e N) (hM : Γ ⊢[PRAAx] le e M)
    (hK : Γ ⊢[PRAAx] le e K) (hT : Γ ⊢[PRAAx] le e T) : Γ ⊢[PRAAx]
    coefficientSum C N K e e ≐ coefficientSum D M T e e := by
  let s (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] jetEqual (s C) (s N) (s D) (s M) (s e) := by
    simpa only [Fm.shift,Syn.shift,s,subst_jetEqual] using h.shift
  have shift_order {a : PTm n} (ha : Γ ⊢[PRAAx] le e a) : Γ.map Fm.shift ⊢[PRAAx] le (s e) (s a) := by
    simpa only [Fm.shift,Syn.shift,s,subst_le] using ha.shift
  refine GaussianRationalFiniteSum.sum_congr_bounded termBody termBody (succ e) (data C N K e) (data D M T e) (.allI (.impI ?_))
  let Δ := lt (var 0) (succ (s e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (s e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have powers := GaussianGammaPowerHorizonCoherence.power_jet (s C) (s N) (s D) (s M) (s K) (s T) (s e)
    (var 0) hs.wk (shift_order hN).wk (shift_order hM).wk
    (le_trans hi (shift_order hK).wk) (le_trans hi (shift_order hT).wk)
  have coeff := jet_at _ _ _ _ _ (s e) powers (le_refl (s e))
  simpa only [Δ,s,Syn.shift,subst_data,ConciseIPRA.PTm.subst_succ] using
    (term_at (Γ := Δ) (s C) (s N) (s K) (s e) (var 0)).eqTrans
      ((qmul_congr (.eqRefl _) coeff).eqTrans (term_at (s D) (s M) (s T) (s e) (var 0)).eqSymm)

theorem exponential_coefficient (C N D M K T e : PTm n)
    (h : Γ ⊢[PRAAx] jetEqual C N D M e) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hD : Γ ⊢[PRAAx] entry D M ≐ qzero)
    (hN : Γ ⊢[PRAAx] le e N) (hM : Γ ⊢[PRAAx] le e M)
    (hK : Γ ⊢[PRAAx] le e K) (hT : Γ ⊢[PRAAx] le e T) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial C N K) (K*N) e ≐ exponentCoefficient (polynomial D M T) (T*M) e :=
  (GaussianRationalPolynomialExponentialCoefficients.finite_low_expansion C N K e hC hN hK).eqTrans
    ((factorial_sum_agreement C N D M K T e h hN hM hK hT).eqTrans
      (GaussianRationalPolynomialExponentialCoefficients.finite_low_expansion D M T e hD hM hT).eqSymm)

end LeanProofs.IPRA.Analysis.GaussianPolynomialExponentialLowJet
