import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadius
import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticDivision
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual nonconstancy of a positive-degree monic Gaussian polynomial

The decoded raw numerator of the squared norm of canonical Gaussian one
is positive by its two actual scalar representations. Consequently the
original leading coefficient supplies the internal positive-degree witness
required by the balanced-radius constructor. No raw normalization identity
or nonconstancy certificate is supplied as an additional premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianMonicNonconstant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq oneCode normSq_one)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem raw_norm_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx]
    normSq (rawGaussian q) ≐ normSq (rawGaussian r) := by
  ipra_congr (normSq (rawGaussian (var 0)) : PTm 1) with [h]

/-- Positivity is derived from the actual Gaussian-one value and the
actual decoded denominator, rather than a host computation of its code. -/
theorem one_norm_positive : Γ ⊢[PRAAx] le one (normSq (rawGaussian (qone : PTm n))) := by
  have canonicalValue := GaussianRationalMetric.qnormSq_represents (Γ := Γ) (qone : PTm n) oneCode one
    (le_refl _) (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))
  have rawValue := GaussianRationalMetric.qnormSq_represents (Γ := Γ) (qone : PTm n)
    (rawGaussian qone) (rawDen qone) (raw_den_positive _) (raw_represents _)
  have comparison := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ canonicalValue rawValue
    (RationalArgmin.reflexive _)
  have cleared : Γ ⊢[PRAAx] le (rawDen (qone : PTm n)*rawDen qone) (normSq (rawGaussian qone)) :=
    le_congr ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring)) (by ipra_ring) comparison
  exact le_trans (positive_product _ _ (raw_den_positive _) (raw_den_positive _)) cleared

theorem leading_coefficient (C N : PTm n) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.coefficient C N N ≐ entry C zero :=
  Foundations.SequenceComposition.entry_congr (.eqRefl _) (monus_self N)

theorem leading_norm_positive (C N : PTm n) (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx]
    le one (GaussianBalancedRadiusSyntax.numerator C N N) :=
  le_congr (.eqRefl _) (raw_norm_congr ((leading_coefficient C N).eqTrans hMonic)).eqSymm one_norm_positive

theorem monic_nonconstant (C N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.nonconstant C N := by
  refine .exI N ?_
  simpa [GaussianBalancedRadiusSyntax.nonconstant] using
    Prf.andI hN (Prf.andI (le_refl N) (leading_norm_positive C N hMonic))

theorem radius_input (C N : PTm n) (hLen : Γ ⊢[PRAAx] Foundations.SequenceComposition.length C ≐ succ N)
    (hN : Γ ⊢[PRAAx] le one N) (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx]
    GaussianBalancedRadius.inputContract C N :=
  .andI hLen (.andI hN (monic_nonconstant C N hN hMonic))

theorem monic_nonconstant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      (le one (GaussianBalancedRadiusSyntax.numerator (var 0) (var 1) (var 1)) ⋏
        GaussianBalancedRadiusSyntax.nonconstant (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (.andI (leading_norm_positive _ _ Prf.hyp0)
    (monic_nonconstant _ _ Prf.hyp1 Prf.hyp0))))

theorem monic_radius_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Foundations.SequenceComposition.length (var 0) ≐ succ (var 1) ⟶ le one (var 1) ⟶
      entry (var 0) zero ≐ qone ⟶ GaussianBalancedRadius.inputContract (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (.impI (radius_input _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianMonicNonconstant
