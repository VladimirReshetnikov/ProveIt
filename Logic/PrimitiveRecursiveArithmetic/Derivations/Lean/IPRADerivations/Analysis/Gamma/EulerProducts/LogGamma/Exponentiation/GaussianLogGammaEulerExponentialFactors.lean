import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.FiniteHeads.GaussianLogGammaEulerNormalizedHead
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.ResidualBounds.GaussianLogGammaEulerResidualDomain
import IPRADerivations.Analysis.Exponential.RightHalfPlane.GaussianRightHalfPlaneLogarithmExponential

/-!
# Exponential recovery of the original Euler factors

At every internal row, the exponential of the canonical logarithm
of the normalized factor recovers the very factor stored by the
original finite reciprocal-Gamma approximant. The leading factor
recovers the original signed input by the same right-half-plane law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialFactors

open_ipra
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianLogGammaEulerFactorSum (residualBody residual_at)
open GaussianLogGammaEulerHead (argument rowData shifted_source)
open GaussianLogGammaEulerResidualDomain (native centered_native linear_point)
open GaussianNameEquivalence (crossEquivalent cross_trans subst_crossEquivalent)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "datum" => GaussianRightHalfPlaneLogarithm.data

def rowExpF : PR 2 := GaussianRadiusExponentialName.nameF L
def rowExpBody : PTm 2 := exponentialInputData L residualBody

private theorem exp_data_congr {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] exponentialInputData L x ≐ exponentialInputData L y := by
  simpa [exponentialInputData, Syn.subst_var, Matrix.cons_val_zero] using
    (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (exponentialInputData L (var 0) : PTm 1)
      (σ := ![x]) (σ' := ![y]) (fun i => by fin_cases i; exact h))

private theorem cross_congr (f g : PR 2) {x x' y y' : PTm n}
    (ex : Γ ⊢[PRAAx] x ≐ x') (ey : Γ ⊢[PRAAx] y ≐ y')
    (h : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx] crossEquivalent f g x' y' := by
  simpa only [subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (crossEquivalent f g (var 0) (var 1) : Fm PTm 2)
      ![x,y] ![x',y'] (fun i => by fin_cases i; exact ex; exact ey)
      (by simpa only [subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using h))

theorem factor_point (i A B D neg : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] argument (A+succ i*D) B (D*succ i) neg ≐ GaussianGammaEulerHead.factor i (native A B neg) D := by
  let k := succ i
  have hk := zero_lt_succ (Γ := Γ) i
  have den := GaussianRationalHorner.positive_product D k hD hk
  have lead := GaussianRightHalfPlaneLogarithmOffset.linear_value (A+k*D) B (D*k) neg den
  have tail := linear_point A B D neg k hD hk
  exact lead.eqSymm.eqTrans (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) tail)

theorem row_recovery (i A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent rowExpF constantF
      (inst2 rowExpBody i (rowData A B D neg)) (GaussianGammaEulerHead.factor i (native A B neg) D) := by
  let k := succ i
  have hs : Γ ⊢[PRAAx] source (A+k*D) (D*k) neg :=
    .andI (shifted_source k A D neg h).andE₁ (GaussianRationalHorner.positive_product D k h.andE₂ (zero_lt_succ _))
  have e : Γ ⊢[PRAAx] inst2 rowExpBody i (rowData A B D neg) ≐
      exponentialInputData L (datum (A+k*D) B (D*k) neg) := by
    simpa only [rowExpBody,inst2,exponentialInputData,GaussianRadiusExponentialName.subst_data,GaussianNameBounds.subst_U]
      using exp_data_congr (residual_at i A B D neg)
  exact cross_congr rowExpF constantF e.eqSymm (factor_point i A B D neg h.andE₂)
    (GaussianRightHalfPlaneLogarithmExponential.recovery (A+k*D) B (D*k) neg hs)

/-- Every actual exponentiated residual row agrees with the corresponding
original numerical Euler factor, with fully independent precisions. -/
theorem factor_rows (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] equalRows rowExpF constantF rowExpBody GaussianGammaEulerHead.factorBody N
      (rowData A B D neg) (GaussianGammaEulerHead.data (native A B neg) D) := by
  refine .allI (.impI ?_)
  let s (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s neg) := by
    simpa [Fm.shift,Syn.shift,s,Δ,source,GaussianRightHalfPlaneArgument.source] using h.shift.wk
  have e := row_recovery (Γ := Δ) (var 0) (s A) (s B) (s D) (s neg) hs
  have point := GaussianGammaEulerHead.factor_at (Γ := Δ) (var 0) (native (s A) (s B) (s neg)) (s D)
  simpa only [equalRows,Syn.shift,GaussianLogGammaEulerHead.subst_rowData,GaussianGammaEulerHead.subst_data,
    GaussianLogGammaEulerResidualDomain.subst_native,s,Δ] using
    cross_congr rowExpF constantF (.eqRefl _) point.eqSymm e

theorem actual_canonical_Euler_logarithm_exponential_factor_rows_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 2) (var 3) ⟶
        equalRows rowExpF constantF rowExpBody GaussianGammaEulerHead.factorBody (var 4)
          (rowData (var 0) (var 1) (var 2) (var 3)) (GaussianGammaEulerHead.data (native (var 0) (var 1) (var 3)) (var 2))) :=
  closeUniv 5 (.impI (factor_rows _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialFactors
