import IPRADerivations.Foundations.TelescopingNames
import IPRADerivations.Foundations.AuxiliaryEnvelope
import IPRADerivations.Analysis.Names.Rates.ErrorBudgets
import IPRADerivations.Probability.Histogram
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# The drift of a conserved quantity along Euler polygons

Packet: `foundations/ipra_local_global`, `paper/04_ode.tex`, Theorem `thm:ode-conservation` ("Polynomial
conservation compiler"), the error estimate `eq:ode-conservationerror`: if the certificate
`∑ (∂_i H) F_i = 0` kills the linear term, a full Euler step changes `H` by at most `R_H M² h²`, and
telescoping the `j` full steps and the final partial step gives `|H(U_n(t)) − H(x₀)| ≤ R_H M² T² 2^{-n}`, since
`j h² + θ² ≤ h (j h + θ) ≤ h T`.

The values `H(U_j)` along the polygon are a body `Hv(j, x)` (cleared numerators):

* `driftB`, `stepB` (with `inst2_driftB`, `inst2_stepB`): the drift `|H(U_j) − H(U_0)|` and the step change
  `|H(U_{j+1}) − H(U_j)|`;
* `drift_sum`: `|H(U_N) − H(U_0)| ≤ ∑_{j<N} |H(U_{j+1}) − H(U_j)|` (`TelescopingNames.telescope` with the
  triangle inequality `ErrorBudgets.ad_tri`);
* `drift_const`: if every step changes `H` by at most `E`, the drift after `N` steps is at most `N E`;
* `time_budget`: `j h² + θ² ≤ h (j h + θ)` for `θ ≤ h`, and `step_budget`: `N (C h²) ≤ C h T` for `N h ≤ T`,
  the arithmetic of `eq:ode-conservationerror`.

The remainder estimate `eq:ode-polyremainder` that bounds one step is `Analysis/PolynomialTaylor` in one
variable; the multivariate expansion and the represented-flow limit are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.OdeConservation

open_ipra
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.Histogram (ad_self)
open LeanProofs.IPRA.Analysis.ErrorBudgets (ad_tri)
open LeanProofs.IPRA.Foundations.TelescopingNames (telescope)
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (Hv : PTm 2)

/-- `|H(U_j) − H(U_0)|`. -/
def driftB : PTm 2 := ad Hv (Syn.subst ![zero, Syn.var 1] Hv)

/-- `|H(U_{j+1}) − H(U_j)|`. -/
def stepB : PTm 2 := ad (Syn.subst ![succ (Syn.var 0), Syn.var 1] Hv) Hv

theorem inst2_driftB (j x : PTm n) :
    inst2 (driftB Hv) j x = ad (inst2 Hv j x) (inst2 Hv zero x) := by
  simp only [inst2, driftB, PTm.subst_add, PTm.subst_monus, Syn.subst_subst]
  congr 2 <;> (congr 1; funext i; fin_cases i <;> simp)

theorem inst2_stepB (j x : PTm n) :
    inst2 (stepB Hv) j x = ad (inst2 Hv (succ j) x) (inst2 Hv j x) := by
  simp only [inst2, stepB, PTm.subst_add, PTm.subst_monus, Syn.subst_subst]
  congr 2 <;> (congr 1; funext i; fin_cases i <;> simp)

variable {Hv}

/-- `|H(U_N) − H(U_0)| ≤ ∑_{j<N} |H(U_{j+1}) − H(U_j)|`. -/
theorem drift_sum (x N : PTm n) :
    Γ ⊢[PRAAx] le (ad (inst2 Hv N x) (inst2 Hv zero x)) (ap2 (sumF (stepB Hv)) N x) := by
  have h0 : Γ ⊢[PRAAx] inst2 (driftB Hv) zero x ≐ zero := by
    rw [inst2_driftB]; exact ad_self _
  have hstep : Γ ⊢[PRAAx] Fm.all (le (inst2 (driftB Hv) (succ (Syn.var 0)) (Syn.shift x))
      (inst2 (driftB Hv) (Syn.var 0) (Syn.shift x) + inst2 (stepB Hv) (Syn.var 0) (Syn.shift x))) := by
    refine .allI ?_
    rw [inst2_driftB, inst2_driftB, inst2_stepB]
    have t := ad_tri (Γ := Γ.map Fm.shift) (inst2 Hv (succ (Syn.var 0)) (Syn.shift x))
      (inst2 Hv (Syn.var 0) (Syn.shift x)) (inst2 Hv zero (Syn.shift x))
    ipra_le sl t
  have d := telescope h0 hstep N
  rw [inst2_driftB] at d
  exact d

/-- If every step changes `H` by at most `E`, the drift after `N` steps is at most `N E`. -/
theorem drift_const {x N E : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift N) ⟶
      le (ad (inst2 Hv (succ (Syn.var 0)) (Syn.shift x)) (inst2 Hv (Syn.var 0) (Syn.shift x))) (Syn.shift E))) :
    Γ ⊢[PRAAx] le (ad (inst2 Hv N x) (inst2 Hv zero x)) (N * E) := by
  refine le_trans (drift_sum x N) (sum_le_const (stepB Hv) ?_)
  rw [inst2_stepB]
  exact h

/-- `j h² + θ² ≤ h (j h + θ)` for `θ ≤ h`: the full steps and the final partial step. -/
theorem time_budget {j h θ : PTm n} (hθ : Γ ⊢[PRAAx] le θ h) :
    Γ ⊢[PRAAx] le (j * (h * h) + θ * θ) (h * (j * h + θ)) := by
  ipra_le 𝔟 θ * sl hθ

/-- `N (C h²) ≤ C h T` for `N h ≤ T`. -/
theorem step_budget {N h T C : PTm n} (hT : Γ ⊢[PRAAx] le (N * h) T) :
    Γ ⊢[PRAAx] le (N * (C * (h * h))) (C * h * T) := by
  ipra_le 𝔟 C * 𝔟 h * sl hT

end LeanProofs.IPRA.Foundations.OdeConservation
