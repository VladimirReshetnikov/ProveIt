import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.Monic.GaussianMonicPositiveDecrease
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.Monic.GaussianMonicDescentBranch

/-!
# A constructed uniform local descent for monic rational polynomials

The concrete PR3 displacement uses the original polynomial, degree and
point. Its zero-residual branch returns zero; its positive branch is the
constructed translated dominant-term displacement. Both branches prove
the unchanged source contraction. The ordinary iPRA monicRD sentence is
derived with no RD, phase, approximate-root or output-law premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianMonicRD

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qadd canonical)
open LeanProofs.IPRA.Analysis.GaussianDescentClock (residualNumerator)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def descent : PR 3 := GaussianMonicPositiveDecrease.deltaF
def step : PR 3 := GaussianMonicDescentBranch.step descent
def delta (N C z : PTm n) : PTm n := GaussianMonicDescentBranch.branchDelta descent N C z
def next (N C z : PTm n) : PTm n := qadd z (delta N C z)

ipra_subst delta
ipra_subst next

theorem positive_at (N C z : PTm n) (hInput : Γ ⊢[PRAAx] GaussianTranslatedBalancedRadius.inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residualNumerator C z)) : Γ ⊢[PRAAx]
    GaussianMonicDescentBranch.positiveAt descent N C z :=
  GaussianMonicPositiveDecrease.positive_program_decrease C N z hInput hPositive

theorem positive_local (N C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx]
    GaussianMonicDescentBranch.positiveLocal descent N C := by
  have input : Γ ⊢[PRAAx] GaussianTranslatedBalancedRadius.inputContract C N := .andI hC (.andI hN hm)
  have shifted : Γ.map Fm.shift ⊢[PRAAx] GaussianTranslatedBalancedRadius.inputContract (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianTranslatedBalancedRadius.subst_inputContract,Syn.shift] using input.shift
  refine .allI (.impI (.impI ?_))
  exact positive_at (Syn.shift N) (Syn.shift C) (var 0) shifted.wk.wk Prf.hyp0

theorem local_rd (N C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx]
    GaussianDescentClock.localRD step N C :=
  GaussianMonicDescentBranch.local_rd_of_positive descent N C (positive_local N C hN hC hm)

theorem positive_monic : Γ ⊢[PRAAx] (GaussianMonicDescentBranch.positiveMonic descent : Fm PTm n) := by
  refine .allI (.allI (.impI (.impI (.impI ?_))))
  exact positive_local (var 1) (var 0) Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

/-- The uniform object-theory RD sentence for the actual fixed program. -/
theorem monic_rd : Γ ⊢[PRAAx] (GaussianFactorParameters.monicRD step : Fm PTm n) :=
  GaussianMonicDescentBranch.monic_rd_of_positive descent positive_monic

theorem program_at (N C z : PTm n) : Γ ⊢[PRAAx] ap3 step N C z ≐ next N C z :=
  (GaussianDescentClock.increment_step_at _ _ _ _).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (GaussianMonicDescentBranch.branch_at descent N C z))

theorem advance_at (N C z : PTm n) : Γ ⊢[PRAAx] GaussianDescentClock.advance step N C z ≐ next N C z :=
  GaussianMonicDescentBranch.advance_branch descent N C z

theorem actual_rd_at (N C z : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hz : Γ ⊢[PRAAx] canonical z) : Γ ⊢[PRAAx] GaussianDescentClock.rdAt step N C z := by
  have h := local_rd N C hN hC hm
  have rule : Γ ⊢[PRAAx] canonical z ⟶ GaussianDescentClock.rdAt step N C z := by
    simpa [GaussianDescentClock.localRD] using h.allE z
  exact .impE rule hz

theorem next_canonical (N C z : PTm n) : Γ ⊢[PRAAx] canonical (next N C z) := GaussianRationalHorner.qadd_canonical _ _

theorem constructed_monic_rd_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] GaussianFactorParameters.monicRD step := monic_rd

theorem constructed_local_rd_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ length (var 1) ≐ succ (var 0) ⟶ entry (var 1) zero ≐ qone ⟶
      GaussianDescentClock.localRD step (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (.impI (local_rd _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem constructed_step_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 step (var 0) (var 1) (var 2) ≐ next (var 0) (var 1) (var 2)) ⋏
      GaussianDescentClock.advance step (var 0) (var 1) (var 2) ≐ next (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.andI (program_at _ _ _) (advance_at _ _ _))

end LeanProofs.IPRA.Analysis.GaussianMonicRD
