import IPRADerivations.Analysis.Polynomials.GaussianRationalPolynomialProductDegree
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalCurveFibers

/-!
# Nonzero values of the actual Gaussian rational power

This is used when evaluating the accumulated product of earlier
fiber factors at a distinct abscissa. The original base is canonical,
and every numerical exponent uses the actual primitive recursion.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPowerNonzero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (canonical qzero subst_canonical subst_qzero)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_zero_right)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power power_zero power_succ power_canonical subst_power)
open ConciseIPRA.PTm (zero succ)
open scoped Fm
open Syn

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem power_nonzero (q k : PTm n) (hc : Γ ⊢[PRAAx] canonical q)
    (hz : Γ ⊢[PRAAx] neg (q ≐ qzero)) :
    Γ ⊢[PRAAx] neg (power q k ≐ qzero) := by
  have all : Γ ⊢[PRAAx] .all (neg (power (Syn.shift q) (var 0) ≐ qzero)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simp only [neg,Fm.subst_imp,Fm.subst_eq,Fm.subst_bot,subst_power,subst_qzero,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero
        ((power_zero q).eqSymm.eqTrans Prf.hyp0))
    · simp only [neg,Fm.subst_imp,Fm.subst_eq,Fm.subst_bot,subst_power,subst_qzero,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let q' := Syn.shift q
      let j : PTm (n + 1) := var 0
      let Δ := neg (power q' j ≐ qzero) :: Γ.map Fm.shift
      have hcs : Γ.map Fm.shift ⊢[PRAAx] canonical q' := by
        simpa only [q',Fm.shift,subst_canonical,Syn.shift] using hc.shift
      have hzs : Γ.map Fm.shift ⊢[PRAAx] neg (q' ≐ qzero) := by
        simpa only [q',Fm.shift,neg,Fm.subst_imp,Fm.subst_eq,Fm.subst_bot,subst_qzero,Syn.shift] using hz.shift
      have nonzero := GaussianRationalPolynomialProductDegree.multiply_nonzero (Γ := Δ)
        (power q' j) q' (power_canonical _ _) hcs.wk Prf.hyp0 hzs.wk
      have eq := power_succ (Γ := Δ) q' j
      exact .impI (.impE nonzero.wk (eq.wk.eqSymm.eqTrans Prf.hyp0))
  simpa only [neg,Fm.subst_imp,Fm.subst_eq,Fm.subst_bot,subst_power,subst_qzero,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem zero_positive_power (k : PTm n) : Γ ⊢[PRAAx] power qzero (succ k) ≐ qzero :=
  (power_succ _ _).eqTrans (qmul_zero_right _)

theorem actual_power_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (canonical (var 0) ⟶ neg (var 0 ≐ qzero) ⟶ neg (power (var 0) (var 1) ≐ qzero)) :=
  closeUniv 2 (.impI (.impI (power_nonzero _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_zero_positive_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (power qzero (succ (var 0)) ≐ qzero) :=
  closeUniv 1 (zero_positive_power _)

end LeanProofs.IPRA.Analysis.GaussianRationalPowerNonzero
