import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianFactorParameters
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianMonicResidualRadius
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Coefficient and root bounds throughout actual deflation

The actual input computes A0 and epsilon. At each active stage its genuine
local RD contract gives a small residual; the proved monic radius theorem
gives the original Euclidean root radius; actual synthetic division then
gives the next coefficient bound A_(j+1). Induction on the bounded universal
coefficient condition is compiled into a quantifier-free bit equation.
There is no supplied global coefficient, radius or residual invariant.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFactorBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianFactorParameters
  (initialA toleranceDenominator polynomial rootAt roots monicRD)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds (coefficientBounds natCode)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1)
open LeanProofs.IPRA.Analysis.RationalArgmin (left)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Foundations.BoundedSyntax
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stageBound (C N j : PTm n) : PTm n := GaussianFactorBudget.bound N (initialA C) j
@[simp] theorem subst_stageBound {m : ℕ} (σ : Fin n → PTm m) (C N j : PTm n) :
    Syn.subst σ (stageBound C N j) = stageBound (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ j) := by simp [stageBound]

theorem bounds_congr {C D A B : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hA : Γ ⊢[PRAAx] A ≐ B)
    (h : Γ ⊢[PRAAx] coefficientBounds C A) : Γ ⊢[PRAAx] coefficientBounds D B := by
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (coefficientBounds (var 0) (var 1) : Fm PTm 2)
    ![C,A] ![D,B] (fun i => by fin_cases i; exact hC; exact hA) (by simpa using h)
  simpa using p

theorem stage_shape (step : PR 3) (C N p q j : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    length (polynomial step C N p q j) ≐ succ (GaussianRationalDeflation.remaining N j) ⋏
      (entry (polynomial step C N p q j) zero ≐ qone) :=
  GaussianRationalDeflation.polynomial_invariant _ _ _ _ _ _ hC hm hj

theorem stage_radius_from_coefficients (step : PR 3) (C N p q j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) (hj : Γ ⊢[PRAAx] lt j N)
    (hcoeff : Γ ⊢[PRAAx] coefficientBounds (polynomial step C N p q j) (stageBound C N j)) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded (rootAt step C N p q j) (stageBound C N j+two) one := by
  have shape := stage_shape (Γ := Γ) step C N p q j hC hm (le_trans (le_succ_self _) hj)
  exact GaussianMonicResidualRadius.residual_radius _ _ _ _ (GaussianRationalDeflation.remaining_positive N j hj)
    (GaussianFactorBudget.bound_positive N (initialA C) j (GaussianFactorParameters.initial_positive C))
    (Prf.andE₁ shape) (Prf.andE₂ shape) hcoeff
    (GaussianFactorParameters.stage_small_residual step C N p q j hRD hC hm hN hp hpq hj)

theorem coefficient_step (step : PR 3) (C N p q j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) (hj : Γ ⊢[PRAAx] lt j N)
    (hcoeff : Γ ⊢[PRAAx] coefficientBounds (polynomial step C N p q j) (stageBound C N j)) :
    Γ ⊢[PRAAx] coefficientBounds (polynomial step C N p q (succ j)) (stageBound C N (succ j)) := by
  have small := le_trans (le_succ_self _) hj
  have shape := stage_shape (Γ := Γ) step C N p q j hC hm small
  have radius := stage_radius_from_coefficients step C N p q j hRD hC hm hN hp hpq hj hcoeff
  have degree : Γ ⊢[PRAAx] le (GaussianRationalDeflation.remaining N j) N :=
    le_of_eq_add ((eq_add_of_le small).eqTrans (add_comm _ _))
  have next := GaussianRationalSyntheticBounds.stage_coefficient_bounds
    (polynomial step C N p q j) (rootAt step C N p q j) (GaussianRationalDeflation.remaining N j)
    N (initialA C) j (Prf.andE₁ shape) (Prf.andE₂ shape) hcoeff radius degree
  exact bounds_congr (GaussianRationalDeflation.polynomial_succ step C N p (toleranceDenominator C N q) j).eqSymm
    (.eqRefl _) next

def invariant (step : PR 3) (C N p q j : PTm n) : Fm PTm n :=
  le j N ⟶ coefficientBounds (polynomial step C N p q j) (stageBound C N j)

@[simp] theorem subst_invariant {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N p q j : PTm n) :
    (invariant step C N p q j).subst σ = invariant step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ j) := by simp [invariant]

def coefficientSyntax (C A : PTm n) : BFm n := .all (length C) (.le
  (left (qL1 (entry (Syn.shift C) (var 0))) (natCode (Syn.shift A)))
  (left (natCode (Syn.shift A)) (qL1 (entry (Syn.shift C) (var 0)))))
theorem coefficient_formula (C A : PTm n) : formula (coefficientSyntax C A) = coefficientBounds C A := by
  simp only [coefficientSyntax,formula,BFm.le,coefficientBounds,Syn.shift,subst_length,RationalArgmin.rationalLE,le]

def invariantSyntax (step : PR 3) (C N p q j : PTm n) : BFm n :=
  .imp (.le j N) (coefficientSyntax (polynomial step C N p q j) (stageBound C N j))
theorem invariant_formula (step : PR 3) (C N p q j : PTm n) :
    formula (invariantSyntax step C N p q j) = invariant step C N p q j := by
  simp only [invariantSyntax,formula,BFm.le,coefficient_formula,invariant,le]

theorem coefficient_zero (step : PR 3) (C N p q : PTm n) : Γ ⊢[PRAAx]
    coefficientBounds (polynomial step C N p q zero) (stageBound C N zero) :=
  bounds_congr (GaussianRationalDeflation.polynomial_zero step C N p (toleranceDenominator C N q)).eqSymm
    (GaussianFactorBudget.bound_zero N (initialA C)).eqSymm (GaussianFactorParameters.initial_coefficients C)

/-- Only the QF compiled bit is inducted upon. Reflection returns the
original bounded universal coefficient condition at every numerical stage. -/
theorem all_coefficients (step : PR 3) (C N p q j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] coefficientBounds (polynomial step C N p q j) (stageBound C N j) := by
  have all : Γ ⊢[PRAAx] .all (invariant step (Syn.shift C) (Syn.shift N) (Syn.shift p) (Syn.shift q) (var 0)) := by
    have hRD' : Γ.map Fm.shift ⊢[PRAAx] monicRD step := by
      simpa only [Fm.shift,GaussianFactorParameters.subst_monicRD] using hRD.shift
    have hC' : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
      simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
    have hm' : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) zero ≐ qone := by
      simpa only [Fm.shift,Fm.subst_eq,subst_entry,GaussianRationalSyntheticDivision.subst_qone,
        ConciseIPRA.PTm.subst_zero,Syn.shift] using hm.shift
    have hN' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
      simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hN.shift
    have hp' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift p) := by
      simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hp.shift
    have hpq' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift p) (Syn.shift q) := by
      simpa only [Fm.shift,subst_le,Syn.shift] using hpq.shift
    simpa only [invariant_formula] using
      (Foundations.BoundedSyntaxInduction.induction
        (invariantSyntax step (Syn.shift C) (Syn.shift N) (Syn.shift p) (Syn.shift q) (var 0)) (Γ := Γ)
        (by
          simp only [invariant_formula,subst_invariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
          exact .impI (coefficient_zero step C N p q))
        (by
          simp only [invariant_formula,subst_invariant,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
          refine .impI ?_
          let I := invariant step (Syn.shift C) (Syn.shift N) (Syn.shift p) (Syn.shift q) (var 0)
          let Δ := le (succ (var 0)) (Syn.shift N) :: I :: Γ.map Fm.shift
          exact coefficient_step _ _ _ _ _ _ hRD'.wk.wk hC'.wk.wk hm'.wk.wk hN'.wk.wk hp'.wk.wk hpq'.wk.wk
            Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))))
  have rule : Γ ⊢[PRAAx] invariant step C N p q j := by
    simpa only [subst_invariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem all_root_radii (step : PR 3) (C N p q j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded (rootAt step C N p q j) (stageBound C N j+two) one :=
  stage_radius_from_coefficients _ _ _ _ _ _ hRD hC hm hN hp hpq hj
    (all_coefficients _ _ _ _ _ _ hRD hC hm hN hp hpq (le_trans (le_succ_self _) hj))

theorem actual_deflation_bounds_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (monicRD step ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      le one (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶ le (var 4) (var 1) ⟶
        coefficientBounds (polynomial step (var 0) (var 1) (var 2) (var 3) (var 4))
          (stageBound (var 0) (var 1) (var 4))) := by
  apply closeUniv 5
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact all_coefficients _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem actual_deflation_radii_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (monicRD step ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      le one (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶ lt (var 4) (var 1) ⟶
        GaussianRationalMetric.bounded (rootAt step (var 0) (var 1) (var 2) (var 3) (var 4))
          (stageBound (var 0) (var 1) (var 4)+two) one) := by
  apply closeUniv 5
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact all_root_radii _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianFactorBounds
