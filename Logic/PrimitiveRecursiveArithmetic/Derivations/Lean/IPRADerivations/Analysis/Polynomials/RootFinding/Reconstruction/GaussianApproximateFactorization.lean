import IPRADerivations.Analysis.Polynomials.RootFinding.Deflation.FactorTransport.GaussianFactorErrorStep
import IPRADerivations.Analysis.Inequalities.WeightedComparison.GaussianWeightedErrorBudget

/-!
# Actual uniform rational approximate factorization

Finite-demand source04 thm:approx-factor, conditional only on its explicit
local rational-descent contract. Original finite input data compute A0,
epsilon, every root, every synthetic quotient and the product polynomial.

Backward QF induction weights the actual coefficient error at stage j by
the actual prefix product of the source factors 2A_j+5. The genuine one-step
error theorem gives the local transfer, the literal final constant gives
zero terminal error, and the exact initial cap is eta. No factorization,
residual, radius, coefficient invariant or error recurrence is supplied.
The upstream RD implementation/proof remains a separate obligation.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianApproximateFactorization

open_ipra
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (initialA toleranceDenominator roots monicRD)
open LeanProofs.IPRA.Analysis.GaussianFactorErrorStep (error subst_error)
open LeanProofs.IPRA.Analysis.GaussianWeightedErrorBudget (weight cap)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Analysis.GaussianRationalDeflation (remaining subst_remaining)
open LeanProofs.IPRA.Analysis.GaussianCoefficientL1 (coefficientNorm subCoefficients)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def errorBound (step : PR 3) (C N p q j : PTm n) : Fm PTm n :=
  rationalLE (weight N (initialA C) j (error step C N p q j))
    (cap N (initialA C) p (toleranceDenominator C N q) j)

ipra_subst errorBound

theorem errorBound_congr (step : PR 3) (C N p q : PTm n) {i j : PTm n}
    (hij : Γ ⊢[PRAAx] i ≐ j) (h : Γ ⊢[PRAAx] errorBound step C N p q i) :
    Γ ⊢[PRAAx] errorBound step C N p q j :=
  RationalArgmin.rationalLE_congr
    (GaussianWeightedErrorBudget.weight_congr N (initialA C) hij (GaussianFactorErrorStep.error_index_congr step C N p q hij))
    (GaussianWeightedErrorBudget.cap_index_congr N (initialA C) p (toleranceDenominator C N q) hij) h

theorem terminal_error_bound (step : PR 3) (C N p q : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hN : Γ ⊢[PRAAx] le one N) (hq : Γ ⊢[PRAAx] le one q) :
    Γ ⊢[PRAAx] errorBound step C N p q N := by
  have actualZero := GaussianFactorErrorStep.final_error_zero (Γ := Γ) step C N p q hC hm hN
  have weightedZero := (GaussianWeightedErrorBudget.weight_congr N (initialA C) (.eqRefl N) actualZero).eqTrans
    (GaussianWeightedErrorBudget.weight_of_zero N (initialA C) N)
  have capZero := GaussianWeightedErrorBudget.cap_end N (initialA C) p (toleranceDenominator C N q)
    (GaussianFactorParameters.tolerance_positive C N q hN hq)
  exact RationalArgmin.rationalLE_congr weightedZero.eqSymm capZero.eqSymm (RationalArgmin.reflexive _)

theorem remaining_active (N k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] lt (remaining N (succ k)) N := by
  have e : Γ ⊢[PRAAx] N ≐ remaining N (succ k)+succ k := (eq_add_of_le hk).eqTrans (add_comm _ _)
  exact le_congr (by ipra_ring) e.eqSymm (add_le_add₂ (le_refl _) (zero_lt_succ k))

theorem backward_error_step (step : PR 3) (C N p q k : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] errorBound step C N p q (remaining N k)) :
    Γ ⊢[PRAAx] errorBound step C N p q (remaining N (succ k)) := by
  let j := remaining N (succ k)
  have hj : Γ ⊢[PRAAx] lt j N := remaining_active N k hk
  have nextBound := errorBound_congr step C N p q (GaussianRationalDeflation.remaining_step N k hk) ih
  exact GaussianWeightedErrorBudget.backward_step _ _ N (initialA C) p (toleranceDenominator C N q) j hj
    (GaussianFactorParameters.tolerance_positive C N q hN (le_trans hp hpq))
    (GaussianFactorErrorStep.error_step step C N p q j hRD hC hm hN hp hpq hj) nextBound

def backwardInvariant (step : PR 3) (C N p q k : PTm n) : Fm PTm n :=
  le k N ⟶ errorBound step C N p q (remaining N k)
ipra_subst backwardInvariant

theorem backward_error_bound (step : PR 3) (C N p q k : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] errorBound step C N p q (remaining N k) := by
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
  have all : Γ ⊢[PRAAx] .all (backwardInvariant step (Syn.shift C) (Syn.shift N) (Syn.shift p) (Syn.shift q) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_backwardInvariant]
    · exact .impI (errorBound_congr step C N p q (monus_zero N).eqSymm
        (terminal_error_bound step C N p q hC hm hN (le_trans hp hpq))).wk
    · refine .impI ?_
      let I := backwardInvariant step (Syn.shift C) (Syn.shift N) (Syn.shift p) (Syn.shift q) (var 0)
      exact backward_error_step _ _ _ _ _ _ hRD'.wk.wk hC'.wk.wk hm'.wk.wk hN'.wk.wk hp'.wk.wk hpq'.wk.wk
        Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] backwardInvariant step C N p q k := by
    simpa only [subst_backwardInvariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

/-- The final error estimate is derived from the actual zero terminal
error and actual one-step errors, with precisely the source eta budget. -/
theorem initial_error_bound (step : PR 3) (C N p q : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    rationalLE (error step C N p q zero) (GaussianFactorBudget.eta p q) := by
  have last := backward_error_bound step C N p q N hRD hC hm hN hp hpq (le_refl _)
  have first := errorBound_congr step C N p q (monus_self N) last
  exact RationalArgmin.rationalLE_congr
    (GaussianWeightedErrorBudget.weight_zero N (initialA C) _ (GaussianFactorErrorStep.error_guard _ _ _ _ _ _))
    (GaussianWeightedErrorBudget.initial_cap N (initialA C) p q hN (le_trans hp hpq)) first

def rootList (step : PR 3) (C N p q : PTm n) : PTm n := roots step C N p q N
def productPolynomial (step : PR 3) (C N p q : PTm n) : PTm n :=
  GaussianRationalReconstruction.reconstruct (rootList step C N p q) N N
def coefficientError (step : PR 3) (C N p q : PTm n) : PTm n :=
  coefficientNorm (subCoefficients C (productPolynomial step C N p q) (succ N))

ipra_subst rootList
ipra_subst productPolynomial
ipra_subst coefficientError

theorem rootList_length (step : PR 3) (C N p q : PTm n) : Γ ⊢[PRAAx] length (rootList step C N p q) ≐ N :=
  GaussianRationalDeflation.roots_length _ _ _ _ _ _
theorem product_length (step : PR 3) (C N p q : PTm n) : Γ ⊢[PRAAx] length (productPolynomial step C N p q) ≐ succ N :=
  GaussianRationalReconstruction.reconstruct_length _ _ _
theorem product_evaluation (step : PR 3) (C N p q y : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (productPolynomial step C N p q) y ≐
      GaussianRationalReconstruction.product (rootList step C N p q) N y :=
  GaussianRationalReconstruction.product_evaluation _ _ _

theorem approximate_factorization (step : PR 3) (C N p q : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    length (rootList step C N p q) ≐ N ⋏
      rationalLE (coefficientError step C N p q) (GaussianFactorBudget.eta p q) :=
  .andI (rootList_length _ _ _ _ _)
    (RationalArgmin.rationalLE_congr (GaussianFactorErrorStep.error_initial _ _ _ _ _) (.eqRefl _)
      (initial_error_bound step C N p q hRD hC hm hN hp hpq))

def output (step : PR 3) (C N p q : PTm n) : PTm n :=
  pairT (rootList step C N p q) (productPolynomial step C N p q)
def outputF (step : PR 3) : PR 4 := PTm.toPR (output step (var 0) (var 1) (var 2) (var 3))
ipra_subst output
theorem program_at (step : PR 3) (C N p q : PTm n) : Γ ⊢[PRAAx]
    PTm.app (outputF step) ![C,N,p,q] ≐ output step C N p q := by
  simpa [outputF] using toPR_eq (Γ := Γ) (output step (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,p,q]

def run (step : PR 3) (C N p q : PTm n) : PTm n := PTm.app (outputF step) ![C,N,p,q]

theorem returned_roots (step : PR 3) (C N p q : PTm n) : Γ ⊢[PRAAx]
    fstT (run step C N p q) ≐ rootList step C N p q :=
  (program_at _ _ _ _ _).fstE
theorem returned_polynomial (step : PR 3) (C N p q : PTm n) : Γ ⊢[PRAAx]
    sndT (run step C N p q) ≐ productPolynomial step C N p q :=
  (program_at _ _ _ _ _).sndE

theorem returned_product_evaluation (step : PR 3) (C N p q y : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (sndT (run step C N p q)) y ≐
      GaussianRationalReconstruction.product (fstT (run step C N p q)) N y := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (GaussianRationalReconstruction.product (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (run step C N p q),N,y]) (σ' := ![rootList step C N p q,N,y])
    (fun i => by fin_cases i; exact returned_roots _ _ _ _ _; exact .eqRefl _; exact .eqRefl _)
  have factors : Γ ⊢[PRAAx] GaussianRationalReconstruction.product (fstT (run step C N p q)) N y ≐
      GaussianRationalReconstruction.product (rootList step C N p q) N y := by
    simpa only [GaussianRationalReconstruction.subst_product,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h
  exact (GaussianRationalReconstruction.evaluate_congr (returned_polynomial _ _ _ _ _) (.eqRefl _)).eqTrans
    ((product_evaluation _ _ _ _ _ _).eqTrans factors.eqSymm)

theorem program_correct (step : PR 3) (C N p q : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    length (fstT (run step C N p q)) ≐ N ⋏
      (length (sndT (run step C N p q)) ≐ succ N ⋏
        rationalLE (coefficientNorm (subCoefficients C (sndT (run step C N p q)) (succ N)))
          (GaussianFactorBudget.eta p q)) := by
  have bound := Prf.andE₂ (approximate_factorization step C N p q hRD hC hm hN hp hpq)
  have errorEq := GaussianCoefficientNormOrder.coefficientNorm_congr
    (GaussianCoefficientNormOrder.subCoefficients_congr (.eqRefl C) (returned_polynomial (Γ := Γ) step C N p q) (.eqRefl (succ N)))
  exact .andI ((congrFst (returned_roots _ _ _ _ _)).eqTrans (rootList_length _ _ _ _ _))
    (.andI ((congrFst (returned_polynomial _ _ _ _ _)).eqTrans (product_length _ _ _ _ _))
      (RationalArgmin.rationalLE_congr errorEq.eqSymm (.eqRefl _) bound))

theorem uniform_approximate_factorization_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (monicRD step ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      le one (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶
        (length (rootList step (var 0) (var 1) (var 2) (var 3)) ≐ var 1 ⋏
          rationalLE (coefficientError step (var 0) (var 1) (var 2) (var 3))
            (GaussianFactorBudget.eta (var 2) (var 3)))) := by
  apply closeUniv 4
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact approximate_factorization _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem actual_product_evaluation_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalHorner.evaluate (productPolynomial step (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
      GaussianRationalReconstruction.product (rootList step (var 0) (var 1) (var 2) (var 3)) (var 1) (var 4)) :=
  closeUniv 5 (product_evaluation _ _ _ _ _ _)

theorem approximate_factorization_program_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app (outputF step) ![var 0,var 1,var 2,var 3] ≐ output step (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _ _)

theorem returned_approximate_factorization_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (monicRD step ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      le one (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶
        (length (fstT (run step (var 0) (var 1) (var 2) (var 3))) ≐ var 1 ⋏
          (length (sndT (run step (var 0) (var 1) (var 2) (var 3))) ≐ succ (var 1) ⋏
            rationalLE (coefficientNorm (subCoefficients (var 0)
                (sndT (run step (var 0) (var 1) (var 2) (var 3))) (succ (var 1))))
              (GaussianFactorBudget.eta (var 2) (var 3))))) := by
  apply closeUniv 4
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact program_correct _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem returned_product_evaluation_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalHorner.evaluate (sndT (run step (var 0) (var 1) (var 2) (var 3))) (var 4) ≐
      GaussianRationalReconstruction.product (fstT (run step (var 0) (var 1) (var 2) (var 3))) (var 1) (var 4)) :=
  closeUniv 5 (returned_product_evaluation _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianApproximateFactorization
