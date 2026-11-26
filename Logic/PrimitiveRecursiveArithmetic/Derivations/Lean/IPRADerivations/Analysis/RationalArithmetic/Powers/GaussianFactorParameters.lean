import IPRADerivations.Analysis.Polynomials.GaussianInitialCoefficientBound
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianFactorBudget
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSyntheticBounds
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalDeflation

/-!
# Computed input parameters and actual deflation residuals

The original polynomial, degree and rational eta=p/q compute A0 and the
raw positive denominator 2NLq of epsilon. The actual outer loop receives
these data directly. A uniform local RD contract for monic polynomials is
the only algebraic-existence premise: stage shape and monicity derive its
applicability, and the actual approximate-root clock derives each residual.
Neither a stage residual nor the initial coefficient bound is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFactorParameters

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds (coefficientBounds natCode)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def initialA (C : PTm n) : PTm n := GaussianInitialCoefficientBound.initialBound C (length C)
def toleranceDenominator (C N q : PTm n) : PTm n := GaussianFactorBudget.cost N (initialA C)*q
def polynomial (step : PR 3) (C N p q j : PTm n) : PTm n :=
  GaussianRationalDeflation.polynomial step C N p (toleranceDenominator C N q) j
def rootAt (step : PR 3) (C N p q j : PTm n) : PTm n :=
  GaussianRationalDeflation.rootAt step C N p (toleranceDenominator C N q) j
def roots (step : PR 3) (C N p q j : PTm n) : PTm n :=
  GaussianRationalDeflation.roots step C N p (toleranceDenominator C N q) j
def run (step : PR 3) (C N p q : PTm n) : PTm n :=
  GaussianRationalDeflation.run step C N p (toleranceDenominator C N q)

@[simp] theorem subst_initialA {m : ℕ} (σ : Fin n → PTm m) (C : PTm n) :
    Syn.subst σ (initialA C) = initialA (Syn.subst σ C) := by simp [initialA]
@[simp] theorem subst_toleranceDenominator {m : ℕ} (σ : Fin n → PTm m) (C N q : PTm n) :
    Syn.subst σ (toleranceDenominator C N q) = toleranceDenominator (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ q) := by
  simp [toleranceDenominator]
@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N p q j : PTm n) :
    Syn.subst σ (polynomial step C N p q j) = polynomial step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ j) := by simp [polynomial]
@[simp] theorem subst_rootAt {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N p q j : PTm n) :
    Syn.subst σ (rootAt step C N p q j) = rootAt step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ j) := by simp [rootAt]
@[simp] theorem subst_roots {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N p q j : PTm n) :
    Syn.subst σ (roots step C N p q j) = roots step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ j) := by simp [roots]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N p q : PTm n) :
    Syn.subst σ (run step C N p q) = run step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) := by
  simp only [run,GaussianRationalDeflation.run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> simp [subst_toleranceDenominator]

/-- The source RD schema, restricted to precisely the monic finite
polynomials needed by deflation. This is not a residual or output law. -/
def monicRD (step : PR 3) : Fm PTm n := .all (.all
  (le one (var 1) ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
    GaussianDescentClock.localRD step (var 1) (var 0)))

@[simp] theorem subst_monicRD {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) :
    (monicRD step : Fm PTm n).subst σ = (monicRD step : Fm PTm m) := by simp [monicRD]

theorem monic_rd_at (step : PR 3) (d C : PTm n) (h : Γ ⊢[PRAAx] monicRD step)
    (hd : Γ ⊢[PRAAx] le one d) (hC : Γ ⊢[PRAAx] length C ≐ succ d)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx] GaussianDescentClock.localRD step d C := by
  have rule : Γ ⊢[PRAAx] le one d ⟶ length C ≐ succ d ⟶ entry C zero ≐ qone ⟶
      GaussianDescentClock.localRD step d C := by
    simpa [monicRD] using (h.allE d).allE C
  exact .impE (.impE (.impE rule hd) hC) hm

theorem initial_positive (C : PTm n) : Γ ⊢[PRAAx] le one (initialA C) :=
  GaussianInitialCoefficientBound.initial_positive _ _

theorem initial_coefficients (C : PTm n) : Γ ⊢[PRAAx] coefficientBounds C (initialA C) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_initialA,initialA,natCode,GaussianInitialCoefficientBound.naturalCode,
    GaussianInitialCoefficientBound.subst_initialBound,subst_length] using
    GaussianInitialCoefficientBound.coefficient_bound (Syn.shift C) (length (Syn.shift C)) (var 0) Prf.hyp0

theorem tolerance_positive (C N q : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hq : Γ ⊢[PRAAx] le one q) :
    Γ ⊢[PRAAx] le one (toleranceDenominator C N q) := GaussianFactorBudget.epsilon_denominator_positive _ _ _ hN hq

theorem tolerance_le_one (C N p q : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le p (toleranceDenominator C N q) :=
  le_trans hpq (le_congr (one_mul q) (.eqRefl _)
    (le_mul_mono (GaussianFactorBudget.cost_positive _ _ hN) (le_refl q)))

theorem bounded_le_one (z p f : PTm n) (hf : Γ ⊢[PRAAx] le one f)
    (hpf : Γ ⊢[PRAAx] le p f) (hz : Γ ⊢[PRAAx] GaussianRationalMetric.bounded z p f) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded z one one := by
  have ht : Γ ⊢[PRAAx] rationalLE (GaussianRationalMetric.squaredTolerance p f)
      (GaussianRationalMetric.squaredTolerance one one) :=
    GaussianRationalMetric.comparison_of_cleared _ _ _ _ (f*f) (one*one)
      (GaussianRationalHorner.positive_product _ _ hf hf)
      (GaussianRationalHorner.positive_product _ _ (le_refl one) (le_refl one))
      (GaussianRationalMetric.squared_tolerance_represents _ _ hf)
      (GaussianRationalMetric.squared_tolerance_represents _ _ (le_refl _))
      (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono hpf hpf))
  exact RationalArgmin.transitive hz ht

theorem stage_rd (step : PR 3) (C N p q j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    GaussianDescentClock.localRD step (GaussianRationalDeflation.remaining N j) (polynomial step C N p q j) := by
  have h := GaussianRationalDeflation.polynomial_invariant step C N p (toleranceDenominator C N q) j
    hC hm (le_trans (le_succ_self _) hj)
  exact monic_rd_at step _ _ hRD (GaussianRationalDeflation.remaining_positive N j hj) (Prf.andE₁ h) (Prf.andE₂ h)

theorem stage_residual (step : PR 3) (C N p q j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hq : Γ ⊢[PRAAx] le one q) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded
      (GaussianRationalHorner.evaluate (polynomial step C N p q j) (rootAt step C N p q j)) p (toleranceDenominator C N q) :=
  Prf.andE₂ (GaussianDescentClock.approximate_root step _ _ _ _
    (stage_rd step C N p q j hRD hC hm hj) hp (tolerance_positive C N q hN hq))

theorem stage_small_residual (step : PR 3) (C N p q j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded
      (GaussianRationalHorner.evaluate (polynomial step C N p q j) (rootAt step C N p q j)) one one :=
  bounded_le_one _ _ _ (tolerance_positive C N q hN (le_trans hp hpq)) (tolerance_le_one C N p q hN hpq)
    (stage_residual step C N p q j hRD hC hm hN hp (le_trans hp hpq) hj)

def outputF (step : PR 3) : PR 4 := PTm.toPR (run step (var 0) (var 1) (var 2) (var 3))
theorem program_at (step : PR 3) (C N p q : PTm n) : Γ ⊢[PRAAx]
    PTm.app (outputF step) ![C,N,p,q] ≐ run step C N p q := by
  simpa [outputF] using toPR_eq (Γ := Γ) (run step (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,p,q]

theorem factor_parameters_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶
      (coefficientBounds (var 0) (initialA (var 0)) ⋏
        (le one (initialA (var 0)) ⋏
          (le one (toleranceDenominator (var 0) (var 1) (var 3)) ⋏
            le (var 2) (toleranceDenominator (var 0) (var 1) (var 3)))))) :=
  closeUniv 4 (.impI (.impI (.impI (.andI (initial_coefficients _) (.andI (initial_positive _)
    (.andI (tolerance_positive _ _ _ hyp2 (le_trans Prf.hyp1 Prf.hyp0)) (tolerance_le_one _ _ _ _ hyp2 Prf.hyp0)))))))

theorem actual_stage_residual_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (monicRD step ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      le one (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶ lt (var 4) (var 1) ⟶
        GaussianRationalMetric.bounded
          (GaussianRationalHorner.evaluate (polynomial step (var 0) (var 1) (var 2) (var 3) (var 4))
            (rootAt step (var 0) (var 1) (var 2) (var 3) (var 4))) one one) := by
  apply closeUniv 5
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact stage_small_residual _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianFactorParameters
