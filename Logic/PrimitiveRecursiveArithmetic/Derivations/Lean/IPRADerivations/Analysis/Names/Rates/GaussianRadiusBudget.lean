import IPRADerivations.AnalyticNumberTheory.GoldbachGeometric
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalL1

/-!
# Strict geometric budget for the monic residual radius

With R=A+2 and positive runtime degree N, the actual finite geometric
sum gives A sum_(k<N) R^k+1 < R^N. This is the strict numerical gap
needed by the reciprocal proof that a monic polynomial cannot have residual
at most one outside its coefficient radius. The polynomial estimate is
not assumed or asserted here; it remains a separate proof obligation.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRadiusBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.GoldbachGeometric (gB inst2_gB geom_sum)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radius (A : PTm n) : PTm n := A+two
def geometric (A N : PTm n) : PTm n := ap2 (sumF gB) N (radius A)
def numerator (A N : PTm n) : PTm n := A*geometric A N+one
def bound (A N : PTm n) : PTm n := normalize (ZT.ofNat (numerator A N)) (pw (radius A) N)

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) :
    Syn.subst σ (radius A) = radius (Syn.subst σ A) := by simp [radius]
@[simp] theorem subst_geometric {m : ℕ} (σ : Fin n → PTm m) (A N : PTm n) :
    Syn.subst σ (geometric A N) = geometric (Syn.subst σ A) (Syn.subst σ N) := by simp [geometric]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (A N : PTm n) :
    Syn.subst σ (numerator A N) = numerator (Syn.subst σ A) (Syn.subst σ N) := by simp [numerator]
@[simp] theorem subst_bound {m : ℕ} (σ : Fin n → PTm m) (A N : PTm n) :
    Syn.subst σ (bound A N) = bound (Syn.subst σ A) (Syn.subst σ N) := by simp [bound]

theorem radius_positive (A : PTm n) : Γ ⊢[PRAAx] le one (radius A) :=
  le_of_eq_add (d := A+one) (by unfold radius; ipra_ring)

theorem geometric_zero (A : PTm n) : Γ ⊢[PRAAx] geometric A zero ≐ zero := sum_zero _ _

theorem geometric_succ (A N : PTm n) : Γ ⊢[PRAAx]
    geometric A (succ N) ≐ geometric A N+pw (radius A) N := by
  simpa only [geometric,inst2_gB] using sum_succ' (Γ := Γ) gB N (radius A)

theorem geometric_positive (A N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (geometric A N) := by
  have h := term_le_sum gB (i := zero) (x := radius A) hN
  rw [inst2_gB] at h
  exact le_congr (pw_zero _) (.eqRefl _) h

theorem exact_gap (A N : PTm n) : Γ ⊢[PRAAx]
    pw (radius A) N ≐ numerator A N+geometric A N := by
  have pred : Γ ⊢[PRAAx] PTm.monus (radius A) one ≐ A+one :=
    (congrMonus (show Γ ⊢[PRAAx] radius A ≐ succ (A+one) from by unfold radius; ipra_ring) (.eqRefl one)).eqTrans
      ((succ_monus_succ (A+one) zero).eqTrans (monus_zero _))
  exact (geom_sum (radius_positive A) N).eqTrans
    ((congrAdd (congrMul pred (.eqRefl _)) (.eqRefl _)).eqTrans (by unfold numerator geometric; ipra_ring))

theorem strict_budget (A N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    lt (numerator A N) (pw (radius A) N) :=
  le_congr (by ipra_ring) (exact_gap A N).eqSymm
    (add_le_add₂ (le_refl (numerator A N)) (geometric_positive A N hN))

theorem budget_below_one (A N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    (rationalLE GaussianRationalL1.oneCode (bound A N) ⟶ .bot) := by
  refine .impI ?_
  have h := GaussianRationalMetric.comparison_to_cleared
    (Γ := rationalLE GaussianRationalL1.oneCode (bound A N) :: Γ)
    GaussianRationalL1.oneCode (bound A N) one (numerator A N) one (pw (radius A) N)
    (normalize_preserves_value _ _ (le_refl _))
    (normalize_preserves_value _ _ (GaussianPolynomialPerturbation.power_positive _ _ (radius_positive A))) Prf.hyp0
  have e : rationalLE GaussianRationalL1.oneCode (bound A N) :: Γ ⊢[PRAAx]
      le (pw (radius A) N) (numerator A N) := le_congr (by ipra_ring) (by ipra_ring) h
  exact lt_irrefl _ _ (lt_of_lt_of_le (strict_budget A N hN.wk) e)

theorem geometric_radius_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ (lt (numerator (var 0) (var 1)) (pw (radius (var 0)) (var 1)) ⋏
      (rationalLE GaussianRationalL1.oneCode (bound (var 0) (var 1)) ⟶ .bot))) :=
  closeUniv 2 (.impI (.andI (strict_budget _ _ Prf.hyp0) (budget_below_one _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRadiusBudget
