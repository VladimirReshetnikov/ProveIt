import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianDescentClockArithmetic
import IPRADerivations.Analysis.Polynomials.RootFinding.Deflation.FactorTransport.GaussianFactorBudget

/-!
# Actual finite precision schedule for collision-tolerant root support

Source04 chooses C=N R^(N-1), b with 2^b≥4C, and E(t)=N(t+2)+b.
Here b is the actual least bounded binary-length search, with a proved
successful endpoint. The exact root-stability budget is derived from the
computed b, not supplied as a precision or search-success premise.
All degrees, radii and precision indices remain internal numerical inputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootSchedule

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def four : PTm n := two*two
def binaryBody : PTm 2 := monus (var 1) (pw two (var 0))
def binaryLength (x : PTm n) : PTm n := Search.mu binaryBody (succ x) x
def coefficientConstant (N R : PTm n) : PTm n := N*pw R (pred N)
def shiftIndex (N R : PTm n) : PTm n := binaryLength (four*coefficientConstant N R)
def precision (N R t : PTm n) : PTm n := N*(t+two)+shiftIndex N R
def toleranceDenominator (N R t : PTm n) : PTm n := pw two (precision N R t)

ipra_subst four
ipra_subst binaryLength
ipra_subst coefficientConstant
ipra_subst shiftIndex
ipra_subst precision
ipra_subst toleranceDenominator

theorem binary_body_at (i x : PTm n) : inst2 binaryBody i x = monus x (pw two i) := by simp [binaryBody,inst2]

/-- The bounded search always succeeds, including x=0. -/
theorem binary_length_correct (x : PTm n) : Γ ⊢[PRAAx]
    le x (pw two (binaryLength x)) ⋏ le (binaryLength x) x := by
  have candidate : Γ ⊢[PRAAx] inst2 binaryBody x x ≐ zero := by
    rw [binary_body_at]
    exact le_trans (le_succ_self x) (RationalClosure.succ_le_two_pow x)
  have found := Search.search_found (f := binaryBody) (N := succ x) candidate (le_refl (succ x))
  exact .andI (by simpa only [binary_body_at,binaryLength,le] using Prf.andE₁ (Prf.andE₂ found)) (Prf.andE₂ (Prf.andE₂ found))

theorem binary_length_minimal (x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (binaryLength x)) :
    Γ ⊢[PRAAx] neg (le x (pw two i)) := by
  simpa only [binary_body_at,le] using Search.search_minimal (f := binaryBody) (N := succ x) hi

theorem shift_budget (N R : PTm n) : Γ ⊢[PRAAx] le (four*coefficientConstant N R) (pw two (shiftIndex N R)) :=
  Prf.andE₁ (binary_length_correct _)

theorem precision_lower (N R t : PTm n) : Γ ⊢[PRAAx] le (N*(t+two)) (precision N R t) := le_add_right _ _

theorem precision_monotone (N R t u : PTm n) (htu : Γ ⊢[PRAAx] le t u) :
    Γ ⊢[PRAAx] le (precision N R t) (precision N R u) :=
  add_le_add₂ (le_mul_mono (le_refl N) (add_le_add₂ htu (le_refl two))) (le_refl _)

theorem precision_ge_index (N R t : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le t (precision N R t) :=
  le_trans (le_add_right t two) (le_trans
    (le_congr (one_mul _) (.eqRefl _) (le_mul_mono hN (le_refl (t+two)))) (precision_lower N R t))

theorem precision_succ (N R t : PTm n) : Γ ⊢[PRAAx] precision N R (succ t) ≐ precision N R t+N := by
  unfold precision
  ipra_ring

theorem tolerance_positive (N R t : PTm n) : Γ ⊢[PRAAx] le one (toleranceDenominator N R t) :=
  GaussianFactorBudget.power_positive _ _ (le_succ_self one)

theorem tolerance_monotone (N R t u : PTm n) (htu : Γ ⊢[PRAAx] le t u) :
    Γ ⊢[PRAAx] le (toleranceDenominator N R t) (toleranceDenominator N R u) :=
  GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (precision_monotone N R t u htu)

/-- The exact power identity used by the source Hausdorff budget. -/
theorem tolerance_split (N R t : PTm n) : Γ ⊢[PRAAx]
    toleranceDenominator N R t ≐ pw (pw two (t+two)) N*pw two (shiftIndex N R) := by
  have exponent : Γ ⊢[PRAAx] N*(t+two) ≐ (t+two)*N := mul_comm _ _
  exact (pw_add two (N*(t+two)) (shiftIndex N R)).eqTrans
    (congrMul ((congrAp2 powF exponent (.eqRefl two)).eqTrans
      (GaussianDescentClockArithmetic.power_composition two (t+two) N).eqSymm) (.eqRefl _))

/-- C·4·2^(-E(t))≤(2^(-t-2))^N, after positive denominator
clearing, with the actual computed binary-length shift. -/
theorem root_stability_budget (N R t : PTm n) : Γ ⊢[PRAAx]
    le (pw (pw two (t+two)) N*(four*coefficientConstant N R)) (toleranceDenominator N R t) :=
  le_congr (.eqRefl _) (tolerance_split N R t).eqSymm
    (le_mul_mono (le_refl _) (shift_budget N R))

def output (N R t : PTm n) : PTm n := pairT (shiftIndex N R) (pairT (precision N R t) (toleranceDenominator N R t))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
ipra_subst output
theorem schedule_program (N R t : PTm n) : Γ ⊢[PRAAx] ap3 outputF N R t ≐ output N R t := by
  simpa [outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![N,R,t]

theorem binary_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le (var 0) (pw two (binaryLength (var 0)))) ⋏
      (le (binaryLength (var 0)) (var 0) ⋏
        (lt (var 1) (binaryLength (var 0)) ⟶ neg (le (var 0) (pw two (var 1)))))) :=
  closeUniv 2 (.andI (Prf.andE₁ (binary_length_correct _))
    (.andI (Prf.andE₂ (binary_length_correct _)) (.impI (binary_length_minimal _ _ Prf.hyp0))))

theorem root_support_schedule_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (four*coefficientConstant (var 0) (var 1)) (pw two (shiftIndex (var 0) (var 1))) ⋏
      (le one (toleranceDenominator (var 0) (var 1) (var 2)) ⋏
        le (pw (pw two (var 2+two)) (var 0)*(four*coefficientConstant (var 0) (var 1)))
          (toleranceDenominator (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (shift_budget _ _) (.andI (tolerance_positive _ _ _) (root_stability_budget _ _ _)))

theorem root_schedule_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 outputF (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (schedule_program _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRootSchedule
