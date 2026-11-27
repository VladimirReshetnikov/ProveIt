import IPRADerivations.Analysis.Logarithm.FiniteSeries.Composition.GaussianFiniteLogarithmGeometricTail
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianDescentClockArithmetic

/-!
# An actual dyadic cutoff for the original finite C4 composition

The numerical cutoff is10(p+8). The existing finite block-decay theorem
at M=10 proves the original geometric budget is at most2^(-p-4).
The conclusion concerns the actual stored finite composition on the
original Euclidean half disk; no represented exponential law is a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmDyadicTail

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (evaluate)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianFiniteLogarithmPolynomial (composition)
open GaussianFiniteLogarithmCompositionTail (linearValue)
open GaussianFiniteLogarithmGeometricTail (numerator denominator residual)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def clock (p : PTm n) : PTm n := num 10*(p+num 8)
def precisionDenominator (p : PTm n) : PTm n := pw two (p+num 4)
ipra_subst clock
ipra_subst precisionDenominator

theorem clock_positive (p : PTm n) : Γ ⊢[PRAAx] le one (clock p) :=
  le_of_eq_add (d := num 10*p+num 79) (by unfold clock; ipra_ring)

theorem clock_monotone (p q : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] le (clock p) (clock q) :=
  le_mul_mono (le_refl _) (add_le_add_right (num 8) h)

theorem precision_positive (p : PTm n) : Γ ⊢[PRAAx] le one (precisionDenominator p) :=
  GaussianFactorBudget.power_positive _ _ (le_succ_self one)

theorem two_four : Γ ⊢[PRAAx] pw two (num 4 : PTm n) ≐ num 16 := by
  have square : Γ ⊢[PRAAx] pw two two ≐ num 4 :=
    (pw_succ two one).eqTrans ((congrMul (pw_one two) (.eqRefl _)).eqTrans (by ipra_ring))
  exact (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] (num 4 : PTm n) ≐ two+two) (.eqRefl _)).eqTrans
    ((pw_add two two two).eqTrans ((congrMul square square).eqTrans (by ipra_ring)))

theorem precision_shift (p : PTm n) : Γ ⊢[PRAAx]
    pw two (p+num 8) ≐ precisionDenominator p*num 16 :=
  (congrAp2 powF (by ipra_ring) (.eqRefl _)).eqTrans
    ((pw_add two (p+num 4) (num 4)).eqTrans (congrMul (.eqRefl _) two_four))

/-- Exact cross-multiplied radius inequality, obtained from the existing
dyadic decay of9/10. All exponents are numerical object-language inputs. -/
theorem clock_budget (p : PTm n) : Γ ⊢[PRAAx]
    le (numerator (clock p)*precisionDenominator p) (denominator (clock p)) := by
  have h10 : Γ ⊢[PRAAx] le one (num 10 : PTm n) := le_of_eq_add (d := num 9) (by ipra_ring)
  have dec := GaussianDescentClockArithmetic.dyadic_decay (Γ := Γ) (num 10) (p+num 8) h10
  have pred10 : Γ ⊢[PRAAx] pred (num 10 : PTm n) ≐ num 9 := pred_succ (num 9)
  have first : Γ ⊢[PRAAx] le
      (numerator (clock p)*precisionDenominator p)
      (num 10*(pw two (p+num 8)*pw (num 9) (clock p))) := by
    refine le_of_eq_add (d := num 61*precisionDenominator p*pw (num 9) (clock p)) ?_
    have pow9 := natEq (pw_succ (Γ := Γ) (num 9) (clock p))
    have dyad := natEq (precision_shift (Γ := Γ) p)
    apply deriveNat; unfold numerator; ipra_simps; rw [pow9,dyad]; ring
  have second : Γ ⊢[PRAAx] le
      (num 10*(pw two (p+num 8)*pw (num 9) (clock p)))
      (num 10*pw (num 10) (clock p)) := by
    exact le_mul_mono (le_refl _) (le_congr
      (congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) pred10)) (.eqRefl _) dec)
  exact le_trans first (le_congr (.eqRefl _)
    ((mul_comm _ _).eqTrans (pw_succ _ _).eqSymm) second)

/-- The SAME original finite composition, at any cutoffs beyond the
computed clock, differs from1+w by at most2^(-p-4). -/
theorem composition_error (d K p w : PTm n)
    (hd : Γ ⊢[PRAAx] le (clock p) d) (hK : Γ ⊢[PRAAx] le (clock p) K)
    (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (composition d K) w) (linearValue w) one (precisionDenominator p) :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianFiniteLogarithmGeometricTail.denominator_positive _) (precision_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (clock_budget p))
    (GaussianFiniteLogarithmGeometricTail.composition_error d K (clock p) w (clock_positive p) hd hK hw)

/-! Fixed-arity producers retain the actual composition and the exact
clock/residual/dyadic denominator, with no supplied approximation law. -/
def clockF : PR 1 := PTm.toPR (clock (var 0))
def output (d K p w : PTm n) : PTm n := pairT (composition d K)
  (pairT (clock p) (pairT (residual d K w) (precisionDenominator p)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (d K p w : PTm n) : PTm n := PTm.app outputF ![d,K,p,w]
ipra_subst output
ipra_subst run

theorem clock_at (p : PTm n) : Γ ⊢[PRAAx] ap1 clockF p ≐ clock p := by
  simpa [clockF,ap1] using toPR_eq (Γ := Γ) (clock (var 0) : PTm 1) ![p]
theorem clock_zero : Γ ⊢[PRAAx] clock (zero : PTm n) ≐ num 80 := by unfold clock; ipra_ring
theorem program_at (d K p w : PTm n) : Γ ⊢[PRAAx] run d K p w ≐ output d K p w := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![d,K,p,w]
theorem returned_composition (d K p w : PTm n) : Γ ⊢[PRAAx] fstT (run d K p w) ≐ composition d K :=
  (program_at _ _ _ _).fstE
theorem returned_tail (d K p w : PTm n) : Γ ⊢[PRAAx] sndT (run d K p w) ≐
    pairT (clock p) (pairT (residual d K w) (precisionDenominator p)) :=
  (program_at _ _ _ _).sndE
theorem returned_clock (d K p w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d K p w)) ≐ clock p :=
  (returned_tail _ _ _ _).fstE
theorem returned_pair (d K p w : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d K p w)) ≐
    pairT (residual d K w) (precisionDenominator p) :=
  (returned_tail _ _ _ _).sndE
theorem returned_residual (d K p w : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run d K p w))) ≐ residual d K w :=
  (returned_pair _ _ _ _).fstE
theorem returned_denominator (d K p w : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run d K p w))) ≐ precisionDenominator p :=
  (returned_pair _ _ _ _).sndE
theorem returned_bound (d K p w : PTm n)
    (hd : Γ ⊢[PRAAx] le (clock p) d) (hK : Γ ⊢[PRAAx] le (clock p) K)
    (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    bounded (fstT (sndT (sndT (run d K p w)))) one (sndT (sndT (sndT (run d K p w)))) :=
  GaussianRationalReciprocal.bound_congr (returned_residual _ _ _ _).eqSymm (.eqRefl _)
    (returned_denominator _ _ _ _).eqSymm (composition_error d K p w hd hK hw)

theorem actual_dyadic_clock_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (clock (var 0))) := closeUniv 1 (clock_positive _)
theorem actual_dyadic_clock_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 0) (var 1) ⟶ le (clock (var 0)) (clock (var 1))) :=
  closeUniv 2 (.impI (clock_monotone _ _ Prf.hyp0))
theorem actual_geometric_dyadic_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (numerator (clock (var 0))*precisionDenominator (var 0)) (denominator (clock (var 0)))) :=
  closeUniv 1 (clock_budget _)
theorem original_half_disk_dyadic_composition_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (clock (var 2)) (var 0) ⟶ le (clock (var 2)) (var 1) ⟶ bounded (var 3) one two ⟶
      distanceBounded (evaluate (composition (var 0) (var 1)) (var 3)) (linearValue (var 3)) one (precisionDenominator (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (composition_error _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_dyadic_clock_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 clockF (var 0) ≐ clock (var 0)) := closeUniv 1 (clock_at _)
theorem actual_dyadic_tail_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem returned_dyadic_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (clock (var 2)) (var 0) ⟶ le (clock (var 2)) (var 1) ⟶ bounded (var 3) one two ⟶
      bounded (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) one
        (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 4 (.impI (.impI (.impI (returned_bound _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_zero_precision_clock_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    clock (zero : PTm 0) ≐ num 80 := clock_zero

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmDyadicTail
