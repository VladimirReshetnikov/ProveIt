import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSchedule
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantSyntax
import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusArithmetic

/-!
# Computed dyadic counts for the rational half-angle direction algorithm

The existing bounded binaryLength has the non-strict bound x<=2^bl(x).
Every schedule below uses exactly that bound. All counts, exponents,
quotients and remainders are actual primitive recursive numerical data.
The clock budgets are proved from these definitions, not supplied as
accuracy or successful-loop assumptions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalDirectionClock

open_ipra
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax (four)
open LeanProofs.IPRA.Analysis.GaussianRootSchedule (binaryLength)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sixteen : PTm n := unit four
def eight : PTm n := unit (succ two)
def ten : PTm n := two*(four+one)
def logarithm (k q : PTm n) : PTm n := binaryLength (sixteen*k*q)
def steps (k q : PTm n) : PTm n := two*logarithm k q+four
def period (k q : PTm n) : PTm n := unit (steps k q)
def localIndex (k q : PTm n) : PTm n := steps k q+binaryLength (sixteen*q)+four
def precision (k q : PTm n) : PTm n := two*localIndex k q+ten
def height (k q : PTm n) : PTm n := unit (precision k q)
def roundedPower (k q : PTm n) : PTm n := quo (period k q) k
def leftover (k q : PTm n) : PTm n := rem (period k q) k

ipra_subst sixteen
ipra_subst eight
ipra_subst ten
ipra_subst logarithm
ipra_subst steps
ipra_subst period
ipra_subst localIndex
ipra_subst precision
ipra_subst height
ipra_subst roundedPower
ipra_subst leftover

theorem period_positive (k q : PTm n) : Γ ⊢[PRAAx] le one (period k q) := unit_positive _
theorem height_positive (k q : PTm n) : Γ ⊢[PRAAx] le one (height k q) := unit_positive _
theorem sixteen_positive : Γ ⊢[PRAAx] le one (sixteen : PTm n) := unit_positive _

theorem eight_le_sixteen : Γ ⊢[PRAAx] le (eight : PTm n) sixteen :=
  GaussianBalancedRadiusArithmetic.unit_monotone _ _
    (le_of_eq_add (d := one) (by unfold four; ipra_ring))

theorem period_factor (k q : PTm n) : Γ ⊢[PRAAx]
    period k q ≐ sixteen*(unit (logarithm k q)*unit (logarithm k q)) :=
  (pw_add two (two*logarithm k q) four).eqTrans
    ((congrMul (GaussianBalancedRadiusArithmetic.unit_square (logarithm k q)).eqSymm (.eqRefl _)).eqTrans
      (by unfold sixteen unit; ipra_ring))

theorem period_budget (k q : PTm n) : Γ ⊢[PRAAx]
    le (sixteen*(sixteen*k*q)*(sixteen*k*q)) (period k q) := by
  have bits := Prf.andE₁ (GaussianRootSchedule.binary_length_correct (Γ := Γ) (sixteen*k*q))
  have associated : Γ ⊢[PRAAx] le (sixteen*(sixteen*k*q)*(sixteen*k*q))
      (sixteen*(unit (logarithm k q)*unit (logarithm k q))) :=
    le_congr (by ipra_ring) (by unfold logarithm unit; ipra_ring)
      (mul_le_mul_right sixteen (le_mul_mono bits bits))
  exact le_congr (.eqRefl _) (period_factor k q).eqSymm associated

/-- This is the squared error budget for the rounded exponent. -/
theorem root_distance_budget (k q : PTm n) : Γ ⊢[PRAAx]
    le (eight*(sixteen*k*q)*(sixteen*k*q)) (period k q) :=
  le_trans (le_congr (by ipra_ring) (by ipra_ring)
    (mul_le_mul_right ((sixteen*k*q)*(sixteen*k*q)) (eight_le_sixteen (Γ := Γ)))) (period_budget k q)

theorem local_factor (k q : PTm n) : Γ ⊢[PRAAx]
    unit (localIndex k q) ≐ period k q*unit (binaryLength (sixteen*q))*sixteen :=
  (pw_add two (steps k q+binaryLength (sixteen*q)) four).eqTrans
    (congrMul (pw_add two (steps k q) (binaryLength (sixteen*q))) (.eqRefl _))

/-- The sum of powered local errors is at most 1/(256q). -/
theorem local_error_budget (k q : PTm n) : Γ ⊢[PRAAx]
    le (sixteen*sixteen*q*period k q) (unit (localIndex k q)) := by
  have bits := Prf.andE₁ (GaussianRootSchedule.binary_length_correct (Γ := Γ) (sixteen*q))
  have associated : Γ ⊢[PRAAx] le (sixteen*sixteen*q*period k q)
      (period k q*unit (binaryLength (sixteen*q))*sixteen) :=
    le_congr (by ipra_ring) (by unfold unit; ipra_ring) (mul_le_mul_right (period k q*sixteen) bits)
  exact le_congr (.eqRefl _) (local_factor k q).eqSymm associated

theorem index_below_precision (k q : PTm n) : Γ ⊢[PRAAx] le (localIndex k q) (precision k q) :=
  le_of_eq_add (d := localIndex k q+ten) (by unfold precision; ipra_ring)

theorem period_below_height (k q : PTm n) : Γ ⊢[PRAAx] le (period k q) (height k q) :=
  GaussianBalancedRadiusArithmetic.unit_monotone _ _ (le_trans
    (le_trans (le_add_right (steps k q) (binaryLength (sixteen*q))) (le_add_right _ four))
    (index_below_precision k q))

theorem height_large (k q : PTm n) : Γ ⊢[PRAAx] le (unit (four+two)) (height k q) :=
  GaussianBalancedRadiusArithmetic.unit_monotone _ _
    (le_of_eq_add (d := two*localIndex k q+four) (by unfold precision ten four; ipra_ring))

theorem height_square (k q : PTm n) : Γ ⊢[PRAAx]
    height k q ≐ unit (localIndex k q+(four+one))*unit (localIndex k q+(four+one)) :=
  (congrAp2 powF (by unfold precision ten; ipra_ring) (.eqRefl two)).eqTrans
    (GaussianBalancedRadiusArithmetic.unit_square (localIndex k q+(four+one))).eqSymm

theorem index_below_height (k q : PTm n) : Γ ⊢[PRAAx]
    le (unit (localIndex k q)) (height k q) :=
  GaussianBalancedRadiusArithmetic.unit_monotone _ _ (index_below_precision k q)

/-- The computed grid also controls the initializer's rational error. -/
theorem initialization_budget (k q : PTm n) : Γ ⊢[PRAAx]
    le (two*sixteen*q) (height k q) := by
  have small : Γ ⊢[PRAAx] le two (sixteen : PTm n) :=
    le_congr (pw_one two) (.eqRefl _) (GaussianBalancedRadiusArithmetic.unit_monotone one four
      (le_of_eq_add (d := one+two) (by unfold four; ipra_ring)))
  have first : Γ ⊢[PRAAx] le (two*sixteen*q) (sixteen*sixteen*q) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (sixteen*q) small)
  have second : Γ ⊢[PRAAx] le (sixteen*sixteen*q) (sixteen*sixteen*q*period k q) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (sixteen*sixteen*q)) (period_positive k q))
  exact le_trans first (le_trans second (le_trans (local_error_budget k q) (index_below_height k q)))

/-- A squared initializer error 4/H is at most 1/(16q)^2. -/
theorem initialization_squared_budget (k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    le ((two*sixteen*q)*(two*sixteen*q)) (height k q) := by
  have coefficient : Γ ⊢[PRAAx] le four (sixteen : PTm n) :=
    le_congr (pw_succ two one |>.eqTrans (congrMul (pw_one two) (.eqRefl _))) (.eqRefl _)
      (GaussianBalancedRadiusArithmetic.unit_monotone two four
        (le_of_eq_add (d := two) (by unfold four; ipra_ring)))
  have magnitude : Γ ⊢[PRAAx] le (sixteen*q) (sixteen*k*q) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (sixteen*q) hk)
  have budget : Γ ⊢[PRAAx] le ((two*sixteen*q)*(two*sixteen*q))
      (sixteen*(sixteen*k*q)*(sixteen*k*q)) :=
    le_congr (by unfold four; ipra_ring) (by ipra_ring)
      (le_mul_mono coefficient (le_mul_mono magnitude magnitude))
  exact le_trans budget (le_trans (period_budget k q) (period_below_height k q))

theorem division_spec (k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    period k q ≐ k*roundedPower k q+leftover k q ⋏ lt (leftover k q) k :=
  div_mod_at (x := period k q) (RationalIntegerNormalization.positive_form hk)

theorem rounded_below_period (k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    le (k*roundedPower k q) (period k q) :=
  le_congr (.eqRefl _) (Prf.andE₁ (division_spec k q hk)).eqSymm (le_add_right _ _)

theorem remainder_identity (k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    monus (period k q) (k*roundedPower k q) ≐ leftover k q :=
  (congrMonus (Prf.andE₁ (division_spec k q hk)) (.eqRefl _)).eqTrans (add_monus' _ _)

theorem remainder_bounded (k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    lt (monus (period k q) (k*roundedPower k q)) k :=
  lt_congr (remainder_identity k q hk).eqSymm (.eqRefl _) (Prf.andE₂ (division_spec k q hk))

def output (k q : PTm n) : PTm n := pairT (steps k q) (pairT (period k q)
  (pairT (localIndex k q) (pairT (precision k q) (pairT (height k q)
    (pairT (roundedPower k q) (leftover k q))))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (k q : PTm n) : PTm n := ap2 outputF k q

ipra_subst output
ipra_subst run

theorem program_at (k q : PTm n) : Γ ⊢[PRAAx] run k q ≐ output k q := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![k,q]

theorem returned_steps (k q : PTm n) : Γ ⊢[PRAAx] fstT (run k q) ≐ steps k q :=
  (program_at k q).fstE

theorem returned_period (k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run k q)) ≐ period k q :=
  (program_at k q).sndE.fstE

theorem returned_localIndex (k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run k q))) ≐ localIndex k q :=
  (program_at k q).sndE.sndE.fstE

theorem returned_precision (k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run k q)))) ≐ precision k q :=
  (program_at k q).sndE.sndE.sndE.fstE

theorem returned_height (k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run k q))))) ≐ height k q :=
  (program_at k q).sndE.sndE.sndE.sndE.fstE

theorem returned_roundedPower (k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (sndT (run k q)))))) ≐ roundedPower k q :=
  (program_at k q).sndE.sndE.sndE.sndE.sndE.fstE

theorem returned_leftover (k q : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (sndT (run k q)))))) ≐ leftover k q :=
  (program_at k q).sndE.sndE.sndE.sndE.sndE.sndE

theorem dyadic_direction_budgets_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (sixteen*(sixteen*var 0*var 1)*(sixteen*var 0*var 1)) (period (var 0) (var 1)) ⋏
      (le (sixteen*sixteen*var 1*period (var 0) (var 1)) (unit (localIndex (var 0) (var 1))) ⋏
        (le (two*sixteen*var 1) (height (var 0) (var 1)) ⋏
          height (var 0) (var 1) ≐ unit (localIndex (var 0) (var 1)+(four+one))*
            unit (localIndex (var 0) (var 1)+(four+one))))) :=
  closeUniv 2 (.andI (period_budget _ _) (.andI (local_error_budget _ _)
    (.andI (initialization_budget _ _) (height_square _ _))))

theorem rounded_direction_clock_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶
      (period (var 0) (var 1) ≐ var 0*roundedPower (var 0) (var 1)+leftover (var 0) (var 1) ⋏
        (lt (leftover (var 0) (var 1)) (var 0) ⋏
          lt (monus (period (var 0) (var 1)) (var 0*roundedPower (var 0) (var 1))) (var 0)))) :=
  closeUniv 2 (.impI (.andI (Prf.andE₁ (division_spec _ _ Prf.hyp0))
    (.andI (Prf.andE₂ (division_spec _ _ Prf.hyp0)) (remainder_bounded _ _ Prf.hyp0))))

theorem direction_clock_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalDirectionClock
