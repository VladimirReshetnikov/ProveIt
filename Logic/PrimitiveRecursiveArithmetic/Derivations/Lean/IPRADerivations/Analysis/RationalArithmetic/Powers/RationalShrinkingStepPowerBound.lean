import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowerOrder

/-!
# Exact rational power budget for a shrinking step

The local squared comparison is cleared using the original positive
denominators. The actual Q bound is raised to an internal even exponent,
the exponent is decreased on [0,1], and the constant is enlarged above
one. Positive-degree power reflection then gives the original radius
comparison. Only positive denominator powers are cancelled; the radius,
Q and the contraction numerator may be zero.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalShrinkingStepPowerBound

open_ipra
open LeanProofs.IPRA.Analysis.RationalNonnegativePowerOrder
open LeanProofs.IPRA.Analysis.RationalNonnegativePowers (power denominator_positive)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (positive_product power_composition)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias natural_square := Common.pw_two

/-- This is exactly the local cleared comparison with C=EWM and D=FL. -/
def combinedBudget (a b u v C D q s j i : PTm n) : Fm PTm n :=
  le (D*D*pw (a*v) (two*i)*pw s (two*j))
    (C*C*pw q (two*j)*pw (b*u) (two*i))

ipra_subst combinedBudget

theorem eliminate_q (X Y C D q s R S m ell N : PTm n)
    (hs : Γ ⊢[PRAAx] le one s) (hQ : Γ ⊢[PRAAx] le (q*pw S N) (pw R N*s))
    (hLocal : Γ ⊢[PRAAx] le (D*D*pw X m*pw s ell) (C*C*pw q ell*pw Y m)) : Γ ⊢[PRAAx]
    le (D*D*pw X m*pw S (N*ell)) (C*C*pw R (N*ell)*pw Y m) := by
  have raised : Γ ⊢[PRAAx] le (pw q ell*pw S (N*ell)) (pw R (N*ell)*pw s ell) :=
    le_congr ((pw_mul_base q (pw S N) ell).eqTrans (congrMul (.eqRefl _) (power_composition S N ell)))
      ((pw_mul_base (pw R N) s ell).eqTrans (congrMul (power_composition R N ell) (.eqRefl _)))
      (pw_le_pw ell hQ)
  have first := mul_le_mul_right (pw S (N*ell)) hLocal
  have second := mul_le_mul_right (C*C*pw Y m) raised
  have joined : Γ ⊢[PRAAx]
      le (pw s ell*(D*D*pw X m*pw S (N*ell))) (pw s ell*(C*C*pw R (N*ell)*pw Y m)) :=
    le_trans (b := C*C*pw q ell*pw Y m*pw S (N*ell)) (le_congr (by ipra_ring) (.eqRefl _) first)
      (le_congr (by ipra_ring) (by ipra_ring) second)
  exact RationalValueBounds.positive_cancel (denominator_positive s ell hs) joined

theorem decrease_decay_exponent (X Y C D R S m ell i N : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (hRS : Γ ⊢[PRAAx] le R S) (hiN : Γ ⊢[PRAAx] le i N)
    (h : Γ ⊢[PRAAx] le (D*D*pw X m*pw S (N*ell)) (C*C*pw R (N*ell)*pw Y m)) : Γ ⊢[PRAAx]
    le (D*D*pw X m*pw S (i*ell)) (C*C*pw R (i*ell)*pw Y m) := by
  have cross := exponent_cross_antitone R S (i*ell) (N*ell) hRS (mul_le_mul_right ell hiN)
  have first := mul_le_mul_right (pw S (i*ell)) h
  have second := mul_le_mul_right (C*C*pw Y m) cross
  have joined : Γ ⊢[PRAAx]
      le (pw S (N*ell)*(D*D*pw X m*pw S (i*ell))) (pw S (N*ell)*(C*C*pw R (i*ell)*pw Y m)) :=
    le_trans (b := C*C*pw R (N*ell)*pw Y m*pw S (i*ell)) (le_congr (by ipra_ring) (.eqRefl _) first)
      (le_congr (by ipra_ring) (by ipra_ring) second)
  exact RationalValueBounds.positive_cancel (denominator_positive S (N*ell) hS) joined

theorem absorb_constant (X Y C D m : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hDC : Γ ⊢[PRAAx] le D C) (hm : Γ ⊢[PRAAx] le two m)
    (h : Γ ⊢[PRAAx] le (D*D*pw X m) (C*C*pw Y m)) : Γ ⊢[PRAAx] le (D*X) (C*Y) := by
  have cross : Γ ⊢[PRAAx] le (C*C*pw D m) (D*D*pw C m) :=
    le_congr (congrMul (natural_square C) (.eqRefl _)) (congrMul (natural_square D) (.eqRefl _))
      (exponent_cross_antitone D C two m hDC hm)
  have first := mul_le_mul_right (pw D m) h
  have second := mul_le_mul_right (pw Y m) cross
  have joined : Γ ⊢[PRAAx] le (D*D*(pw D m*pw X m)) (D*D*(pw C m*pw Y m)) :=
    le_trans (b := C*C*pw Y m*pw D m) (le_congr (by ipra_ring) (.eqRefl _) first)
      (le_congr (by ipra_ring) (by ipra_ring) second)
  have powers : Γ ⊢[PRAAx] le (pw (D*X) m) (pw (C*Y) m) :=
    le_congr (pw_mul_base D X m).eqSymm (pw_mul_base C Y m).eqSymm
      (RationalValueBounds.positive_cancel (positive_product D D hD hD) joined)
  exact natural_power_order_reflect _ _ _ (le_trans (le_succ_self one) hm) powers

def bound (u v C D R S j : PTm n) : PTm n :=
  fraction (u*C*pw R j) (v*D*pw S j)

ipra_subst bound

theorem shrinking_step_bound (a b u v C D q s R S j N i : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hv : Γ ⊢[PRAAx] le one v) (hD : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] le one s) (hS : Γ ⊢[PRAAx] le one S)
    (hDC : Γ ⊢[PRAAx] le D C) (hRS : Γ ⊢[PRAAx] le R S)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N)
    (hQ : Γ ⊢[PRAAx] rationalLE (fraction q s) (power R S N))
    (hLocal : Γ ⊢[PRAAx] combinedBudget a b u v C D q s j i) : Γ ⊢[PRAAx]
    rationalLE (fraction a b) (bound u v C D R S j) := by
  have clearedQ : Γ ⊢[PRAAx] le (q*pw S N) (pw R N*s) :=
    le_congr (mul_comm _ _) (.eqRefl _)
      (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
        (fraction_represents q s hs) (RationalNonnegativePowers.power_represents R S N hS) hQ)
  have reduced := decrease_decay_exponent (a*v) (b*u) C D R S (two*i) (two*j) i N hS hRS hiN
    (eliminate_q (a*v) (b*u) C D q s R S (two*i) (two*j) N hs clearedQ hLocal)
  have radiusPowers : Γ ⊢[PRAAx]
      le (D*D*pw ((a*v)*pw S j) (two*i)) (C*C*pw ((b*u)*pw R j) (two*i)) := by
    have ds := natEq (power_composition (Γ := Γ) S j (two*i))
    have rs := natEq (power_composition (Γ := Γ) R j (two*i))
    have sl := natEq (pw_mul_base (Γ := Γ) (a*v) (pw S j) (two*i))
    have rl := natEq (pw_mul_base (Γ := Γ) (b*u) (pw R j) (two*i))
    have exp : Γ ⊢[PRAAx] i*(two*j) ≐ j*(two*i) := by ipra_ring
    apply le_congr (a' := D*D*pw ((a*v)*pw S j) (two*i))
      (b' := C*C*pw ((b*u)*pw R j) (two*i)) ?_ ?_ reduced
    · apply deriveNat
      ipra_simps
      rw [sl,ds,natEq (congrAp2 powF exp (.eqRefl S))]
      ring
    · apply deriveNat
      ipra_simps
      rw [rl,rs,natEq (congrAp2 powF exp (.eqRefl R))]
      ring
  have hi2 : Γ ⊢[PRAAx] le two (two*i) := le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two hi)
  have small := absorb_constant _ _ C D (two*i) hD hDC hi2 radiusPowers
  exact fraction_order _ _ _ _ hb
    (positive_product _ _ (positive_product v D hv hD) (denominator_positive S j hS))
    (le_congr (by ipra_ring) (by ipra_ring) small)

theorem source_bound (a b u v L M E F q s R S j N i W : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hv : Γ ⊢[PRAAx] le one v)
    (hL : Γ ⊢[PRAAx] le one L) (hF : Γ ⊢[PRAAx] le one F)
    (hs : Γ ⊢[PRAAx] le one s) (hS : Γ ⊢[PRAAx] le one S)
    (hC : Γ ⊢[PRAAx] le (F*L) (E*W*M)) (hRS : Γ ⊢[PRAAx] le R S)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N)
    (hQ : Γ ⊢[PRAAx] rationalLE (fraction q s) (power R S N))
    (hLocal : Γ ⊢[PRAAx] combinedBudget a b u v (E*W*M) (F*L) q s j i) : Γ ⊢[PRAAx]
    rationalLE (fraction a b) (bound u v (E*W*M) (F*L) R S j) :=
  shrinking_step_bound a b u v (E*W*M) (F*L) q s R S j N i
    hb hv (positive_product F L hF hL) hs hS hC hRS hi hiN hQ hLocal

def conditions (a b u v C D q s R S j N i : PTm n) : Fm PTm n :=
  (le one b ⋏ (le one v ⋏ (le one D ⋏ (le one s ⋏ le one S)))) ⋏
    ((le D C ⋏ (le R S ⋏ (le one i ⋏ le i N))) ⋏
      (rationalLE (fraction q s) (power R S N) ⋏ combinedBudget a b u v C D q s j i))

ipra_subst conditions

theorem shrinking_step_of_conditions (a b u v C D q s R S j N i : PTm n)
    (h : Γ ⊢[PRAAx] conditions a b u v C D q s R S j N i) : Γ ⊢[PRAAx]
    rationalLE (fraction a b) (bound u v C D R S j) := by
  have den := Prf.andE₁ h
  have ord := Prf.andE₁ (Prf.andE₂ h)
  have cmp := Prf.andE₂ (Prf.andE₂ h)
  exact shrinking_step_bound _ _ _ _ _ _ _ _ _ _ _ _ _
    (Prf.andE₁ den) (Prf.andE₁ (Prf.andE₂ den))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ den)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ den))))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ den))))
    (Prf.andE₁ ord) (Prf.andE₁ (Prf.andE₂ ord))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ ord))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ ord)))
    (Prf.andE₁ cmp) (Prf.andE₂ cmp)

theorem bound_denominator_positive (v D S j : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hD : Γ ⊢[PRAAx] le one D) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    le one (v*D*pw S j) :=
  positive_product _ _ (positive_product v D hv hD) (denominator_positive S j hS)

theorem bound_represents (u v C D R S j : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hD : Γ ⊢[PRAAx] le one D) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (bound u v C D R S j) (ZT.ofNat (u*C*pw R j)) (v*D*pw S j) :=
  fraction_represents _ _ (bound_denominator_positive v D S j hv hD hS)

theorem bound_canonical (u v C D R S j : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hD : Γ ⊢[PRAAx] le one D) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (bound u v C D R S j) :=
  RationalNormalForm.normalize_well_formed _ _ (bound_denominator_positive v D S j hv hD hS)

def boundF : PR 7 := PTm.toPR (bound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (u v C D R S j : PTm n) : PTm n := PTm.app boundF ![u,v,C,D,R,S,j]
ipra_subst run

theorem program_at (u v C D R S j : PTm n) : Γ ⊢[PRAAx] run u v C D R S j ≐ bound u v C D R S j := by
  simpa [run,boundF] using toPR_eq (Γ := Γ)
    (bound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![u,v,C,D,R,S,j]

theorem program_bound (a b u v C D q s R S j N i : PTm n)
    (h : Γ ⊢[PRAAx] conditions a b u v C D q s R S j N i) : Γ ⊢[PRAAx]
    rationalLE (fraction a b) (run u v C D R S j) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (program_at u v C D R S j).eqSymm
    (shrinking_step_of_conditions a b u v C D q s R S j N i h)

theorem squared_constant_absorption_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le (var 3) (var 2) ⟶ le two (var 4) ⟶
      le (var 3*var 3*pw (var 0) (var 4)) (var 2*var 2*pw (var 1) (var 4)) ⟶
        le (var 3*var 0) (var 2*var 1)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (absorb_constant _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem rational_shrinking_step_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (conditions (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
      (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
        rationalLE (fraction (var 0) (var 1)) (bound (var 2) (var 3) (var 4) (var 5) (var 8) (var 9) (var 10))) :=
  closeUniv 13 (.impI (shrinking_step_of_conditions _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem source_shrinking_step_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
    (conditions (var 0) (var 1) (var 2) (var 3) (var 6*var 15*var 5) (var 7*var 4)
      (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) ⟶
        rationalLE (fraction (var 0) (var 1))
          (fraction (var 2*(var 6*var 15*var 5)*pw (var 10) (var 12))
            (var 3*(var 7*var 4)*pw (var 11) (var 12)))) :=
  closeUniv 16 (.impI (shrinking_step_of_conditions _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem shrinking_step_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      bound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at _ _ _ _ _ _ _)

theorem returned_shrinking_step_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (conditions (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
      (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
        rationalLE (fraction (var 0) (var 1)) (run (var 2) (var 3) (var 4) (var 5) (var 8) (var 9) (var 10))) :=
  closeUniv 13 (.impI (program_bound _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalShrinkingStepPowerBound
