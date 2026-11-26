import IPRADerivations.Analysis.Names.GaussianLinearDistanceName
import IPRADerivations.Analysis.RationalArithmetic.RationalClosure

/-!
# Finite dyadic slack removal for nonnegative rational observations

The scalar is an actual rational code with a supplied natural-numerator
representation. Clearing its actual positive denominator reduces the
comparison to the natural integer-gap lemma. A single PR precision
`C*B*E` removes the slack C*2^-m from a bound A/B. No limiting principle,
quantified induction or search for a successful precision is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianScalarSlackRemoval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianEuclideanPointDistance (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def precision (E B C : PTm n) : PTm n := C*B*E
def slack (z A B C m : PTm n) : Fm PTm n :=
  rationalLE z (fraction (A*unit m+C*B) (B*unit m))
def allSlack (z A B C : PTm n) : Fm PTm n :=
  .all (slack (Syn.shift z) (Syn.shift A) (Syn.shift B) (Syn.shift C) (var 0))

@[simp] theorem subst_precision {l : ℕ} (σ : Fin n → PTm l) (E B C : PTm n) :
    Syn.subst σ (precision E B C) = precision (Syn.subst σ E) (Syn.subst σ B) (Syn.subst σ C) := by
  simp [precision]
@[simp] theorem subst_slack {l : ℕ} (σ : Fin n → PTm l) (z A B C m : PTm n) :
    (slack z A B C m).subst σ = slack (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ C) (Syn.subst σ m) := by
  simp [slack]
@[simp] theorem subst_allSlack {l : ℕ} (σ : Fin n → PTm l) (z A B C : PTm n) :
    (allSlack z A B C).subst σ = allSlack (Syn.subst σ z) (Syn.subst σ A)
      (Syn.subst σ B) (Syn.subst σ C) := by
  simp [allSlack,Syn.subst_shift,Syn.shift_subst]

theorem slack_at (z A B C m : PTm n) (h : Γ ⊢[PRAAx] allSlack z A B C) :
    Γ ⊢[PRAAx] slack z A B C m := by
  simpa only [allSlack,subst_slack,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE m

/-- The supplied representation describes the actual scalar; the bound
is decoded and cleared by the original rational comparison theorem. -/
theorem slack_linear (z P E A B C m : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] RationalArithmetic.represents z (ZT.ofNat P) E)
    (h : Γ ⊢[PRAAx] slack z A B C m) : Γ ⊢[PRAAx]
    le (unit m*(B*P)) (unit m*(A*E)+precision E B C) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ hz
    (fraction_represents _ _ (positive_product _ _ hB (unit_positive m))) h
  exact le_congr (by ipra_ring) (by unfold precision; ipra_ring) raw

/-- Querying exactly the computed integer-gap precision already suffices. -/
theorem slack_removal_at (z P E A B C : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] RationalArithmetic.represents z (ZT.ofNat P) E)
    (h : Γ ⊢[PRAAx] slack z A B C (precision E B C)) :
    Γ ⊢[PRAAx] rationalLE z (fraction A B) := by
  have linear := slack_linear z P E A B C (precision E B C) hB hz h
  have cleared : Γ ⊢[PRAAx] le (B*P) (A*E) := by
    refine .orE (lt_or_le (A*E) (B*P)) ?_ Prf.hyp0
    exact RationalClosure.closure_aux _ Prf.hyp0 linear.wk
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hE hB hz
    (fraction_represents _ _ hB) cleared

theorem slack_removal (z P E A B C : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] RationalArithmetic.represents z (ZT.ofNat P) E)
    (h : Γ ⊢[PRAAx] allSlack z A B C) :
    Γ ⊢[PRAAx] rationalLE z (fraction A B) :=
  slack_removal_at z P E A B C hE hB hz (slack_at z A B C (precision E B C) h)

/-- Compose a genuine one-sided scalar error with an actual rational
upper bound. The middle representation denominator is proved positive
and cancelled, with no common-denominator assumption. -/
theorem upper_cut (u v P E Q F A B C D : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hF : Γ ⊢[PRAAx] le one F)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hu : Γ ⊢[PRAAx] RationalArithmetic.represents u (ZT.ofNat P) E)
    (hv : Γ ⊢[PRAAx] RationalArithmetic.represents v (ZT.ofNat Q) F)
    (hError : Γ ⊢[PRAAx] RationalValueBounds.upper u v A B)
    (hBound : Γ ⊢[PRAAx] rationalLE v (fraction C D)) : Γ ⊢[PRAAx]
    rationalLE u (fraction (C*B+A*D) (D*B)) := by
  have raw := GaussianLinearDistanceName.upper_to_cleared _ _ _ _ _ _ _ _ hu hv hError
  have bound := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ hv
    (fraction_represents _ _ hD) hBound
  have first : Γ ⊢[PRAAx] le (F*((D*B)*P)) (D*B*Q*E+D*A*E*F) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right D raw)
  have second : Γ ⊢[PRAAx] le (D*B*Q*E+D*A*E*F) (F*((C*B+A*D)*E)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (D*A*E*F) (mul_le_mul_right (B*E) bound))
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hE
    (positive_product _ _ hD hB) hu (fraction_represents _ _ (positive_product _ _ hD hB))
    (RationalValueBounds.positive_cancel hF (le_trans first second))

def precisionF : PR 3 := PTm.toPR (precision (var 0) (var 1) (var 2))

theorem precision_at (E B C : PTm n) : Γ ⊢[PRAAx]
    ap3 precisionF E B C ≐ precision E B C := by
  simpa only [precisionF,ap3,subst_precision,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (precision (var 0) (var 1) (var 2) : PTm 3) ![E,B,C]

theorem finite_scalar_slack_removal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le one (var 4) ⟶
      RationalArithmetic.represents (var 0) (ZT.ofNat (var 1)) (var 2) ⟶
      slack (var 0) (var 3) (var 4) (var 5) (precision (var 2) (var 4) (var 5)) ⟶
      rationalLE (var 0) (fraction (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (slack_removal_at _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem scalar_slack_removal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le one (var 4) ⟶
      RationalArithmetic.represents (var 0) (ZT.ofNat (var 1)) (var 2) ⟶
      allSlack (var 0) (var 3) (var 4) (var 5) ⟶
      rationalLE (var 0) (fraction (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (slack_removal _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem scalar_slack_query_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 precisionF (var 0) (var 1) (var 2) ≐ precision (var 0) (var 1) (var 2)) :=
  closeUniv 3 (precision_at _ _ _)

theorem scalar_upper_cut_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (le one (var 3) ⟶ le one (var 5) ⟶ le one (var 7) ⟶ le one (var 9) ⟶
      RationalArithmetic.represents (var 0) (ZT.ofNat (var 2)) (var 3) ⟶
      RationalArithmetic.represents (var 1) (ZT.ofNat (var 4)) (var 5) ⟶
      RationalValueBounds.upper (var 0) (var 1) (var 6) (var 7) ⟶
      rationalLE (var 1) (fraction (var 8) (var 9)) ⟶
      rationalLE (var 0) (fraction (var 8*var 7+var 6*var 9) (var 9*var 7))) := by
  apply closeUniv 10
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  exact upper_cut _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianScalarSlackRemoval
