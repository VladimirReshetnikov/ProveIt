import IPRADerivations.Analysis.RationalArithmetic.Distances.RationalPointDistanceVariation
import IPRADerivations.Analysis.Optimization.Aggregates.AggregateOptimization

/-!
# Distance names, finite observations and representation independence

Finite-demand Section 3, equations (D) and (E).  Fixed rational points use
the actual minimum against `S_k`; regular point names use the prescribed
actual samples `d(U_(k+1),S_(k+1))`.  The finite variation theorem gives
their regularity and Lipschitz bounds at independent rational scales.
Equivalent aggregate and point names give equivalent distance names.

All dimensions, indices, rational radii and persistent data are internal.
Only the fixed point/list PR evaluators are schema parameters.  No
completed real, chosen support point or equality test on PR programs is
used.  The displayed observation inequalities are the finite meaning of
the represented-distance assertions in the source.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.AggregateDistanceName

open_ipra
open LeanProofs.IPRA.Analysis
open LeanProofs.IPRA.Analysis.AggregateEquality
open LeanProofs.IPRA.Analysis.AggregateOptimization (pointRegular pointRegular_at subst_pointRegular)
open LeanProofs.IPRA.Analysis.RationalPointDistanceVariation (scalarCode variation_radius)
open LeanProofs.IPRA.Analysis.RationalHausdorff (pointRadius originalClose)
open LeanProofs.IPRA.Analysis.RationalValueBounds (radius radius_congr radius_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def fixedDistance (S : PR 2) (z k d x : PTm n) : PTm n := scalarCode z (sample S k x) d
def movingDistance (U S : PR 2) (k d x : PTm n) : PTm n :=
  scalarCode (sample U (succ k) x) (sample S (succ k) x) d

ipra_subst fixedDistance
ipra_subst movingDistance

theorem unit_product_positive (s t : PTm n) : Γ ⊢[PRAAx] le one (unit s*unit t) :=
  le_congr (one_mul one) (.eqRefl _) (le_mul_mono (unit_positive s) (unit_positive t))

theorem unit_successor (k : PTm n) : Γ ⊢[PRAAx] unit (succ k) ≐ two*unit k :=
  (pw_succ two k).eqTrans (mul_comm _ _)

/-- A fixed rational point needs no artificial point-name input. -/
theorem fixed_observation (S : PR 2) (z s t d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (rS : Γ ⊢[PRAAx] regular S d x) :
    Γ ⊢[PRAAx] radius (fixedDistance S z s d x) (fixedDistance S z t d x)
      (unit s+unit t) (unit s*unit t) := by
  have r := variation_radius z z (sample S s x) (sample S t x) d zero one
    (unit s+unit t) (unit s*unit t) (nonempty_at S s x hS) (nonempty_at S t x hS)
    (le_refl one) (unit_product_positive s t) (pointRadius_diagonal _ _ _ _)
    (regular_at S s t d x rS)
  exact radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) r

/-- Actual `k+1` samples pay one half of the error for each of the point
and aggregate names, giving exactly the source regularity constant. -/
theorem moving_regular_at (U S : PR 2) (s t d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (rS : Γ ⊢[PRAAx] regular S d x)
    (rU : Γ ⊢[PRAAx] pointRegular U d x) :
    Γ ⊢[PRAAx] radius (movingDistance U S s d x) (movingDistance U S t d x)
      (unit s+unit t) (unit s*unit t) := by
  have pos := unit_product_positive (Γ := Γ) (succ s) (succ t)
  have r := variation_radius (sample U (succ s) x) (sample U (succ t) x)
    (sample S (succ s) x) (sample S (succ t) x) d
    (unit (succ s)+unit (succ t)) (unit (succ s)*unit (succ t))
    (unit (succ s)+unit (succ t)) (unit (succ s)*unit (succ t))
    (nonempty_at S (succ s) x hS) (nonempty_at S (succ t) x hS) pos pos
    (pointRegular_at U (succ s) (succ t) d x rU) (regular_at S (succ s) (succ t) d x rS)
  apply radius_mono _ _ _ _ _ _
    (le_congr (one_mul one) (.eqRefl _) (le_mul_mono pos pos)) r
  apply le_of_eq_add (d := zero)
  have es := natEq (unit_successor (Γ := Γ) s)
  have et := natEq (unit_successor (Γ := Γ) t)
  apply deriveNat
  ipra_simps
  rw [es,et]
  ring

def fixedRegular (S : PR 2) (z d x : PTm n) : Fm PTm n :=
  .all (.all (radius (fixedDistance S (Syn.shift (Syn.shift z)) (var 1) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)))
    (fixedDistance S (Syn.shift (Syn.shift z)) (var 0) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))
def movingRegular (U S : PR 2) (d x : PTm n) : Fm PTm n :=
  .all (.all (radius (movingDistance U S (var 1) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)))
    (movingDistance U S (var 0) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

theorem fixed_regular (S : PR 2) (z d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (rS : Γ ⊢[PRAAx] regular S d x) :
    Γ ⊢[PRAAx] fixedRegular S z d x := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] nonempty S (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_nonempty,Syn.shift] using hS.shift.shift
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] regular S (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_regular,Syn.shift] using rS.shift.shift
  exact fixed_observation S _ _ _ _ _ hs rs

theorem moving_regular (U S : PR 2) (d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (rS : Γ ⊢[PRAAx] regular S d x)
    (rU : Γ ⊢[PRAAx] pointRegular U d x) : Γ ⊢[PRAAx] movingRegular U S d x := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] nonempty S (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_nonempty,Syn.shift] using hS.shift.shift
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] regular S (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_regular,Syn.shift] using rS.shift.shift
  have ru : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointRegular U (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_pointRegular,Syn.shift] using rU.shift.shift
  exact moving_regular_at U S _ _ _ _ hs rs ru

/-- Finite observation form of `|D_S(U)-d(U_p,S_s)| ≤ e_p+e_s`:
the actual name sample at index `k` has precisely its additional `e_k`.
There is no chosen completed point or supplied distance-name bound. -/
theorem moving_observation_at (U S : PR 2) (k p s d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (rS : Γ ⊢[PRAAx] regular S d x)
    (rU : Γ ⊢[PRAAx] pointRegular U d x) :
    Γ ⊢[PRAAx] radius (movingDistance U S k d x) (scalarCode (sample U p x) (sample S s x) d)
      (unit p*unit s+unit k*(unit p+unit s)) (unit k*unit p*unit s) := by
  have pb := unit_product_positive (Γ := Γ) (succ k) p
  have sb := unit_product_positive (Γ := Γ) (succ k) s
  have r := variation_radius (sample U (succ k) x) (sample U p x)
    (sample S (succ k) x) (sample S s x) d
    (unit (succ k)+unit p) (unit (succ k)*unit p)
    (unit (succ k)+unit s) (unit (succ k)*unit s)
    (nonempty_at S (succ k) x hS) (nonempty_at S s x hS) pb sb
    (pointRegular_at U (succ k) p d x rU) (regular_at S (succ k) s d x rS)
  apply radius_mono _ _ _ _ _ _
    (le_congr (one_mul one) (.eqRefl _) (le_mul_mono pb sb)) r
  apply le_of_eq_add (d := zero)
  have e := natEq (unit_successor (Γ := Γ) k)
  apply deriveNat
  ipra_simps
  rw [e]
  ring

/-- Finite form of the fixed-point Lipschitz assertion in equation (D):
the same actual aggregate sample costs no aggregate error at all. -/
theorem fixed_lipschitz_at (S : PR 2) (z w k d A B x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hB : Γ ⊢[PRAAx] le one B)
    (hzw : Γ ⊢[PRAAx] pointRadius z w d A B) :
    Γ ⊢[PRAAx] radius (fixedDistance S z k d x) (fixedDistance S w k d x) A B := by
  have r := variation_radius z w (sample S k x) (sample S k x) d A B zero one
    (nonempty_at S k x hS) (nonempty_at S k x hS) hB (le_refl _) hzw (close_diagonal _ _ _ _)
  exact radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) r

/-- No equality decision on evaluators is asserted: this is an unbounded
observational equality of point names in the source's `2e_k` convention. -/
def pointEquivalent (U V : PR 2) (d x : PTm n) : Fm PTm n :=
  .all (pointRadius (sample U (var 0) (Syn.shift x)) (sample V (var 0) (Syn.shift x)) (Syn.shift d) two (unit (var 0)))

ipra_subst pointEquivalent [Fm.subst_all, RationalHausdorff.subst_pointRadius, subst_sample, subst_unit,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ]

def representsFixed (U : PR 2) (z d x : PTm n) : Fm PTm n :=
  .all (pointRadius (sample U (var 0) (Syn.shift x)) (Syn.shift z) (Syn.shift d) one (unit (var 0)))

theorem represents_fixed_at (U : PR 2) (z k d x : PTm n)
    (h : Γ ⊢[PRAAx] representsFixed U z d x) :
    Γ ⊢[PRAAx] pointRadius (sample U k x) z d one (unit k) := by
  simpa [representsFixed] using Prf.allE k h

/-- The two source distance constructions agree when a regular point name
represents a fixed rational point. The exact budget is the standard `2e_k`.
-/
theorem fixed_moving_compatible_at (U S : PR 2) (z k d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (rS : Γ ⊢[PRAAx] regular S d x)
    (hz : Γ ⊢[PRAAx] representsFixed U z d x) :
    Γ ⊢[PRAAx] radius (movingDistance U S k d x) (fixedDistance S z k d x) two (unit k) := by
  have ub := unit_positive (Γ := Γ) (succ k)
  have rb := unit_product_positive (Γ := Γ) (succ k) k
  have r := variation_radius (sample U (succ k) x) z (sample S (succ k) x) (sample S k x) d
    one (unit (succ k)) (unit (succ k)+unit k) (unit (succ k)*unit k)
    (nonempty_at S (succ k) x hS) (nonempty_at S k x hS) ub rb
    (represents_fixed_at U z (succ k) d x hz) (regular_at S (succ k) k d x rS)
  apply radius_mono _ _ _ _ _ _
    (le_congr (one_mul one) (.eqRefl _) (le_mul_mono ub rb)) r
  apply le_of_eq_add (d := zero)
  have e := natEq (unit_successor (Γ := Γ) k)
  apply deriveNat
  ipra_simps
  rw [e]
  ring

theorem point_equivalent_at (U V : PR 2) (k d x : PTm n)
    (h : Γ ⊢[PRAAx] pointEquivalent U V d x) :
    Γ ⊢[PRAAx] pointRadius (sample U k x) (sample V k x) d two (unit k) := by
  simpa [pointEquivalent] using Prf.allE k h

theorem fixed_equivalent_at (S T : PR 2) (z k d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hT : Γ ⊢[PRAAx] nonempty T x)
    (hST : Γ ⊢[PRAAx] equivalent S T d x) :
    Γ ⊢[PRAAx] radius (fixedDistance S z k d x) (fixedDistance T z k d x) two (unit k) := by
  have r := variation_radius z z (sample S k x) (sample T k x) d zero one two (unit k)
    (nonempty_at S k x hS) (nonempty_at T k x hT) (le_refl _) (unit_positive k)
    (pointRadius_diagonal _ _ _ _) (equivalent_at S T k d x hST)
  exact radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) r

theorem moving_equivalent_at (U V S T : PR 2) (k d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hT : Γ ⊢[PRAAx] nonempty T x)
    (hUV : Γ ⊢[PRAAx] pointEquivalent U V d x) (hST : Γ ⊢[PRAAx] equivalent S T d x) :
    Γ ⊢[PRAAx] radius (movingDistance U S k d x) (movingDistance V T k d x) two (unit k) := by
  have r := variation_radius (sample U (succ k) x) (sample V (succ k) x)
    (sample S (succ k) x) (sample T (succ k) x) d two (unit (succ k)) two (unit (succ k))
    (nonempty_at S (succ k) x hS) (nonempty_at T (succ k) x hT) (unit_positive _) (unit_positive _)
    (point_equivalent_at U V (succ k) d x hUV) (equivalent_at S T (succ k) d x hST)
  apply radius_mono _ _ _ _ _ _ (unit_product_positive (succ k) (succ k)) r
  apply le_of_eq_add (d := zero)
  have e := natEq (unit_successor (Γ := Γ) k)
  apply deriveNat
  ipra_simps
  rw [e]
  ring

def fixedEquivalent (S T : PR 2) (z d x : PTm n) : Fm PTm n :=
  .all (radius (fixedDistance S (Syn.shift z) (var 0) (Syn.shift d) (Syn.shift x))
    (fixedDistance T (Syn.shift z) (var 0) (Syn.shift d) (Syn.shift x)) two (unit (var 0)))
def movingEquivalent (U V S T : PR 2) (d x : PTm n) : Fm PTm n :=
  .all (radius (movingDistance U S (var 0) (Syn.shift d) (Syn.shift x))
    (movingDistance V T (var 0) (Syn.shift d) (Syn.shift x)) two (unit (var 0)))

theorem fixed_names_equivalent (S T : PR 2) (z d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hT : Γ ⊢[PRAAx] nonempty T x)
    (hST : Γ ⊢[PRAAx] equivalent S T d x) : Γ ⊢[PRAAx] fixedEquivalent S T z d x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] nonempty S (Syn.shift x) := by
    simpa only [Fm.shift,subst_nonempty,Syn.shift] using hS.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] nonempty T (Syn.shift x) := by
    simpa only [Fm.shift,subst_nonempty,Syn.shift] using hT.shift
  have he : Γ.map Fm.shift ⊢[PRAAx] equivalent S T (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift,subst_equivalent,Syn.shift] using hST.shift
  exact fixed_equivalent_at S T _ _ _ _ hs ht he

theorem moving_names_equivalent (U V S T : PR 2) (d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hT : Γ ⊢[PRAAx] nonempty T x)
    (hUV : Γ ⊢[PRAAx] pointEquivalent U V d x) (hST : Γ ⊢[PRAAx] equivalent S T d x) :
    Γ ⊢[PRAAx] movingEquivalent U V S T d x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] nonempty S (Syn.shift x) := by
    simpa only [Fm.shift,subst_nonempty,Syn.shift] using hS.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] nonempty T (Syn.shift x) := by
    simpa only [Fm.shift,subst_nonempty,Syn.shift] using hT.shift
  have hp : Γ.map Fm.shift ⊢[PRAAx] pointEquivalent U V (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointEquivalent,Syn.shift] using hUV.shift
  have he : Γ.map Fm.shift ⊢[PRAAx] equivalent S T (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift,subst_equivalent,Syn.shift] using hST.shift
  exact moving_equivalent_at U V S T _ _ _ hs ht hp he

def fixedDistanceF (S : PR 2) : PR 4 := PTm.toPR (fixedDistance S (var 0) (var 1) (var 2) (var 3))
def movingDistanceF (U S : PR 2) : PR 3 := PTm.toPR (movingDistance U S (var 0) (var 1) (var 2))

theorem fixed_program_at (S : PR 2) (z k d x : PTm n) :
    Γ ⊢[PRAAx] PTm.app (fixedDistanceF S) ![z,k,d,x] ≐ fixedDistance S z k d x := by
  simpa only [fixedDistanceF,subst_fixedDistance,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (fixedDistance S (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,k,d,x]
theorem moving_program_at (U S : PR 2) (k d x : PTm n) :
    Γ ⊢[PRAAx] ap3 (movingDistanceF U S) k d x ≐ movingDistance U S k d x := by
  simpa only [movingDistanceF,ap3,subst_movingDistance,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (movingDistance U S (var 0) (var 1) (var 2) : PTm 3) ![k,d,x]

theorem fixed_regular_closed (S : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonempty S (var 2) ⟶ regular S (var 1) (var 2) ⟶ fixedRegular S (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (fixed_regular S _ _ _ Prf.hyp1 Prf.hyp0)))
theorem moving_regular_closed (U S : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (nonempty S (var 1) ⟶ regular S (var 0) (var 1) ⟶ pointRegular U (var 0) (var 1) ⟶ movingRegular U S (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (.impI (moving_regular U S _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem observation_closed (S : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (nonempty S (var 4) ⟶ regular S (var 3) (var 4) ⟶
      radius (fixedDistance S (var 0) (var 1) (var 3) (var 4)) (fixedDistance S (var 0) (var 2) (var 3) (var 4))
        (unit (var 1)+unit (var 2)) (unit (var 1)*unit (var 2))) :=
  closeUniv 5 (.impI (.impI (fixed_observation S _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem moving_observation_closed (U S : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (nonempty S (var 4) ⟶ regular S (var 3) (var 4) ⟶ pointRegular U (var 3) (var 4) ⟶
      radius (movingDistance U S (var 0) (var 3) (var 4))
        (scalarCode (sample U (var 1) (var 4)) (sample S (var 2) (var 4)) (var 3))
        (unit (var 1)*unit (var 2)+unit (var 0)*(unit (var 1)+unit (var 2)))
        (unit (var 0)*unit (var 1)*unit (var 2))) :=
  closeUniv 5 (.impI (.impI (.impI (moving_observation_at U S _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem fixed_moving_compatibility_closed (U S : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (nonempty S (var 3) ⟶ regular S (var 2) (var 3) ⟶ representsFixed U (var 0) (var 2) (var 3) ⟶
      radius (movingDistance U S (var 1) (var 2) (var 3)) (fixedDistance S (var 0) (var 1) (var 2) (var 3))
        two (unit (var 1))) :=
  closeUniv 4 (.impI (.impI (.impI (fixed_moving_compatible_at U S _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem lipschitz_closed (S : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (nonempty S (var 6) ⟶ le one (var 5) ⟶ pointRadius (var 0) (var 1) (var 3) (var 4) (var 5) ⟶
      radius (fixedDistance S (var 0) (var 2) (var 3) (var 6)) (fixedDistance S (var 1) (var 2) (var 3) (var 6))
        (var 4) (var 5)) :=
  closeUniv 7 (.impI (.impI (.impI (fixed_lipschitz_at S _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem fixed_equivalence_closed (S T : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (nonempty S (var 3) ⟶ nonempty T (var 3) ⟶ equivalent S T (var 2) (var 3) ⟶
      radius (fixedDistance S (var 0) (var 1) (var 2) (var 3)) (fixedDistance T (var 0) (var 1) (var 2) (var 3))
        two (unit (var 1))) :=
  closeUniv 4 (.impI (.impI (.impI (fixed_equivalent_at S T _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem moving_equivalence_closed (U V S T : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonempty S (var 2) ⟶ nonempty T (var 2) ⟶ pointEquivalent U V (var 1) (var 2) ⟶
      equivalent S T (var 1) (var 2) ⟶
        radius (movingDistance U S (var 0) (var 1) (var 2)) (movingDistance V T (var 0) (var 1) (var 2)) two (unit (var 0))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (moving_equivalent_at U V S T _ _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem fixed_names_equivalent_closed (S T : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonempty S (var 2) ⟶ nonempty T (var 2) ⟶ equivalent S T (var 1) (var 2) ⟶
      fixedEquivalent S T (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (fixed_names_equivalent S T _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem moving_names_equivalent_closed (U V S T : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (nonempty S (var 1) ⟶ nonempty T (var 1) ⟶ pointEquivalent U V (var 0) (var 1) ⟶
      equivalent S T (var 0) (var 1) ⟶ movingEquivalent U V S T (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (.impI (.impI (moving_names_equivalent U V S T _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem distance_programs_closed (U S : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((PTm.app (fixedDistanceF S) ![var 0,var 1,var 2,var 3] ≐ fixedDistance S (var 0) (var 1) (var 2) (var 3)) ⋏
      (ap3 (movingDistanceF U S) (var 0) (var 1) (var 2) ≐ movingDistance U S (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.andI (fixed_program_at S _ _ _ _) (moving_program_at U S _ _ _))

end LeanProofs.IPRA.Analysis.AggregateDistanceName
