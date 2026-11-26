import IPRADerivations.Analysis.Geometry.HalfAngles.GaussianRationalHalfAngle
import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusArithmetic
import IPRADerivations.Analysis.Inequalities.RationalNonnegativePowers

/-!
# Actual repeated rational half-angles

One primitive recursive loop repeatedly applies the constructed principal
half-angle. All initial points, grid denominators and iteration counts are
numerical inputs. For an exactly unit input and a positive grid denominator,
the actual iterates remain unit and their squared distance to one is at
most 4/2^j. The induction is quantifier-free and has no supplied invariant
or accuracy premise. Canonicality of positive iterates is unconditional.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalHalfAngleIteration

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalCircleParametrization (four)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def step : PTm 4 := GaussianRationalHalfAngle.half (var 1) (var 3)
def iterationF : PR 3 := recDef (var 0 : PTm 2) step
def iterate (q H j : PTm n) : PTm n := ap3 iterationF j q H
def distance (q : PTm n) : PTm n := qnormSq (qsub q GaussianRationalReciprocal.qone)
def nearOne (q H j : PTm n) : Fm PTm n :=
  RationalArgmin.rationalLE (distance (iterate q H j)) (fraction four (unit j))

ipra_subst iterate
ipra_subst distance
ipra_subst nearOne

theorem iterate_zero (q H : PTm n) : Γ ⊢[PRAAx] iterate q H zero ≐ q := by
  have h := rec_zero (Γ := Γ) (var 0 : PTm 2) step ![q,H]
  have e : (Fin.cases zero ![q,H] : Fin 3 → PTm n) = ![zero,q,H] := by funext i; fin_cases i <;> rfl
  rw [e] at h
  simpa only [iterate,iterationF,ap3,Syn.subst_var,Matrix.cons_val_zero] using h

theorem iterate_succ (q H j : PTm n) : Γ ⊢[PRAAx]
    iterate q H (succ j) ≐ GaussianRationalHalfAngle.half (iterate q H j) H := by
  have h := rec_succ (Γ := Γ) (var 0 : PTm 2) step j ![q,H]
  have a : (Fin.cases (succ j) ![q,H] : Fin 3 → PTm n) = ![succ j,q,H] := by funext i; fin_cases i <;> rfl
  have b : (Fin.cases j (Fin.cases (PTm.app iterationF (Fin.cases j ![q,H])) ![q,H]) :
      Fin 4 → PTm n) = ![j,iterate q H j,q,H] := by funext i; fin_cases i <;> rfl
  unfold iterationF at b
  rw [a,b] at h
  simpa only [iterate,iterationF,ap3,step,GaussianRationalHalfAngle.subst_half,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using h

theorem iterate_index_congr (q H : PTm n) {j k : PTm n} (h : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] iterate q H j ≐ iterate q H k := congrAp3 iterationF h (.eqRefl _) (.eqRefl _)

theorem distance_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) :
    Γ ⊢[PRAAx] distance q ≐ distance r := by
  ipra_congr (distance (var 0) : PTm 1) with [h]

theorem unit_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r)
    (hr : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit r) : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit q := by
  have hn : Γ ⊢[PRAAx] qnormSq q ≐ qnormSq r := by
    ipra_congr (qnormSq (var 0) : PTm 1) with [h]
  exact hn.eqTrans hr

theorem iterate_unit (q H j : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hq : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit q) : Γ ⊢[PRAAx]
    GaussianRationalHalfAngle.unit (iterate q H j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact unit_congr ((iterate_index_congr q H Prf.hyp0).eqTrans (iterate_zero q H)) hq.wk
  · exact unit_congr ((iterate_index_congr q H Prf.hyp0).eqTrans (iterate_succ q H _))
      (GaussianRationalHalfAngle.half_unit _ _ hH.wk)

theorem iterate_canonical_positive (q H j : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hj : Γ ⊢[PRAAx] le one j) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (iterate q H j) :=
  GaussianRationalHorner.canonical_congr
    ((iterate_index_congr q H (RationalIntegerNormalization.positive_form hj)).eqTrans (iterate_succ q H _))
    (GaussianRationalHalfAngle.half_canonical _ _ hH)

theorem iterate_canonical (q H j : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hq : Γ ⊢[PRAAx] GaussianRationalHorner.canonical q) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (iterate q H j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr
      ((iterate_index_congr q H Prf.hyp0).eqTrans (iterate_zero q H)) hq.wk
  · exact GaussianRationalHorner.canonical_congr
      ((iterate_index_congr q H Prf.hyp0).eqTrans (iterate_succ q H _))
      (GaussianRationalHalfAngle.half_canonical _ _ hH.wk)

/-- Exact contraction transports any rational squared-distance budget.
The halved numerator is never rounded or supplied as an input premise. -/
theorem half_budget (q H A B : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit q)
    (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (distance q) (fraction A B)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (distance (GaussianRationalHalfAngle.half q H)) (fraction A (two*B)) := by
  have cleared := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (fraction_represents (two*GaussianRationalHalfAngle.minus q) (rawDen q) (raw_den_positive q))
    (fraction_represents A B hB)
    (RationalArgmin.rationalLE_congr (GaussianRationalHalfAngle.input_distance q hq) (.eqRefl _) h)
  exact RationalArgmin.transitive (GaussianRationalHalfAngle.half_contraction_fraction q H hH hq)
    (GaussianEuclideanDistanceName.fraction_order _ _ _ _ (raw_den_positive q)
      (positive_product _ _ (le_of_eq_add (d := one) (by ipra_ring)) hB)
      (le_congr (by ipra_ring) (.eqRefl _) cleared))

theorem initial_distance (q : PTm n) (hq : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (distance q) (fraction four one) := by
  have bound := mul_le_mul_right two (GaussianRationalHalfAngle.minus_bound q hq)
  exact RationalArgmin.rationalLE_congr (GaussianRationalHalfAngle.input_distance q hq).eqSymm (.eqRefl _)
    (GaussianEuclideanDistanceName.fraction_order _ _ _ _ (raw_den_positive q) (le_refl one)
      (le_congr (by ipra_ring) (by unfold GaussianRationalHalfAngle.base four; ipra_ring) bound))

/-- Genuine QF induction over the actual repeated constructor. -/
theorem iterate_near_one (q H j : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hq : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit q) : Γ ⊢[PRAAx] nearOne q H j := by
  have Hshift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift H) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hH.shift
  have qshift : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalHalfAngle.unit (Syn.shift q) := by
    simpa only [Fm.shift,GaussianRationalHalfAngle.subst_unit,Syn.shift] using hq.shift
  have all : Γ ⊢[PRAAx] .all (nearOne (Syn.shift q) (Syn.shift H) (var 0)) := by
    ipra_qfind (le_QF _ _) [subst_nearOne]
    · exact RationalArgmin.rationalLE_congr (distance_congr (iterate_zero q H)).eqSymm
        (RationalNonnegativePowers.fraction_congr (.eqRefl _) (pw_zero two)).eqSymm (initial_distance q hq)
    · let Δ := nearOne (Syn.shift q) (Syn.shift H) (var 0) :: Γ.map Fm.shift
      have previousUnit := iterate_unit (Γ := Δ) (Syn.shift q) (Syn.shift H) (var 0) Hshift.wk qshift.wk
      have next := half_budget (iterate (Syn.shift q) (Syn.shift H) (var 0)) (Syn.shift H) four (unit (var 0))
        Hshift.wk (unit_positive _) previousUnit (Prf.hyp0 : Δ ⊢[PRAAx] nearOne (Syn.shift q) (Syn.shift H) (var 0))
      exact RationalArgmin.rationalLE_congr (distance_congr (iterate_succ _ _ _)).eqSymm
        (RationalNonnegativePowers.fraction_congr (.eqRefl _)
          ((pw_succ two (var 0)).eqTrans (mul_comm _ _))).eqSymm next
  simpa only [subst_nearOne,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

def output (q H j : PTm n) : PTm n := pairT (iterate q H j) (pairT (unit j) (pairT H j))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (q H j : PTm n) : PTm n := ap3 outputF q H j

ipra_subst output
ipra_subst run

theorem program_at (q H j : PTm n) : Γ ⊢[PRAAx] run q H j ≐ output q H j := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![q,H,j]

theorem returned_point (q H j : PTm n) : Γ ⊢[PRAAx] fstT (run q H j) ≐ iterate q H j :=
  (program_at q H j).fstE
theorem returned_denominator (q H j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run q H j)) ≐ unit j :=
  (program_at q H j).sndE.fstE
theorem returned_grid (q H j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run q H j))) ≐ H :=
  (program_at q H j).sndE.sndE.fstE
theorem returned_count (q H j : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run q H j))) ≐ j :=
  (program_at q H j).sndE.sndE.sndE

theorem returned_bound (q H j : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hq : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (distance (fstT (run q H j))) (fraction four (unit j)) :=
  RationalArgmin.rationalLE_congr (distance_congr (returned_point q H j)).eqSymm (.eqRefl _)
    (iterate_near_one q H j hH hq)

theorem repeated_half_angle_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ GaussianRationalHalfAngle.unit (var 0) ⟶
      GaussianRationalHalfAngle.unit (iterate (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (iterate_unit _ _ _ Prf.hyp1 Prf.hyp0)))

theorem repeated_half_angle_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ GaussianRationalHalfAngle.unit (var 0) ⟶ nearOne (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (iterate_near_one _ _ _ Prf.hyp1 Prf.hyp0)))

theorem repeated_half_angle_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ GaussianRationalHorner.canonical (var 0) ⟶
      GaussianRationalHorner.canonical (iterate (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (iterate_canonical _ _ _ Prf.hyp1 Prf.hyp0)))

theorem half_angle_iteration_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) ⋏
      (fstT (run (var 0) (var 1) (var 2)) ≐ iterate (var 0) (var 1) (var 2) ⋏
        (fstT (sndT (run (var 0) (var 1) (var 2))) ≐ unit (var 2) ⋏
          (fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ var 1 ⋏
            sndT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ var 2)))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_point _ _ _)
    (.andI (returned_denominator _ _ _) (.andI (returned_grid _ _ _) (returned_count _ _ _)))))

theorem returned_half_angle_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ GaussianRationalHalfAngle.unit (var 0) ⟶
      RationalArgmin.rationalLE (distance (fstT (run (var 0) (var 1) (var 2)))) (fraction four (unit (var 2)))) :=
  closeUniv 3 (.impI (.impI (returned_bound _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalHalfAngleIteration
