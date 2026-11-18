import IPRADerivations.Analysis.GaussianRationalPowerAlgebra
import IPRADerivations.Analysis.GaussianRationalRelativeTriangle

/-!
# Actual Gaussian-rational power differences at runtime exponents

The original independently denominated inputs determine the product
difference identity. A genuine QF induction then bounds actual power
differences by j*R^(j-1) times the original point distance. The natural
budget handles j=0 and R=0 explicitly. Same-denominator Euclidean addition
preserves the exact radius, and the unit-disk specialization is j*A/B.
No power, difference, prefix, or final-output law is an input premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPowerDifference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qadd qmul represents positive_product qmul_represents qadd_represents represents_congr canonical_unique)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qsub_congr rescale_to remainingDen remaining_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power bound_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem product_difference_from_representations (a b u v A B U V E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] represents a A E)
    (hb : Γ ⊢[PRAAx] represents b B E) (hu : Γ ⊢[PRAAx] represents u U E)
    (hv : Γ ⊢[PRAAx] represents v V E) : Γ ⊢[PRAAx]
    qsub (qmul a u) (qmul b v) ≐ qadd (qmul (qsub a b) u) (qmul b (qsub u v)) := by
  have e2 := positive_product E E hE hE
  have lhs := GaussianRationalMetric.qsub_represents _ _ _ _ _ e2
    (qmul_represents _ _ _ _ _ _ hE hE ha hu) (qmul_represents _ _ _ _ _ _ hE hE hb hv)
  have rhs := qadd_represents _ _ _ _ _ e2
    (qmul_represents _ _ _ _ _ _ hE hE (GaussianRationalMetric.qsub_represents _ _ _ _ _ hE ha hb) hu)
    (qmul_represents _ _ _ _ _ _ hE hE hb (GaussianRationalMetric.qsub_represents _ _ _ _ _ hE hu hv))
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalHorner.qadd_canonical _ _) e2 (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_mul,
      GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add] <;> ring

theorem product_difference (a b u v : PTm n) : Γ ⊢[PRAAx]
    qsub (qmul a u) (qmul b v) ≐ qadd (qmul (qsub a b) u) (qmul b (qsub u v)) := by
  let E := remainingDen a b u v
  have ha := rescale_to a (rawGaussian a) (rawDen a) (rawDen b*rawDen u*rawDen v) E
    (raw_represents (Γ := Γ) a) (by unfold E remainingDen; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen a*rawDen u*rawDen v) E
    (raw_represents (Γ := Γ) b) (by unfold E remainingDen; ipra_ring)
  have hu := rescale_to u (rawGaussian u) (rawDen u) (rawDen a*rawDen b*rawDen v) E
    (raw_represents (Γ := Γ) u) (by unfold E remainingDen; ipra_ring)
  have hv := rescale_to v (rawGaussian v) (rawDen v) (rawDen a*rawDen b*rawDen u) E
    (raw_represents (Γ := Γ) v) (by unfold E remainingDen; ipra_ring)
  exact product_difference_from_representations _ _ _ _ _ _ _ _ E (remaining_den_positive a b u v) ha hb hu hv

def difference (u v j : PTm n) : PTm n := qsub (power u j) (power v j)
def budget (R A j : PTm n) : PTm n := j*pw R (pred j)*A
def distanceLaw (u v R A B j : PTm n) : Fm PTm n := bounded (difference u v j) (budget R A j) B

@[simp] theorem subst_difference {m : ℕ} (σ : Fin n → PTm m) (u v j : PTm n) :
    Syn.subst σ (difference u v j) = difference (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ j) := by simp [difference]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (R A j : PTm n) :
    Syn.subst σ (budget R A j) = budget (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ j) := by simp [budget]
@[simp] theorem subst_distanceLaw {m : ℕ} (σ : Fin n → PTm m) (u v R A B j : PTm n) :
    (distanceLaw u v R A B j).subst σ = distanceLaw (Syn.subst σ u) (Syn.subst σ v)
      (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ j) := by simp [distanceLaw]

theorem difference_succ (u v j : PTm n) : Γ ⊢[PRAAx]
    difference u v (succ j) ≐ qadd (qmul (difference u v j) u) (qmul (power v j) (qsub u v)) :=
  (qsub_congr (GaussianRationalReciprocal.power_succ u j) (GaussianRationalReciprocal.power_succ v j)).eqTrans
    (product_difference (power u j) (power v j) u v)

theorem budget_zero (R A : PTm n) : Γ ⊢[PRAAx] budget R A zero ≐ zero := by unfold budget; ipra_ring
theorem budget_succ (R A j : PTm n) : Γ ⊢[PRAAx] budget R A (succ j) ≐ succ j*pw R j*A :=
  congrMul (congrMul (.eqRefl _) (congrAp2 powF (pred_succ j) (.eqRefl _))) (.eqRefl _)

/-- Splitting exponent zero makes the exact recurrence valid even at
R=0. No positivity or division by R is used. -/
theorem budget_step (R A j : PTm n) : Γ ⊢[PRAAx]
    budget R A j*R+pw R j*A ≐ budget R A (succ j) := by
  have first : Γ ⊢[PRAAx] budget R A j*R+pw R j*A ≐ succ j*pw R j*A := by
    refine .orE (zero_or_succ j) ?_ ?_
    · have e := natEq (Prf.hyp0 : (j ≐ zero)::Γ ⊢[PRAAx] j ≐ zero)
      have p := natEq ((congrAp2 powF (Prf.hyp0 : (j ≐ zero)::Γ ⊢[PRAAx] j ≐ zero) (.eqRefl R)).eqTrans (pw_zero R))
      apply deriveNat
      unfold budget
      ipra_simps
      rw [e,p]
      ring
    · have positive := Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := j ≐ succ (pred j))
      have p := natEq ((congrAp2 powF positive (.eqRefl R)).eqTrans (pw_succ R (pred j)))
      apply deriveNat
      unfold budget
      ipra_simps
      rw [p]
      ring
  exact first.eqTrans (budget_succ R A j).eqSymm

theorem bounded_sum_same (q r A C B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] bounded q A B) (hr : Γ ⊢[PRAAx] bounded r C B) : Γ ⊢[PRAAx]
    bounded (qadd q r) (A+C) B :=
  GaussianRationalRelativeTriangle.relative_triangle q r A C (B*B) (positive_product B B hB hB) hq hr

theorem bounded_power_integer (q R j : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) : Γ ⊢[PRAAx]
    bounded (power q j) (pw R j) one :=
  bound_congr (.eqRefl _) (.eqRefl _) (GaussianPolynomialPerturbation.one_power j)
    (GaussianRationalReciprocal.bounded_power q R one j (le_refl one) hq)

theorem distance_refl_zero (q B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] distanceBounded q q zero B := by
  have d := raw_den_positive (Γ := Γ) q
  have rep := GaussianRationalMetric.qsub_represents q q (rawGaussian q) (rawGaussian q) (rawDen q) d (raw_represents q) (raw_represents q)
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ d hB rep
  have z := (GaussianRootAlgebra.normSq_equal (Γ := Γ) (GaussianRootAlgebra.sub_self (rawGaussian q))).eqTrans
    ComplexLogarithmRemainder.normSq_zero
  exact le_congr ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqSymm (by ipra_ring) (le_refl zero)

theorem difference_zero_bound (u v R A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceLaw u v R A B zero :=
  bound_congr (qsub_congr (GaussianRationalReciprocal.power_zero u) (GaussianRationalReciprocal.power_zero v)).eqSymm
    (budget_zero R A).eqSymm (.eqRefl _) (distance_refl_zero qone B hB)

theorem difference_step_bound (u v R A B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) (h : Γ ⊢[PRAAx] distanceLaw u v R A B j) : Γ ⊢[PRAAx]
    distanceLaw u v R A B (succ j) := by
  have first : Γ ⊢[PRAAx] bounded (qmul (difference u v j) u) (budget R A j*R) B :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB (le_refl one) h hu)
  have second : Γ ⊢[PRAAx] bounded (qmul (power v j) (qsub u v)) (pw R j*A) B :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul B)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hB (bounded_power_integer v R j hv) hd)
  exact bound_congr (difference_succ u v j).eqSymm (budget_step R A j) (.eqRefl _)
    (bounded_sum_same _ _ _ _ _ hB first second)

/-- The numerical exponent is internal. The only local inputs are the
two original disk comparisons and their genuine original point distance. -/
theorem power_distance_bound (u v R A B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    distanceBounded (power u j) (power v j) (budget R A j) B := by
  have bShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hB.shift
  have uShift : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift u) (Syn.shift R) one := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hu.shift
  have vShift : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift v) (Syn.shift R) one := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hv.shift
  have dShift : Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift u) (Syn.shift v) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_distanceBounded,Syn.shift] using hd.shift
  have all : Γ ⊢[PRAAx] .all (distanceLaw (Syn.shift u) (Syn.shift v) (Syn.shift R) (Syn.shift A) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_distanceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact difference_zero_bound u v R A B hB
    · simp only [subst_distanceLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact difference_step_bound _ _ _ _ _ _ bShift.wk uShift.wk vShift.wk dShift.wk Prf.hyp0
  change Γ ⊢[PRAAx] distanceLaw u v R A B j
  simpa only [subst_distanceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem unit_disk_power_difference (u v A B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u one one) (hv : Γ ⊢[PRAAx] bounded v one one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    distanceBounded (power u j) (power v j) (j*A) B := by
  have e : Γ ⊢[PRAAx] budget one A j ≐ j*A :=
    (congrMul (congrMul (.eqRefl _) (GaussianPolynomialPerturbation.one_power (pred j))) (.eqRefl _)).eqTrans (by ipra_ring)
  exact bound_congr (.eqRefl _) e (.eqRefl _) (power_distance_bound u v one A B j hB hu hv hd)

def output (u v R A B j : PTm n) : PTm n := pairT (difference u v j) (pairT (budget R A j) B)
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (u v R A B j : PTm n) : PTm n := PTm.app outputF ![u,v,R,A,B,j]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (u v R A B j : PTm n) :
    Syn.subst σ (output u v R A B j) = output (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ R)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ j) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (u v R A B j : PTm n) :
    Syn.subst σ (run u v R A B j) = run (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ R)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ j) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (u v R A B j : PTm n) : Γ ⊢[PRAAx] run u v R A B j ≐ output u v R A B j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![u,v,R,A,B,j]
theorem output_value (u v R A B j : PTm n) : Γ ⊢[PRAAx] fstT (run u v R A B j) ≐ difference u v j :=
  (congrFst (program_at u v R A B j)).eqTrans (fst_pair _ _)
theorem output_numerator (u v R A B j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run u v R A B j)) ≐ budget R A j :=
  (congrFst ((congrSnd (program_at u v R A B j)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem output_denominator (u v R A B j : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run u v R A B j)) ≐ B :=
  (congrSnd ((congrSnd (program_at u v R A B j)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem program_certificate (u v R A B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    le one (sndT (sndT (run u v R A B j))) ⋏
      bounded (fstT (run u v R A B j)) (fstT (sndT (run u v R A B j))) (sndT (sndT (run u v R A B j))) :=
  .andI (le_congr (.eqRefl _) (output_denominator u v R A B j).eqSymm hB)
    (bound_congr (output_value u v R A B j).eqSymm (output_numerator u v R A B j).eqSymm
      (output_denominator u v R A B j).eqSymm (power_distance_bound u v R A B j hB hu hv hd))

theorem rational_product_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (qsub (qmul (var 0) (var 2)) (qmul (var 1) (var 3)) ≐
      qadd (qmul (qsub (var 0) (var 1)) (var 2)) (qmul (var 1) (qsub (var 2) (var 3)))) :=
  closeUniv 4 (product_difference _ _ _ _)
theorem rational_power_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 4) ⟶ bounded (var 0) (var 2) one ⟶ bounded (var 1) (var 2) one ⟶
      distanceBounded (var 0) (var 1) (var 3) (var 4) ⟶
        distanceBounded (power (var 0) (var 5)) (power (var 1) (var 5)) (budget (var 2) (var 3) (var 5)) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (power_distance_bound _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem rational_unit_disk_power_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ bounded (var 0) one one ⟶ bounded (var 1) one one ⟶
      distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
        distanceBounded (power (var 0) (var 4)) (power (var 1) (var 4)) (var 4*var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (unit_disk_power_difference _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem rational_power_distance_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (budget (var 0) (var 1) (var 2)*var 0+pw (var 0) (var 2)*var 1 ≐ budget (var 0) (var 1) (succ (var 2))) :=
  closeUniv 3 (budget_step _ _ _)
theorem rational_power_distance_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ difference (var 0) (var 1) (var 5) ⋏
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ≐ budget (var 2) (var 3) (var 5) ⋏
          sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ≐ var 4))) :=
  closeUniv 6 (.andI (program_at _ _ _ _ _ _) (.andI (output_value _ _ _ _ _ _)
    (.andI (output_numerator _ _ _ _ _ _) (output_denominator _ _ _ _ _ _))))
theorem rational_power_distance_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 4) ⟶ bounded (var 0) (var 2) one ⟶ bounded (var 1) (var 2) one ⟶
      distanceBounded (var 0) (var 1) (var 3) (var 4) ⟶
        (le one (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) ⋏
          bounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
            (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))
            (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (program_certificate _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalPowerDifference
