import IPRADerivations.Analysis.GaussianRationalSumAlgebra
import IPRADerivations.Analysis.GaussianRationalProductWitness
import IPRADerivations.Analysis.RationalNonnegativePowers
import IPRADerivations.Core.LinearCombination

/-!
# Actual rational Gaussian power algebra at internal exponents

The existing power evaluator satisfies addition, composition and product
laws by genuine QF induction. Every exponent and original raw operand is
numerical. Unit norm propagates through the actual product program. Unit
and square simplifications identify an original input code with its power
only under the genuine canonical-input guard.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPowerAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qmul canonical represents positive_product qmul_represents represents_congr canonical_unique)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF power_zero power_succ power_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem qmul_commutative (u v : PTm n) : Γ ⊢[PRAAx] qmul u v ≐ qmul v u := by
  have du := raw_den_positive (Γ := Γ) u
  have dv := raw_den_positive (Γ := Γ) v
  have left := qmul_represents u v (rawGaussian u) (rawGaussian v) (rawDen u) (rawDen v) du dv (raw_represents u) (raw_represents v)
  have right := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm (rawDen v) (rawDen u))
    (qmul_represents v u (rawGaussian v) (rawGaussian u) (rawDen v) (rawDen u) dv du (raw_represents v) (raw_represents u))
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.qmul_canonical _ _) (positive_product _ _ du dv) (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply GaussianRootAlgebra.equal_of_values <;> simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul] <;> ring

theorem qmul_shuffle (a b c d : PTm n) : Γ ⊢[PRAAx]
    qmul (qmul a b) (qmul c d) ≐ qmul (qmul a c) (qmul b d) :=
  (GaussianReciprocalHorner.qmul_associative a b (qmul c d)).eqTrans
    ((qmul_congr (.eqRefl _)
      ((GaussianReciprocalHorner.qmul_associative b c d).eqSymm.eqTrans
        ((qmul_congr (qmul_commutative b c) (.eqRefl _)).eqTrans
          (GaussianReciprocalHorner.qmul_associative c b d)))).eqTrans
      (GaussianReciprocalHorner.qmul_associative a c (qmul b d)).eqSymm)

theorem power_one (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] power q one ≐ q :=
  (power_succ q zero).eqTrans ((qmul_congr (power_zero q) (.eqRefl _)).eqTrans
    ((qmul_commutative qone q).eqTrans (GaussianReciprocalHorner.qmul_one_right q hq)))

theorem power_two (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] power q two ≐ qmul q q :=
  (power_succ q one).eqTrans (qmul_congr (power_one q hq) (.eqRefl _))

def addLaw (q j k : PTm n) : Fm PTm n := power q (j+k) ≐ qmul (power q j) (power q k)
@[simp] theorem subst_addLaw {m : ℕ} (σ : Fin n → PTm m) (q j k : PTm n) :
    (addLaw q j k).subst σ = addLaw (Syn.subst σ q) (Syn.subst σ j) (Syn.subst σ k) := by simp [addLaw]

theorem add_zero_case (q j : PTm n) : Γ ⊢[PRAAx] addLaw q j zero :=
  (congrAp2 powerF (add_zero j) (.eqRefl _)).eqTrans
    ((qmul_congr (.eqRefl _) (power_zero q)).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (power_canonical q j))).eqSymm

theorem add_step (q j k : PTm n) (h : Γ ⊢[PRAAx] addLaw q j k) : Γ ⊢[PRAAx] addLaw q j (succ k) :=
  ((congrAp2 powerF (add_succ j k) (.eqRefl _)).eqTrans (power_succ q (j+k))).eqTrans
    ((qmul_congr h (.eqRefl _)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative (power q j) (power q k) q).eqTrans
        (qmul_congr (.eqRefl _) (power_succ q k).eqSymm)))

theorem power_add (q j k : PTm n) : Γ ⊢[PRAAx] power q (j+k) ≐ qmul (power q j) (power q k) := by
  have all : Γ ⊢[PRAAx] .all (addLaw (Syn.shift q) (Syn.shift j) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_addLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact add_zero_case q j
    · simp only [subst_addLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact add_step _ _ _ Prf.hyp0
  change Γ ⊢[PRAAx] addLaw q j k
  simpa only [subst_addLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

def compositionLaw (q j k : PTm n) : Fm PTm n := power (power q j) k ≐ power q (j*k)
@[simp] theorem subst_compositionLaw {m : ℕ} (σ : Fin n → PTm m) (q j k : PTm n) :
    (compositionLaw q j k).subst σ = compositionLaw (Syn.subst σ q) (Syn.subst σ j) (Syn.subst σ k) := by simp [compositionLaw]

theorem composition_zero (q j : PTm n) : Γ ⊢[PRAAx] compositionLaw q j zero :=
  (power_zero (power q j)).eqTrans ((congrAp2 powerF (mul_zero j) (.eqRefl q)).eqTrans (power_zero q)).eqSymm

theorem composition_step (q j k : PTm n) (h : Γ ⊢[PRAAx] compositionLaw q j k) : Γ ⊢[PRAAx] compositionLaw q j (succ k) :=
  (power_succ (power q j) k).eqTrans ((qmul_congr h (.eqRefl _)).eqTrans
    ((power_add q (j*k) j).eqSymm.eqTrans (congrAp2 powerF (by ipra_ring) (.eqRefl _))))

theorem power_composition (q j k : PTm n) : Γ ⊢[PRAAx] power (power q j) k ≐ power q (j*k) := by
  have all : Γ ⊢[PRAAx] .all (compositionLaw (Syn.shift q) (Syn.shift j) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_compositionLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact composition_zero q j
    · simp only [subst_compositionLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact composition_step _ _ _ Prf.hyp0
  change Γ ⊢[PRAAx] compositionLaw q j k
  simpa only [subst_compositionLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

def productLaw (u v j : PTm n) : Fm PTm n := power (qmul u v) j ≐ qmul (power u j) (power v j)
@[simp] theorem subst_productLaw {m : ℕ} (σ : Fin n → PTm m) (u v j : PTm n) :
    (productLaw u v j).subst σ = productLaw (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ j) := by simp [productLaw]

theorem product_zero (u v : PTm n) : Γ ⊢[PRAAx] productLaw u v zero :=
  (power_zero (qmul u v)).eqTrans ((qmul_congr (power_zero u) (power_zero v)).eqTrans
    (GaussianReciprocalHorner.qmul_one_right qone GaussianRationalSyntheticDivision.qone_canonical)).eqSymm

theorem product_step (u v j : PTm n) (h : Γ ⊢[PRAAx] productLaw u v j) : Γ ⊢[PRAAx] productLaw u v (succ j) :=
  (power_succ (qmul u v) j).eqTrans ((qmul_congr h (.eqRefl _)).eqTrans
    ((qmul_shuffle (power u j) (power v j) u v).eqTrans
      (qmul_congr (power_succ u j).eqSymm (power_succ v j).eqSymm)))

theorem power_product (u v j : PTm n) : Γ ⊢[PRAAx] power (qmul u v) j ≐ qmul (power u j) (power v j) := by
  have all : Γ ⊢[PRAAx] .all (productLaw (Syn.shift u) (Syn.shift v) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_productLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact product_zero u v
    · simp only [subst_productLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact product_step _ _ _ Prf.hyp0
  change Γ ⊢[PRAAx] productLaw u v j
  simpa only [subst_productLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem norm_one : Γ ⊢[PRAAx] qnormSq (qone : PTm n) ≐ fraction one one := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalMetric.qnormSq_canonical _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (GaussianRationalMetric.qnormSq_represents _ _ _ (le_refl one)
      (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one)))
    (fraction_represents one one (le_refl one)) (positive_product _ _ (le_refl one) (le_refl one)) (le_refl one)
  ipra_lc natEq (ComplexLogarithmRemainder.normSq_one (Γ := Γ))

def unitLaw (q j : PTm n) : Fm PTm n := qnormSq (power q j) ≐ fraction one one
@[simp] theorem subst_unitLaw {m : ℕ} (σ : Fin n → PTm m) (q j : PTm n) :
    (unitLaw q j).subst σ = unitLaw (Syn.subst σ q) (Syn.subst σ j) := by simp [unitLaw]

theorem unit_zero (q : PTm n) : Γ ⊢[PRAAx] unitLaw q zero :=
  (GaussianRationalProductWitness.qnormSq_congr (power_zero q)).eqTrans norm_one

theorem unit_step (q j : PTm n) (hq : Γ ⊢[PRAAx] qnormSq q ≐ fraction one one)
    (h : Γ ⊢[PRAAx] unitLaw q j) : Γ ⊢[PRAAx] unitLaw q (succ j) :=
  (GaussianRationalProductWitness.qnormSq_congr (power_succ q j)).eqTrans
    ((GaussianRationalProductWitness.norm_multiply _ _).eqTrans
      ((RationalAlgebra.multiply_congr h hq).eqTrans
        ((RationalNonnegativePowers.fraction_multiply one one one one (le_refl one) (le_refl one)).eqTrans
          (RationalNonnegativePowers.fraction_congr (one_mul one) (one_mul one)))))

theorem unit_power (q j : PTm n) (hq : Γ ⊢[PRAAx] qnormSq q ≐ fraction one one) : Γ ⊢[PRAAx]
    qnormSq (power q j) ≐ fraction one one := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] qnormSq (Syn.shift q) ≐ (fraction one one : PTm (n+1)) := by
    simpa only [Fm.shift,Fm.subst_eq,GaussianRationalMetric.subst_qnormSq,GaussianEuclideanDistanceName.subst_fraction,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hq.shift
  have all : Γ ⊢[PRAAx] .all (unitLaw (Syn.shift q) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_unitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact unit_zero q
    · simp only [subst_unitLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact unit_step _ _ shifted.wk Prf.hyp0
  change Γ ⊢[PRAAx] unitLaw q j
  simpa only [subst_unitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem unit_bounded (q : PTm n) (hq : Γ ⊢[PRAAx] qnormSq q ≐ fraction one one) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded q one one :=
  RationalArgmin.rationalLE_congr hq.eqSymm
    (RationalNonnegativePowers.fraction_congr (one_mul one) (one_mul one)).eqSymm
    (RationalArgmin.reflexive (fraction one one))

def output (q j k : PTm n) : PTm n :=
  pairT (power q (j+k)) (pairT (power (power q j) k) (pairT (power q j) (power q k)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (q j k : PTm n) : PTm n := ap3 outputF q j k

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (q j k : PTm n) :
    Syn.subst σ (output q j k) = output (Syn.subst σ q) (Syn.subst σ j) (Syn.subst σ k) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (q j k : PTm n) :
    Syn.subst σ (run q j k) = run (Syn.subst σ q) (Syn.subst σ j) (Syn.subst σ k) := by simp [run]

theorem program_at (q j k : PTm n) : Γ ⊢[PRAAx] run q j k ≐ output q j k := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![q,j,k]
theorem returned_sum_power (q j k : PTm n) : Γ ⊢[PRAAx] fstT (run q j k) ≐ power q (j+k) :=
  (congrFst (program_at q j k)).eqTrans (fst_pair _ _)
theorem returned_composed_power (q j k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run q j k)) ≐ power (power q j) k :=
  (congrFst ((congrSnd (program_at q j k)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_left_power (q j k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run q j k))) ≐ power q j :=
  (congrFst ((congrSnd ((congrSnd (program_at q j k)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_right_power (q j k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run q j k))) ≐ power q k :=
  (congrSnd ((congrSnd ((congrSnd (program_at q j k)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem rational_power_add_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (power (var 0) (var 1+var 2) ≐ qmul (power (var 0) (var 1)) (power (var 0) (var 2))) :=
  closeUniv 3 (power_add _ _ _)
theorem rational_power_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (power (power (var 0) (var 1)) (var 2) ≐ power (var 0) (var 1*var 2)) :=
  closeUniv 3 (power_composition _ _ _)
theorem rational_power_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (power (qmul (var 0) (var 1)) (var 2) ≐ qmul (power (var 0) (var 2)) (power (var 1) (var 2))) :=
  closeUniv 3 (power_product _ _ _)
theorem rational_unit_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qnormSq (var 0) ≐ fraction one one ⟶ qnormSq (power (var 0) (var 1)) ≐ fraction one one) :=
  closeUniv 2 (.impI (unit_power _ _ Prf.hyp0))
theorem rational_unit_bounded_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qnormSq (var 0) ≐ fraction one one ⟶ GaussianRationalMetric.bounded (var 0) one one) :=
  closeUniv 1 (.impI (unit_bounded _ Prf.hyp0))
theorem rational_power_square_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (canonical (var 0) ⟶ power (var 0) two ≐ qmul (var 0) (var 0)) :=
  closeUniv 1 (.impI (power_two _ Prf.hyp0))
theorem rational_multiplication_commutative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qmul (var 0) (var 1) ≐ qmul (var 1) (var 0)) := closeUniv 2 (qmul_commutative _ _)
theorem rational_power_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2) ⋏
      (fstT (run (var 0) (var 1) (var 2)) ≐ power (var 0) (var 1+var 2) ⋏
        (fstT (sndT (run (var 0) (var 1) (var 2))) ≐ power (var 0) (var 1*var 2) ⋏
          (fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ power (var 0) (var 1) ⋏
            sndT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ power (var 0) (var 2))))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_sum_power _ _ _)
    (.andI ((returned_composed_power _ _ _).eqTrans (power_composition _ _ _))
      (.andI (returned_left_power _ _ _) (returned_right_power _ _ _)))))

end LeanProofs.IPRA.Analysis.GaussianRationalPowerAlgebra
