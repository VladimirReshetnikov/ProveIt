import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.WeightedSums.GaussianRationalDerivativeWeights
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalL1Algebra
import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowers
import IPRADerivations.Analysis.Barnes.TailControl.BarnesCutoff
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianDescentClockArithmetic

/-!
# The original rational derivative sum and its exact ceiling mesh

The actual rational finite sum reads the original descending coefficients,
not a uniform coefficient bound. Its value is proved equal to the cleared
native derivative sum. A native maximum constructs max(1,sum), and the
existing actual integer-ceiling program supplies the source mesh.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianRationalDerivativeSum

open_ipra
open GaussianRationalVariableHornerBudget (denominator coefficient denominator_positive coefficient_represents)
open GaussianRationalDerivativeWeights (weight prefixSum total)
open GaussianRationalHorner (scalar_congr scalar_add_same)
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open GaussianRationalL1 (qL1 qL1_represents)
open RationalArithmetic (represents)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def multiplier (N U i : PTm n) : PTm n := monus N i*pw U (pred (monus N i))
def term (C N U i : PTm n) : PTm n := RationalArithmetic.multiply (fraction (multiplier N U i) one) (qL1 (entry C i))
def data (C N U : PTm n) : PTm n := GaussianRationalDerivativeWeights.data C N U
def body : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def partialSum (C N U k : PTm n) : PTm n := RationalFiniteSum.sum body k (data C N U)
def derivativeSum (C N U : PTm n) : PTm n := partialSum C N U N
def numerator (C N U : PTm n) : PTm n := BarnesCutoff.maximum (denominator C) (total C N U)
def L (C N U : PTm n) : PTm n := fraction (numerator C N U) (denominator C)
def four : PTm n := two*two
def mesh (C N U p q : PTm n) : PTm n := GaussianDescentClockArithmetic.ceiling (four*numerator C N U*q) (denominator C*p)

ipra_subst multiplier
ipra_subst term
ipra_subst data
ipra_subst partialSum
ipra_subst derivativeSum
ipra_subst numerator [BarnesCutoff.maximum]
ipra_subst L
ipra_subst four
ipra_subst mesh

theorem term_congr {C D N K U V i j : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ K)
    (hU : Γ ⊢[PRAAx] U ≐ V) (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx] term C N U i ≐ term D K V j := by
  ipra_congr (term (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hC, hN, hU, hi]
theorem body_at (C N U i : PTm n) : Γ ⊢[PRAAx] inst2 body i (data C N U) ≐ term C N U i := by
  simp only [body,inst2,subst_term,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact term_congr (fst_pair _ _) (snd_pair _ _).fstE
    (snd_pair _ _).sndE (.eqRefl _)
theorem term_represents (C N U i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx]
    represents (term C N U i) (ZT.ofNat (weight C N U i)) (denominator C) := by
  have prod : Γ ⊢[PRAAx] represents (term C N U i)
      (ZT.ofNat (multiplier N U i)*ZT.ofNat (coefficient C i)) (one*denominator C) :=
    RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (fraction_represents (multiplier N U i) one (le_refl one))
    (qL1_represents _ _ _ (denominator_positive C) (coefficient_represents C i hi))
  refine scalar_congr (.eqRefl _) ?_ (one_mul _) prod
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  unfold multiplier weight coefficient
  ipra_simps
  ring

theorem partial_zero (C N U : PTm n) : Γ ⊢[PRAAx] partialSum C N U zero ≐ RationalIntegerNormalization.integerCode (ZT.natLit 0) :=
  RationalFiniteSum.sum_zero _ _
theorem partial_succ (C N U k : PTm n) : Γ ⊢[PRAAx]
    partialSum C N U (succ k) ≐ RationalArithmetic.add (partialSum C N U k) (term C N U k) :=
  (RationalFiniteSum.sum_succ _ _ _).eqTrans (RationalAlgebra.add_congr (.eqRefl _) (body_at C N U k))

def prefixLaw (C N U k : PTm n) : Fm PTm n := le k (length C) ⟶
  represents (partialSum C N U k) (ZT.ofNat (prefixSum C N U k)) (denominator C)
ipra_subst prefixLaw

theorem prefix_zero_represents (C N U : PTm n) : Γ ⊢[PRAAx]
    represents (partialSum C N U zero) (ZT.ofNat (prefixSum C N U zero)) (denominator C) := by
  have zeroCode : Γ ⊢[PRAAx] fraction zero (denominator C) ≐ RationalIntegerNormalization.integerCode (ZT.natLit 0) := by
    apply RationalIntegerNormalization.normalize_integer _ _ _ (denominator_positive C)
    ipra_lc
  have hz := scalar_congr zeroCode (.eqRefl _) (.eqRefl _) (fraction_represents zero (denominator C) (denominator_positive (Γ := Γ) C))
  refine scalar_congr (partial_zero C N U).eqSymm ?_ (.eqRefl _) hz
  apply ZT.derive
  simp only [ZT.toZ_ofNat]
  exact (natEq (GaussianRationalDerivativeWeights.prefix_zero (Γ := Γ) C N U)).symm

theorem prefix_step (C N U k : PTm n) (hk : Γ ⊢[PRAAx] lt k (length C))
    (ih : Γ ⊢[PRAAx] represents (partialSum C N U k) (ZT.ofNat (prefixSum C N U k)) (denominator C)) : Γ ⊢[PRAAx]
    represents (partialSum C N U (succ k)) (ZT.ofNat (prefixSum C N U (succ k))) (denominator C) := by
  have sum := scalar_add_same _ _ _ _ _ (denominator_positive C) ih (term_represents C N U k hk)
  refine scalar_congr (partial_succ C N U k).eqSymm ?_ (.eqRefl _) sum
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_ofNat]
  rw [natEq (GaussianRationalDerivativeWeights.prefix_succ (Γ := Γ) C N U k)]
  ipra_simps

theorem prefix_represents (C N U k : PTm n) (hk : Γ ⊢[PRAAx] le k (length C)) : Γ ⊢[PRAAx]
    represents (partialSum C N U k) (ZT.ofNat (prefixSum C N U k)) (denominator C) := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift N) (Syn.shift U) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_prefixLaw]
    · exact .impI (prefix_zero_represents C N U).wk
    · refine .impI ?_
      exact prefix_step _ _ _ _ Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw C N U k := by simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem derivative_represents (C N U : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    represents (derivativeSum C N U) (ZT.ofNat (total C N U)) (denominator C) :=
  prefix_represents C N U N (le_congr (.eqRefl _) hLen.eqSymm (le_succ_self _))

theorem derivative_value (C N U : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    derivativeSum C N U ≐ fraction (total C N U) (denominator C) := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalFiniteSum.sum_well_formed _ _ _)
    (RationalNormalForm.normalize_well_formed _ _ (denominator_positive C)) (derivative_represents C N U hLen)
    (fraction_represents _ _ (denominator_positive C)) (denominator_positive C) (denominator_positive C)
  exact .eqRefl _

theorem denominator_le_numerator (C N U : PTm n) : Γ ⊢[PRAAx] le (denominator C) (numerator C N U) := BarnesCutoff.maximum_left _ _
theorem total_le_numerator (C N U : PTm n) : Γ ⊢[PRAAx] le (total C N U) (numerator C N U) := BarnesCutoff.maximum_right _ _
theorem numerator_positive (C N U : PTm n) : Γ ⊢[PRAAx] le one (numerator C N U) := le_trans (denominator_positive C) (denominator_le_numerator C N U)

theorem L_one_bound (C N U : PTm n) : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fraction one one) (L C N U) :=
  fraction_order _ _ _ _ (le_refl _) (denominator_positive C)
    (le_congr (by ipra_ring) (by ipra_ring) (denominator_le_numerator C N U))
theorem L_derivative_bound (C N U : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (derivativeSum C N U) (L C N U) := by
  apply RationalArgmin.rationalLE_congr (derivative_value C N U hLen).eqSymm (.eqRefl _)
  exact fraction_order _ _ _ _ (denominator_positive C) (denominator_positive C)
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right _ (total_le_numerator C N U)))

theorem L_when_small (C N U : PTm n) (h : Γ ⊢[PRAAx] le (total C N U) (denominator C)) : Γ ⊢[PRAAx]
    L C N U ≐ fraction one one := by
  have value : Γ ⊢[PRAAx] numerator C N U ≐ denominator C := BarnesCutoff.maximum_of_left h
  have same := RationalNonnegativePowers.fraction_congr value (.eqRefl (denominator C))
  refine same.eqTrans ?_
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ (denominator_positive C))
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (fraction_represents _ _ (denominator_positive C)) (fraction_represents _ _ (le_refl one))
    (denominator_positive C) (le_refl one)
  ipra_lc

theorem L_when_large (C N U : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (h : Γ ⊢[PRAAx] le (denominator C) (total C N U)) : Γ ⊢[PRAAx]
    L C N U ≐ derivativeSum C N U :=
  (RationalNonnegativePowers.fraction_congr (BarnesCutoff.maximum_of_right h) (.eqRefl _)).eqTrans (derivative_value C N U hLen).eqSymm

theorem L_least (C N U A B : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hOne : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fraction one one) (fraction A B))
    (hSum : Γ ⊢[PRAAx] RationalArgmin.rationalLE (derivativeSum C N U) (fraction A B)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (L C N U) (fraction A B) := by
  refine .orE (le_total (total C N U) (denominator C)) ?_ ?_
  · exact RationalArgmin.rationalLE_congr (L_when_small C N U Prf.hyp0).eqSymm (.eqRefl _) hOne.wk
  · exact RationalArgmin.rationalLE_congr (L_when_large C N U hLen.wk Prf.hyp0).eqSymm (.eqRefl _) hSum.wk

theorem mesh_budget (C N U p q : PTm n) (hp : Γ ⊢[PRAAx] le one p) : Γ ⊢[PRAAx]
    le (four*numerator C N U*q) (denominator C*p*mesh C N U p q) :=
  GaussianDescentClockArithmetic.ceiling_lower _ _ (GaussianRationalHorner.positive_product _ _ (denominator_positive C) hp)

theorem mesh_least (C N U p q K : PTm n) (hp : Γ ⊢[PRAAx] le one p)
    (hK : Γ ⊢[PRAAx] le (four*numerator C N U*q) (denominator C*p*K)) : Γ ⊢[PRAAx]
    le (mesh C N U p q) K :=
  GaussianDescentClockArithmetic.ceiling_least _ _ _ (GaussianRationalHorner.positive_product _ _ (denominator_positive C) hp) hK

theorem mesh_positive (C N U p q : PTm n) (hp : Γ ⊢[PRAAx] le one p) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    le one (mesh C N U p q) := by
  have num : Γ ⊢[PRAAx] le one (four*numerator C N U*q) :=
    GaussianRationalHorner.positive_product _ _
      (GaussianRationalHorner.positive_product _ _ GaussianDescentClockArithmetic.four_positive (numerator_positive C N U)) hq
  refine .orE (zero_or_succ (mesh C N U p q)) ?_ ?_
  · have bad : (mesh C N U p q ≐ zero) :: Γ ⊢[PRAAx] le one zero :=
      le_trans num.wk (le_congr (.eqRefl _) ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)) (mesh_budget C N U p q hp.wk))
    exact succ_ne_zero' _ ((monus_zero one).eqSymm.eqTrans bad)
  · exact Order.zero_lt_of_eq_succ Prf.hyp0

theorem mesh_variation_budget (C N U p q : PTm n) (hp : Γ ⊢[PRAAx] le one p) : Γ ⊢[PRAAx]
    le (total C N U*(four*q)) (p*(denominator C*mesh C N U p q)) := by
  have enlarge : Γ ⊢[PRAAx] le (total C N U*(four*q)) (four*numerator C N U*q) :=
    le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right (four*q) (total_le_numerator C N U))
  exact le_trans enlarge (le_congr (.eqRefl _) (by ipra_ring) (mesh_budget C N U p q hp))

theorem mesh_evaluation_bound (C N U z w p q : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hz : Γ ⊢[PRAAx] GaussianRationalMetric.bounded z U one)
    (hw : Γ ⊢[PRAAx] GaussianRationalMetric.bounded w U one)
    (hp : Γ ⊢[PRAAx] le one p) (hq : Γ ⊢[PRAAx] le one q)
    (hNear : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded z w one (mesh C N U p q)) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (GaussianRationalHorner.evaluate C z) (GaussianRationalHorner.evaluate C w) p (four*q) := by
  have hm := mesh_positive C N U p q hp hq
  have full := GaussianRationalDerivativeWeights.evaluation_bound C N U z w one (mesh C N U p q) hLen hz hw hm hNear
  have simplified := GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] total C N U*one ≐ total C N U) (.eqRefl _) full
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (denominator_positive C) hm)
    (GaussianRationalHorner.positive_product _ _ GaussianDescentClockArithmetic.four_positive hq)
    (mesh_variation_budget C N U p q hp) simplified

def output (C N U p q : PTm n) : PTm n := pairT (L C N U)
  (pairT (derivativeSum C N U) (pairT (mesh C N U p q) (pairT (numerator C N U) (denominator C))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (C N U p q : PTm n) : PTm n := PTm.app outputF ![C,N,U,p,q]
ipra_subst output
ipra_subst run
theorem program_at (C N U p q : PTm n) : Γ ⊢[PRAAx] run C N U p q ≐ output C N U p q := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,U,p,q]
theorem returned_L (C N U p q : PTm n) : Γ ⊢[PRAAx] fstT (run C N U p q) ≐ L C N U :=
  (program_at C N U p q).fstE
theorem returned_sum (C N U p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N U p q)) ≐ derivativeSum C N U :=
  (congrFst (congrSnd (program_at C N U p q))).eqTrans (snd_pair _ _).fstE
theorem returned_mesh (C N U p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N U p q))) ≐ mesh C N U p q :=
  (congrFst (congrSnd (congrSnd (program_at C N U p q)))).eqTrans
    ((congrFst (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _).fstE)

theorem actual_original_derivative_term_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inst2 body (var 3) (data (var 0) (var 1) (var 2)) ≐ RationalArithmetic.multiply
      (fraction (monus (var 1) (var 3)*pw (var 2) (pred (monus (var 1) (var 3)))) one) (qL1 (entry (var 0) (var 3)))) :=
  closeUniv 4 (body_at _ _ _ _)
theorem actual_original_derivative_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ derivativeSum (var 0) (var 1) (var 2) ≐ fraction (total (var 0) (var 1) (var 2)) (denominator (var 0))) :=
  closeUniv 3 (.impI (derivative_value _ _ _ Prf.hyp0))
theorem actual_L_maximum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶
      (RationalArgmin.rationalLE (fraction one one) (L (var 0) (var 1) (var 2)) ⋏
        RationalArgmin.rationalLE (derivativeSum (var 0) (var 1) (var 2)) (L (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.andI (L_one_bound _ _ _) (L_derivative_bound _ _ _ Prf.hyp0)))
theorem actual_L_maximum_least_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ RationalArgmin.rationalLE (fraction one one) (fraction (var 3) (var 4)) ⟶
      RationalArgmin.rationalLE (derivativeSum (var 0) (var 1) (var 2)) (fraction (var 3) (var 4)) ⟶
        RationalArgmin.rationalLE (L (var 0) (var 1) (var 2)) (fraction (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (L_least _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_source_mesh_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le one (var 4) ⟶ (le one (mesh (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      le (four*numerator (var 0) (var 1) (var 2)*var 4) (denominator (var 0)*var 3*mesh (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (.impI (.andI (mesh_positive _ _ _ _ _ Prf.hyp1 Prf.hyp0) (mesh_budget _ _ _ _ _ Prf.hyp1))))
theorem actual_source_mesh_least_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le (four*numerator (var 0) (var 1) (var 2)*var 4) (denominator (var 0)*var 3*var 5) ⟶
      le (mesh (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (mesh_least _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_source_mesh_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 1) ⟶ GaussianRationalMetric.bounded (var 3) (var 2) one ⟶
      GaussianRationalMetric.bounded (var 4) (var 2) one ⟶ le one (var 5) ⟶ le one (var 6) ⟶
      GaussianRationalMetric.distanceBounded (var 3) (var 4) one (mesh (var 0) (var 1) (var 2) (var 5) (var 6)) ⟶
      GaussianRationalMetric.distanceBounded (GaussianRationalHorner.evaluate (var 0) (var 3))
        (GaussianRationalHorner.evaluate (var 0) (var 4)) (var 5) (four*var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI (mesh_evaluation_bound _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))
theorem actual_source_derivative_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalDerivativeSum
