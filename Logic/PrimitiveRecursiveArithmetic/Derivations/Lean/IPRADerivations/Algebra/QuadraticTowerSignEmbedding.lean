import IPRADerivations.Algebra.QuadraticTowerScalarArrays
import IPRADerivations.Algebra.QuadraticTowerSignCoherence

/-!
# Actual scalar and zero sign queries at numerical tower depth

Source `isoperimetric_ipra.tex`, sections2.3 and11.1. The original rational
scalar is represented at coefficient0 in an actual width2^h array. Backward
budget inflation and a guarded QF induction through the SAME sign state
prove scalar and zero reflection. The upper half is actually zero, so these
conclusions hold for every numerical radicand array D, including redundant
extensions. General paired-domain sign correctness and ordered quotient
laws remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerSignEmbedding

open_ipra
open LeanProofs.IPRA.Analysis
open QuadraticTowerScalarArrays (zeroArray scalarArray zeroScalar)
open QuadraticTowerScalarBudget (height)
open QuadraticTowerMultiplicationTable (budget demandF)
open QuadraticTowerMultiplicationHeight (cap)
open QuadraticTowerSignCoherence (state)
open QuadraticTowerSignRecipe (read firstTag secondTag thirdTag recipe dispatch)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel_one sel_zero)
open LeanProofs.IPRA.Foundations.BoundedReflection

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem budget_inflation (h B D : PTm n) : Γ ⊢[PRAAx] le B (budget h B D) :=
  le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path (succ h)) B)
    (QuadraticTowerGrowth.path_growth_budget h B D B (le_refl B))

def floorLaw (H B D j : PTm n) : Fm PTm n :=
  le B (Foundations.BackwardDemand.backward demandF H B j D)
ipra_subst floorLaw
theorem backward_floor (H B D j : PTm n) : Γ ⊢[PRAAx] floorLaw H B D j := by
  have all : Γ ⊢[PRAAx] .all (floorLaw (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0)) := by
    ipra_qfind (le_QF _ _) [subst_floorLaw]
    · exact le_congr (.eqRefl _) (Foundations.BackwardDemand.backward_zero demandF H B D).eqSymm (le_refl B)
    · exact le_trans Prf.hyp0 (le_congr (.eqRefl _)
        (Foundations.BackwardDemand.backward_succ demandF _ _ _ _).eqSymm (budget_inflation _ _ _))
  simpa only [subst_floorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
theorem cap_floor (H B t D : PTm n) : Γ ⊢[PRAAx] le B (cap H B t D) :=
  backward_floor H B D (monus H t)

theorem read_cap_congr (h B C S A : PTm n) (hB : Γ ⊢[PRAAx] B ≐ C) : Γ ⊢[PRAAx]
    read h B S A ≐ read h C S A := by
  ipra_congr (read (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl h, hB, .eqRefl S, .eqRefl A]

theorem dispatch_b_zero_total (s t u : PTm n) (ht : Γ ⊢[PRAAx] t ≐ zero) : Γ ⊢[PRAAx]
    dispatch s t u ≐ s := by
  refine .orE (eqb_cases s zero) ?_ ?_
  · exact (sel_zero Prf.hyp0).eqTrans (sel_one (eqb_of_eq ht.wk))
  · exact ((sel_one Prf.hyp0).eqTrans
      (QuadraticTowerSignRecipe.tag_product_zero_left _ _ ht.wk)).eqTrans (eq_of_eqb Prf.hyp0).eqSymm

theorem zero_recipe (h B D S : PTm n)
    (hz : Γ ⊢[PRAAx] read h (budget h B D) S (zeroArray h) ≐ zero) : Γ ⊢[PRAAx]
    recipe h B D S (zeroArray (succ h)) ≐ zero := by
  have a : Γ ⊢[PRAAx] firstTag h B D S (zeroArray (succ h)) ≐ zero :=
    (QuadraticTowerSignRecipe.read_operand_congr _ _ _ _ _ (QuadraticTowerScalarArrays.left_zero h)).eqTrans hz
  have b : Γ ⊢[PRAAx] secondTag h B D S (zeroArray (succ h)) ≐ zero :=
    (QuadraticTowerSignRecipe.read_operand_congr _ _ _ _ _ (QuadraticTowerScalarArrays.right_zero h)).eqTrans hz
  exact (dispatch_b_zero_total _ _ _ b).eqTrans a

theorem scalar_recipe (h B D S q : PTm n)
    (hz : Γ ⊢[PRAAx] read h (budget h B D) S (zeroArray h) ≐ zero) : Γ ⊢[PRAAx]
    recipe h B D S (scalarArray (succ h) q) ≐ read h (budget h B D) S (scalarArray h q) := by
  have b : Γ ⊢[PRAAx] secondTag h B D S (scalarArray (succ h) q) ≐ zero :=
    (QuadraticTowerSignRecipe.read_operand_congr _ _ _ _ _ (QuadraticTowerScalarArrays.right_scalar h q)).eqTrans hz
  exact (dispatch_b_zero_total _ _ _ b).eqTrans
    (QuadraticTowerSignRecipe.read_operand_congr _ _ _ _ _ (QuadraticTowerScalarArrays.left_scalar h q))

theorem ground_zero (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    read zero B (QuadraticTowerSignTable.base B) (zeroArray zero) ≐ zero :=
  (QuadraticTowerSignCoherence.base_read_ground B _ (QuadraticTowerScalarArrays.zero_array_height _ _ hB)).eqTrans
    ((QuadraticTowerSignTable.ground_tag_proper _ _ (RationalArithmetic.recode_equal _)).eqTrans
      ((QuadraticTowerSignTable.ground_tag_congr (QuadraticTowerScalarArrays.zero_at_zero zero)).eqTrans
        ((QuadraticTowerSignTable.ground_tag_native zeroScalar).eqTrans QuadraticTowerScalarArrays.zero_native_tag)))

theorem ground_scalar (B q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] height q B) : Γ ⊢[PRAAx]
    read zero B (QuadraticTowerSignTable.base B) (scalarArray zero q) ≐ QuadraticTowerSignTable.groundTag q :=
  (QuadraticTowerSignCoherence.base_read_ground B _ (QuadraticTowerScalarArrays.scalar_array_height _ _ _ hB hq)).eqTrans
    ((QuadraticTowerSignTable.ground_tag_proper _ _ (RationalArithmetic.recode_equal _)).eqTrans
      ((QuadraticTowerSignTable.ground_tag_congr (QuadraticTowerScalarArrays.scalar_at_zero zero q)).eqTrans
        (QuadraticTowerSignTable.ground_tag_proper _ _ (RationalArithmetic.recode_equal q))))

def forwardLaw (H B D q t : PTm n) : Fm PTm n := le t H ⟶
  (read t (cap H B t D) (state H B t D) (zeroArray t) ≐ zero ⋏
    read t (cap H B t D) (state H B t D) (scalarArray t q) ≐ QuadraticTowerSignTable.groundTag q)
ipra_subst forwardLaw

theorem forward_zero (H B D q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] height q B) : Γ ⊢[PRAAx]
    forwardLaw H B D q zero := by
  have hK := le_trans hB (cap_floor H B zero D)
  have qK := QuadraticTowerScalarBudget.height_mono q B _ hq (cap_floor H B zero D)
  refine .impI (.andI ?_ ?_)
  · exact (QuadraticTowerSignCoherence.read_table_congr _ _ _ _ _ (QuadraticTowerSignCoherence.state_zero H B D)).eqTrans
      (ground_zero _ hK.wk)
  · exact (QuadraticTowerSignCoherence.read_table_congr _ _ _ _ _ (QuadraticTowerSignCoherence.state_zero H B D)).eqTrans
      (ground_scalar _ _ hK.wk qK.wk)

theorem forward_step (H B D q t : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] height q B)
    (ih : Γ ⊢[PRAAx] forwardLaw H B D q t) : Γ ⊢[PRAAx] forwardLaw H B D q (succ t) := by
  refine .impI ?_
  let Δ := le (succ t) H :: Γ
  have ht : Δ ⊢[PRAAx] lt t H := Prf.hyp0
  have previous := Prf.impE ih.wk (le_trans (le_succ_self t) ht)
  let K := cap H B (succ t) D
  let S := state H B t D
  have hK : Δ ⊢[PRAAx] le one K := le_trans hB.wk (cap_floor H B (succ t) D)
  have qK : Δ ⊢[PRAAx] height q K := QuadraticTowerScalarBudget.height_mono q B K hq.wk (cap_floor H B (succ t) D)
  have z : Δ ⊢[PRAAx] read t (budget t K D) S (zeroArray t) ≐ zero :=
    (read_cap_congr _ _ _ _ _ (QuadraticTowerMultiplicationHeight.cap_link H B t D ht).eqSymm).eqTrans (Prf.andE₁ previous)
  have a : Δ ⊢[PRAAx] read t (budget t K D) S (scalarArray t q) ≐ QuadraticTowerSignTable.groundTag q :=
    (read_cap_congr _ _ _ _ _ (QuadraticTowerMultiplicationHeight.cap_link H B t D ht).eqSymm).eqTrans (Prf.andE₂ previous)
  refine .andI ?_ ?_
  · exact (QuadraticTowerSignCoherence.read_table_congr _ _ _ _ _ (QuadraticTowerSignCoherence.state_succ H B t D)).eqTrans
      ((QuadraticTowerSignCoherence.step_read_normalized t K S D _ (QuadraticTowerScalarArrays.zero_array_height _ _ hK)).eqTrans
        ((QuadraticTowerSignTable.recipe_operand_congr _ _ _ _ _ _ (QuadraticTowerScalarArrays.normalized_zero _)).eqTrans
          (zero_recipe t K D S z)))
  · exact (QuadraticTowerSignCoherence.read_table_congr _ _ _ _ _ (QuadraticTowerSignCoherence.state_succ H B t D)).eqTrans
      ((QuadraticTowerSignCoherence.step_read_normalized t K S D _ (QuadraticTowerScalarArrays.scalar_array_height _ _ _ hK qK)).eqTrans
        ((QuadraticTowerSignTable.recipe_operand_congr _ _ _ _ _ _ (QuadraticTowerScalarArrays.normalized_scalar _ _)).eqTrans
          ((scalar_recipe t K D S q z).eqTrans a)))

theorem forward_all (H B D q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] height q B) : Γ ⊢[PRAAx]
    .all (forwardLaw (Syn.shift H) (Syn.shift B) (Syn.shift D) (Syn.shift q) (var 0)) := by
  refine PRA.qfInd _ (by simp [forwardLaw,Fm.QF,le]) ?_ ?_
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      forward_zero H B D q hB hq
  · simp only [subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
    have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
    have qh : Γ.map Fm.shift ⊢[PRAAx] height (Syn.shift q) (Syn.shift B) := by
      simpa [Fm.shift,Syn.shift] using hq.shift
    exact forward_step _ _ _ _ _ b.wk qh.wk Prf.hyp0

theorem query_equations (h B D q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] height q B) : Γ ⊢[PRAAx]
    (QuadraticTowerSignTable.query h B D (zeroArray h) ≐ zero ⋏
      QuadraticTowerSignTable.query h B D (scalarArray h q) ≐ QuadraticTowerSignTable.groundTag q) := by
  have gate : Γ ⊢[PRAAx] forwardLaw h B D q h := by
    simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all h B D q hB hq).allE h
  have terminal := Prf.impE gate (le_refl h)
  have final : Γ ⊢[PRAAx] cap h B h D ≐ B := Foundations.BackwardDemand.horizon_final demandF h B D
  exact .andI ((read_cap_congr _ _ _ _ _ final.eqSymm).eqTrans (Prf.andE₁ terminal))
    ((read_cap_congr _ _ _ _ _ final.eqSymm).eqTrans (Prf.andE₂ terminal))

theorem zero_query (h B D : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query h B D (zeroArray h) ≐ zero :=
  .andE₁ (query_equations h B D zeroScalar hB (QuadraticTowerScalarArrays.zero_height B hB))
theorem scalar_query (h B D q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] height q B) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query h B D (scalarArray h q) ≐ QuadraticTowerSignTable.groundTag q :=
  .andE₂ (query_equations h B D q hB hq)
theorem scalar_query_native (h B D q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] height q B) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query h B D (scalarArray h q) ≐
      QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf q) :=
  (scalar_query h B D q hB hq).eqTrans (QuadraticTowerSignTable.ground_tag_native q)

theorem scalar_query_proper (h B C D E q r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hC : Γ ⊢[PRAAx] le one C) (hq : Γ ⊢[PRAAx] height q B) (hr : Γ ⊢[PRAAx] height r C)
    (he : Γ ⊢[PRAAx] RationalArgmin.rationalEq q r) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query h B D (scalarArray h q) ≐ QuadraticTowerSignTable.query h C E (scalarArray h r) :=
  (scalar_query h B D q hB hq).eqTrans ((QuadraticTowerSignTable.ground_tag_proper q r he).eqTrans
    (scalar_query h C E r hC hr).eqSymm)

theorem returned_zero (h B D : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    fstT (QuadraticTowerSignTable.run h B D (zeroArray h)) ≐ zero :=
  (QuadraticTowerSignTable.returned_tag _ _ _ _).eqTrans (zero_query h B D hB)
theorem returned_scalar (h B D q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] height q B) : Γ ⊢[PRAAx]
    fstT (QuadraticTowerSignTable.run h B D (scalarArray h q)) ≐ QuadraticTowerSignTable.groundTag q :=
  (QuadraticTowerSignTable.returned_tag _ _ _ _).eqTrans (scalar_query h B D q hB hq)
theorem returned_scalar_native (h B D q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] height q B) : Γ ⊢[PRAAx]
    fstT (QuadraticTowerSignTable.run h B D (scalarArray h q)) ≐
      QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf q) :=
  (QuadraticTowerSignTable.returned_tag _ _ _ _).eqTrans (scalar_query_native h B D q hB hq)

def output (h B D q : PTm n) : PTm n := pairT (QuadraticTowerSignTable.query h B D (zeroArray h))
  (QuadraticTowerSignTable.query h B D (scalarArray h q))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (h B D q : PTm n) : PTm n := PTm.app outputF ![h,B,D,q]
ipra_subst output
ipra_subst run
theorem program_at (h B D q : PTm n) : Γ ⊢[PRAAx] run h B D q ≐ output h B D q := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![h,B,D,q]
theorem produced_zero (h B D q : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    fstT (run h B D q) ≐ zero :=
  (program_at h B D q).fstE.eqTrans (zero_query h B D hB)
theorem produced_scalar (h B D q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] height q B) : Γ ⊢[PRAAx]
    sndT (run h B D q) ≐ QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf q) :=
  (program_at h B D q).sndE.eqTrans (scalar_query_native h B D q hB hq)

theorem actual_sign_backward_cap_floor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 1) (cap (var 0) (var 1) (var 2) (var 3))) := closeUniv 4 (cap_floor _ _ _ _)
theorem actual_zero_upper_dispatch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (var 1 ≐ zero ⟶ dispatch (var 0) (var 1) (var 2) ≐ var 0) :=
  closeUniv 3 (.impI (dispatch_b_zero_total _ _ _ Prf.hyp0))
theorem actual_zero_tower_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (zeroArray (var 0)) ≐ zero) :=
  closeUniv 3 (.impI (zero_query _ _ _ Prf.hyp0))
theorem actual_scalar_tower_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ height (var 3) (var 1) ⟶
      QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (scalarArray (var 0) (var 3)) ≐
        QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf (var 3))) :=
  closeUniv 4 (.impI (.impI (scalar_query_native _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_zero_tower_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ fstT (QuadraticTowerSignTable.run (var 0) (var 1) (var 2) (zeroArray (var 0))) ≐ zero) :=
  closeUniv 3 (.impI (returned_zero _ _ _ Prf.hyp0))
theorem actual_returned_scalar_tower_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ height (var 3) (var 1) ⟶
      fstT (QuadraticTowerSignTable.run (var 0) (var 1) (var 2) (scalarArray (var 0) (var 3))) ≐
        QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf (var 3))) :=
  closeUniv 4 (.impI (.impI (returned_scalar_native _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_scalar_sign_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_scalar_sign_produced_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ height (var 3) (var 1) ⟶
      (fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ zero ⋏
        sndT (run (var 0) (var 1) (var 2) (var 3)) ≐ QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf (var 3)))) :=
  closeUniv 4 (.impI (.impI (.andI (produced_zero _ _ _ _ Prf.hyp1) (produced_scalar _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Algebra.QuadraticTowerSignEmbedding
