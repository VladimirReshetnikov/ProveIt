import PA196PANegationBound
import DiophantineConsistency.PRAWitnessPR
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-! Numeric growth bounds for arithmetic-language formula negation and
implication, useful for the exact induction-body graph. These are all-model
IΣ₁ value bounds, not yet candidate-PRA witness bounds for those graphs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace PA196InductionImpGrowth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open DiophantineConsistency.PRAWitnessCodeGrowth DiophantineConsistency.PRAWitnessPR
open DiophantineConsistency.PRAWitnessCalculus DiophantineConsistency.PRAWitnessArithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.PRAWitnessTransfer
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem lift_tau_id {p P y : V} (hp : p + 2 ≤ P)
    (hy : y ≤ tau (p + 8) (2 * p + 6)) : y ≤ tau (P + 8) (2 * P + 2) :=
  le_trans hy (tau_mono (add_le_add (le_trans le_self_add hp) le_rfl) (depth_step hp))

theorem neg_le : ∀ p : V, IsUFormula ℒₒᵣ p → neg ℒₒᵣ p ≤ tau (p + 8) (2 * p + 6) := by
  refine IsUFormula.ISigma1.sigma1_succ_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k R v hR hv
    rw [neg_rel hR hv]
    set P := ^rel k R v
    have h := code4_le_tau (le_tau_of P 1 0 (by simpa using small_le P (n := 1) (by norm_num)))
      (le_tau_of P k 0 (le_trans (arity_lt_rel k R v).le le_self_add))
      (le_tau_of P R 0 (le_trans (r_lt_rel k R v).le le_self_add))
      (le_tau_of P v 0 (le_trans (v_lt_rel k R v).le le_self_add))
    exact le_trans (by simpa [qqNRel] using h) (tau_mono le_rfl (depth6_le _))
  · intro k R v hR hv
    rw [neg_nrel hR hv]
    set P := ^nrel k R v
    have h := code4_le_tau (le_tau_of P 0 0 (by simp))
      (le_tau_of P k 0 (le_trans (arity_lt_nrel k R v).le le_self_add))
      (le_tau_of P R 0 (le_trans (r_lt_nrel k R v).le le_self_add))
      (le_tau_of P v 0 (le_trans (v_lt_nrel k R v).le le_self_add))
    exact le_trans (by simpa [qqRel] using h) (tau_mono le_rfl (depth6_le _))
  · rw [neg_verum]
    have h := code2_le_tau (le_tau_of (^⊤ : V) 3 0 (by simpa using small_le (^⊤ : V) (n := 3) (by norm_num)))
      (le_tau_of (^⊤ : V) 0 0 (by simp))
    exact le_trans (by simpa [qqFalsum] using h) (tau_mono le_rfl (depth2_le _))
  · rw [neg_falsum]
    have h := code2_le_tau (le_tau_of (^⊥ : V) 2 0 (by simpa using small_le (^⊥ : V) (n := 2) (by norm_num)))
      (le_tau_of (^⊥ : V) 0 0 (by simp))
    exact le_trans (by simpa [qqVerum] using h) (tau_mono le_rfl (depth2_le _))
  · intro p q hp hq ihp ihq
    rw [neg_and hp hq]
    set P := p ^⋏ q
    have hp2 := add_two_le_and_left p q; have hq2 := add_two_le_and_right p q
    have hnp : neg ℒₒᵣ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have hnq : neg ℒₒᵣ q ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hq2 ihq
    have h := code3_le_tau (le_tau_of' 5 hnp) hnp hnq
    exact le_trans (by simpa [qqOr] using h) (tau_mono le_rfl (depth_three P))
  · intro p q hp hq ihp ihq
    rw [neg_or hp hq]
    set P := p ^⋎ q
    have hp2 := add_two_le_or_left p q; have hq2 := add_two_le_or_right p q
    have hnp : neg ℒₒᵣ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have hnq : neg ℒₒᵣ q ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hq2 ihq
    have h := code3_le_tau (le_tau_of' 4 hnp) hnp hnq
    exact le_trans (by simpa [qqAnd] using h) (tau_mono le_rfl (depth_three P))
  · intro p hp ihp
    rw [neg_all hp]
    set P := ^∀ p
    have hp2 := add_two_le_all p
    have hnp : neg ℒₒᵣ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have h := code2_le_tau (le_tau_of' 7 hnp) hnp
    exact le_trans (by simpa [qqExs] using h) (tau_mono le_rfl (depth_two P))
  · intro p hp ihp
    rw [neg_ex hp]
    set P := ^∃ p
    have hp2 := add_two_le_exs p
    have hnp : neg ℒₒᵣ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have h := code2_le_tau (le_tau_of' 6 hnp) hnp
    exact le_trans (by simpa [qqAll] using h) (tau_mono le_rfl (depth_two P))

/-- Uniform bound includes non-formula inputs, on which negation is zero. -/
theorem neg_all (X T : V) (h : X ≤ T) : neg ℒₒᵣ X ≤ tau (T + 8) (2 * T + 6) := by
  by_cases hX : IsUFormula ℒₒᵣ X
  · exact le_trans (neg_le X hX) (tau_mono (add_le_add h le_rfl) (add_le_add (mul_le_mul' le_rfl h) le_rfl))
  · rw [neg_not_uformula hX]; simp

/-- Uniform growth bound for an implication in the arithmetic language. -/
theorem imp_all {a b T : V} (ha : a ≤ T) (hb : b ≤ T) :
    imp ℒₒᵣ a b ≤ tau (T + 8) (2 * T + 10) := by
  have hb' : b ≤ tau (T + 8) (2 * T + 6) := le_trans (le_trans hb le_self_add) (le_tau _ _)
  have h := code3_le_tau (small_le_tau (T + 8) (2 * T + 6) (n := 5) (by norm_num)) (neg_all a T ha) hb'
  unfold imp
  exact le_trans (by simpa [qqOr] using h) (tau_mono le_rfl (le_of_eq (by ring)))

section candidateModel
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The disjunction-code conjunct appearing in every arithmetic implication
graph, including all three occurrences in `indBodyValGraph`. -/
noncomputable def actualImpOr : ArithmeticSemisentence 4 :=
  match (impGraph ℒₒᵣ).val with
  | .exs (.and _ graph) => graph
  | _ => ⊥

theorem actualImpOr_exact : actualImpOr = Rewriting.subst qqOrDef.val ![#1,#0,#3] := by rfl

/-- An unconditional bound for the exact disjunction subgraph; this is not
a bound for the surrounding negation graph or the whole implication graph. -/
theorem wb_actualImpOr : WB M actualImpOr := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [actualImpOr_exact]
  exact wb_rew _ (wb_qqOrDef (M := M))

/-- The arithmetic implication graph's remaining witness obligation is the
negation graph; its disjunction and intermediate existential are discharged. -/
theorem wb_impGraph_of_negGraph (hneg : WB M (negGraph ℒₒᵣ).val) :
    WB M (impGraph ℒₒᵣ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqOrDef (M := M)
  simp only [impGraph, HierarchySymbol.Semiformula.val_mkSigma]
  exact wb_exs_poly _ (by simp) ‘#0’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      simpa [h'.2] using le_of_lt (lt_or_left u (e 2)), h⟩) (by wb_auto)

/-- The arithmetic negation-graph bound discharges the last premise. -/
theorem wb_impGraph : WB M (impGraph ℒₒᵣ).val :=
  wb_impGraph_of_negGraph (PA196PANegationBound.wb_negGraph)

#print axioms wb_impGraph
#print axioms wb_impGraph_of_negGraph
#print axioms wb_actualImpOr
end candidateModel

#print axioms neg_le
#print axioms neg_all
#print axioms imp_all
end PA196InductionImpGrowth
