module
public import TemplateNthCore
public import MappingTemplateBridge
public import SeqTemplateBridge
public import FixActualBridge
public import PrimitivePair3Bridge
public import PrimitiveDomainBridge
public import PrimitiveUnderBridge
public import PrimitiveEdgeBridge
@[expose] public section
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

theorem constructed_mapping_to : ConstructedNth.mapping.toFoundation =
 (isMappingDef : ArithmeticSemisentence 1) := by
 rw [ConstructedNth.mapping,mappingTemplate_to,domain_to,member_to,edge_to]
 unfold standardMapping isMappingDef
 simp only [Bounding.HierarchySymbol.Semiformula.val_mkSigma,Arithmetic.ballIn,operator_subst]
 congr! 40
 · rename_i i
   fin_cases i <;> rfl
 · conv_rhs => rw [closed_subst_identity _ _ (by intro i; fin_cases i <;> rfl)]
   simp only [memRelOpr,Semiformula.Operator.operator,Rewriting.emb,Rew.emb_eq_id,
    ReflectiveRewriting.id_app]

theorem constructed_seq_to : ConstructedNth.seq.toFoundation =
 (seqDef : ArithmeticSemisentence 1) := by
 rw [ConstructedNth.seq,seqTemplate_to,constructed_mapping_to,domain_to,under_to]
 unfold standardSeq seqDef
 rfl

theorem constructed_length_to : ConstructedNth.length.toFoundation =
 (lhDef : ArithmeticSemisentence 2) := by
 rw [ConstructedNth.length,seqLengthTemplate_to,constructed_seq_to,domain_to,under_to]
 unfold standardSeqLength lhDef
 rfl

def standardPREdge : ArithmeticSemisentence 3 := “i s z. i ∼[s] z”
theorem constructed_edge_to : ConstructedNth.edge.toFoundation = standardPREdge := by
 rw [ConstructedNth.edge,prSub3_to,edge_to]
 unfold standardPREdge memRelOpr Semiformula.Operator.operator Rewriting.emb
 simp only [Rew.emb_eq_id,ReflectiveRewriting.id_app,Term.to_bvar]
 rfl

theorem constructed_zero_to : fixZeroTemplate.toFoundation =
 (Nth.blueprint.prBlueprint.zero : ArithmeticSemisentence 1) := by
 apply Function.LeftInverse.injective Formula.to_from
 with_unfolding_all decide +kernel

theorem constructed_succ_to : ConstructedNth.succ.toFoundation =
 (Nth.blueprint.prBlueprint.succ : ArithmeticSemisentence 3) := actualFixSucc_to
theorem constructed_cseq_to : ConstructedNth.cseq.toFoundation =
 (Nth.blueprint.prBlueprint.cseqDef : ArithmeticSemisentence 1) := by
 rw [ConstructedNth.cseq,prCSeqTemplate_to,constructed_zero_to,constructed_seq_to,
  constructed_succ_to,constructed_edge_to,constructed_length_to]
 unfold standardPRCSeq PR.Blueprint.cseqDef standardPREdge
 simp only [Bounding.HierarchySymbol.Semiformula.val_mkSigma,operator_subst]
 congr! 40
 all_goals first
  | rfl
  | (apply Rew.ext; · intro i; fin_cases i <;> rfl; · intro x; exact Empty.elim x)
  | (funext i; fin_cases i <;> rfl)
  | (rename_i i; fin_cases i <;> rfl)
theorem constructed_result_to : ConstructedNth.result.toFoundation =
 (Nth.blueprint.prBlueprint.resultDef : ArithmeticSemisentence 2) := by
 rw [ConstructedNth.result,prResultTemplate_to,constructed_cseq_to,constructed_edge_to]
 unfold standardPRResult PR.Blueprint.resultDef standardPREdge
 simp only [Bounding.HierarchySymbol.Semiformula.val_mkSigma,operator_subst]
 congr! 20
 all_goals first
  | rfl
  | (apply Rew.ext; · intro i; fin_cases i <;> rfl; · intro x; exact Empty.elim x)
  | (funext i; fin_cases i <;> rfl)
  | (rename_i i; fin_cases i <;> rfl)

theorem constructed_graph_to : ConstructedNth.graph.toFoundation =
 (Nth.blueprint.fixpointDef : ArithmeticSemisentence 1) := by
 rw [ConstructedNth.graph,fixPointTemplate_to,member_to,constructed_result_to]
 unfold standardFixPoint Fixpoint.Blueprint.fixpointDef Fixpoint.Blueprint.limSeqDef
 change _ = (“x. ∃ s L, !Nth.blueprint.prBlueprint.resultDef L s ⋯ ∧ x ∈ L” : ArithmeticSemisentence 1)
 simp only [Bounding.HierarchySymbol.Semiformula.val_mkSigma,operator_subst]
 congr! 20
 all_goals first
  | rfl
  | (apply Rew.ext; · intro i; fin_cases i <;> rfl; · intro x; exact Empty.elim x)
  | (funext i; fin_cases i <;> rfl)
  | (rename_i i; fin_cases i <;> rfl)

/-- Closed exact syntax certificate, assembled from explicit primitive and
parameterized template certificates. No nthDef-equality hypothesis remains. -/
theorem constructed_nth_to : ConstructedNth.formula.toFoundation =
 (nthDef : ArithmeticSemisentence 3) := by
 rw [ConstructedNth.formula,nthTemplate_to,pair3_to,constructed_graph_to]
 unfold standardNth nthDef Nth.graphDef
 rfl
#print axioms constructed_result_to
#print axioms constructed_graph_to
#print axioms constructed_nth_to
#print axioms constructed_cseq_to
#print axioms constructed_mapping_to
#print axioms constructed_seq_to
#print axioms constructed_length_to
#print axioms constructed_edge_to
#print axioms constructed_zero_to
#print axioms constructed_succ_to
end PalomarPA
