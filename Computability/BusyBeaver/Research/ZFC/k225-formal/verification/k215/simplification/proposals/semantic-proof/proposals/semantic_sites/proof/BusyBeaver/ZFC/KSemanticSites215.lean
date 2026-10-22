import BusyBeaver.ZFC.KDecoderPrefix215

/-!
Semantic coverage for K215 from the maintained exact decoder-prefix theorem.
This module is a generic integration boundary. It does not assert that the
primitive families have already been proved, and contains no assumptions hidden
as axioms: `PrimitiveContracts` is an explicit hypothesis of its theorems.
Requires the accompanying KSim refactor.
-/
namespace SetTheory.BusyBeaver.ZFC.KSemanticSites215
open KZip KRuntimeCore KSim RegisterPath RMBisim SiteCoverage
open KDecoderPrefix215 DecoderSourceBinding DecoderPaths K215Decoder

/-- Every routed primitive port must implement its full source continuation.
The source word is retained in the obligation, even when physical entry states
or the decoder's two-bit role suffixes coincide. -/
def PrimitiveContracts : Prop :=
  ∀ {word : List Bool} {e : RegisterPath.Edge}, LeafAt KSource215.t215 word e →
    ∀ pre bit q op arg,
      word = pre ++ [bit] → e = primitive op arg →
      RoutedEntry formal sourceNodes roles 0 word q bit op arg →
      PortContract KTableCore.tm215 (leafPort pre bit q) word e

/-- Only the finite source shape is reduced; no symbolic TM executor runs here. -/
theorem shape_checked : allSites (fun _ _ => true) [] KSource215.t215 = true := by
  decide +kernel

/-- Decoder-prefix composition supplies the exact old edge specification. -/
theorem leaf_contract (contracts : PrimitiveContracts)
    {word : List Bool} {e : RegisterPath.Edge} (leaf : LeafAt KSource215.t215 word e) :
    EdgeContract KTableCore.tm215 word e := by
  obtain ⟨pre, bit, q, op, arg, hword, hedge, hroute, hprefix⟩ := leaf_prefix leaf
  apply PortContract.precompose (port := leafPort pre bit q)
  · intro n vs
    obtain ⟨steps, _, _, run⟩ := hprefix n vs
    exact ⟨steps, run⟩
  · exact contracts leaf pre bit q op arg hword hedge hroute

/-- Once parametric primitive families are supplied, no `checkEdge=true`
conclusion is needed to feed the register-machine simulation. -/
theorem covered (contracts : PrimitiveContracts) :
    SemanticCovered KTableCore.tm215 KSource215.p215 :=
  SemanticCovered.of_leaves KSource215.t215_eq shape_checked (leaf_contract contracts)

/-- Directly usable machine/source equivalence with explicit primitive input. -/
theorem halts_iff (contracts : PrimitiveContracts)
    (haltRows : ∀ b, KTableCore.tm215 230 b = none)
    {c : Configuration} {T : Conf} (related : Rel KSource215.p215 c T) :
    RegisterPath.Halts KSource215.p215 c ↔ KZip.Halts KTableCore.tm215 T :=
  Semantic.halts_iff (covered contracts) haltRows related

#print axioms shape_checked
#print axioms leaf_contract
#print axioms covered
#print axioms halts_iff
end SetTheory.BusyBeaver.ZFC.KSemanticSites215
