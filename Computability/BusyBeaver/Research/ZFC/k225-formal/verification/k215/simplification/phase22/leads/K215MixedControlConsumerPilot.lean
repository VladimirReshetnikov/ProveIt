import K215ControlCoveragePilot
import BusyBeaver.ZFC.KSim

/-! Source-only pilot. Not compiled or adopted.
This consumer keeps its physical-contract proposition explicit. Instantiate it
with EXACTLY KSim.EdgeContract tm215 after rebasing the archived semantic consumer.
The quantified `framed` premise is a remaining producer obligation, not an axiom
or a claim that residual reachability already begins at dispatch.
-/
namespace SetTheory.BusyBeaver.ZFC.K215ControlCoveragePilot
open RegisterPath RMBisim SiteCoverage KControlRowsPilot
open KFrameContracts KFrameCallers KTableCore

/-- Skip only controls classified into the framed family. All other leaves
retain the original checkEdge, including BOTH decrement branches and halt. -/
def literalGate (Q : List Bool) (e : Edge) : Bool :=
  if isControl e && !(literalControl Q e) then true else KSim.checkEdge tm215 Q e

/-- Same quantifier shape as the archived KSim.SemanticCovered consumer. -/
def ContractCovered (C : List Bool → Edge → Prop) : Prop :=
  ∀ P, ∃ e d, walk KSource215.p215 (KSource215.p215.nnodes + 1)
    KSource215.p215.root P 0 = some (e, d) ∧ C (consume P d) e

/-- Exact all-outcome assembly boundary. `fallbacks` rejects failed decoder
branches and checks every nonframed outcome. Framed caller validity alone would
not suffice; control_leaf_cases supplies the exact source-family coverage. -/
theorem covered_by_framed_and_literal
    (C : List Bool → Edge → Prop)
    (framed : ∀ c, c ∈ callers → C c.word (action (metaAt c.templateIndex)))
    (literal : ∀ Q e, KSim.checkEdge tm215 Q e = true → C Q e)
    (fallbacks : allSites literalGate [] KSource215.t215 = true) :
    ContractCovered C := by
  intro P
  obtain ⟨e, d, hw⟩ := allSites_walk_total literalGate KSource215.p215
    KSource215.t215 KSource215.t215_eq fallbacks P
  have hgate := allSites_walk literalGate KSource215.p215 KSource215.t215
    KSource215.t215_eq fallbacks P e d hw
  refine ⟨e, d, hw, ?_⟩
  cases he : isControl e with
  | false =>
      exact literal _ _ (by simpa [literalGate, he] using hgate)
  | true =>
      rcases control_leaf_cases (walk_leaf hw) he with hLit | ⟨c, hc, hword, haction⟩
      · exact literal _ _ (by simpa [literalGate, he, hLit] using hgate)
      · simpa only [hword, haction] using framed c hc

/-- A review/replay pilot may reuse the accepted old all-sites proof without
repeating its evaluator. It still imports the old certificates and therefore
claims NO reduction in checking cost or dependency/source size. To remove the
old control replays, check literalGate directly in replacement batches. -/
theorem literalGate_of_old_sites
    (old : allSites (KSim.checkEdge tm215) [] KSource215.t215 = true) :
    allSites literalGate [] KSource215.t215 = true := by
  apply allSites_mono (KSim.checkEdge tm215) literalGate _ KSource215.t215 [] old
  intro Q e h
  unfold literalGate
  split
  · rfl
  · exact h

#print axioms covered_by_framed_and_literal
#print axioms literalGate_of_old_sites
end SetTheory.BusyBeaver.ZFC.K215ControlCoveragePilot
