import BusyBeaver.ZFC.KSimPrefix
import BusyBeaver.ZFC.KDecoderPrefix215

/-!
An exact connection from the maintained K215 decoder to semantic site coverage.
The existing prefix theorem chooses a fixed port before quantifying over gaps
and registers. Suffix execution begins at that port and preserves every original
branch target. `CheckedLeafSuffixes` is an explicit remaining finite-certificate
obligation: this file does not assert that all concrete suffix checks pass.
-/
namespace SetTheory.BusyBeaver.ZFC.KDecoderSuffix215

open KZip KRuntimeCore KSim KSimPrefix KDecoderPrefix215
open RegisterPath SiteCoverage DecoderSourceBinding DecoderPaths K215Decoder

/-- All exact source leaves have positive checked primitive suffixes. The
accepted full role path, rather than state/read alone, determines eligibility. -/
def CheckedLeafSuffixes : Prop :=
  ∀ {word : List Bool} {e : Edge}, LeafAt KSource215.t215 word e →
    ∀ {pre : List Bool} {bit : Bool} {q op arg : Nat},
      word = pre ++ [bit] → e = primitive op arg →
      RoutedEntry formal sourceNodes roles 0 word q bit op arg →
      checkEdgeFrom KTableCore.tm215 word (leafPort pre bit q) e = true

/-- A shared decoder theorem and a suffix certificate provide the original
all-natural semantic contract at one literal leaf. -/
theorem leaf_spec (B : BoxLemmas KTableCore.tm215) (suffixes : CheckedLeafSuffixes)
    {word : List Bool} {e : Edge} (leaf : LeafAt KSource215.t215 word e) :
    KSim.EdgeSpec KTableCore.tm215 word e := by
  obtain ⟨pre, bit, q, op, arg, hsplit, he, hr, hp⟩ := leaf_prefix leaf
  have hpref : PrefixSpec KTableCore.tm215 word (leafPort pre bit q) := by
    intro n vs
    obtain ⟨steps, _, _, hs⟩ := hp n vs
    exact ⟨steps, hs⟩
  exact edgeSpec_of_prefix_checked B hpref (suffixes leaf hsplit he hr)

/-- Total finite source shape is a separate, non-runtime obligation. -/
theorem semantic_covered (B : BoxLemmas KTableCore.tm215)
    (total : allSites (fun _ _ => true) [] KSource215.t215 = true)
    (suffixes : CheckedLeafSuffixes) : SemanticCovered KTableCore.tm215 KSource215.p215 :=
  semanticCovered_of_leaf_specs KSource215.t215_eq total (leaf_spec B suffixes)

/-- Conditional binary/source halting equivalence with no new simulation
induction and no Boolean whole-site premise. -/
theorem source_halts_iff (B : BoxLemmas KTableCore.tm215)
    (total : allSites (fun _ _ => true) [] KSource215.t215 = true)
    (suffixes : CheckedLeafSuffixes) (terminal : ∀ b, KTableCore.tm215 230 b = none)
    {c : Configuration} {T : Conf} (hc : KSim.Rel KSource215.p215 c T) :
    RegisterPath.Halts KSource215.p215 c ↔ KZip.Halts KTableCore.tm215 T :=
  KSim.Semantic.halts_iff (semantic_covered B total suffixes) terminal hc

#print axioms leaf_spec
#print axioms semantic_covered
#print axioms source_halts_iff

end SetTheory.BusyBeaver.ZFC.KDecoderSuffix215
