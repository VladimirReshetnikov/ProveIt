import BusyBeaver.ZFC.KSim

/-! Existing public theorem types, checked without a concrete site evaluation. -/
namespace SetTheory.BusyBeaver.ZFC.KSimCompatibility
open KZip KRuntimeCore KSim RegisterPath

example {M : TMN} (B : BoxLemmas M) {p : Program} (coverage : Covered M p)
    {c c' : Configuration} {T : Conf} (related : Rel p c T)
    (transition : RegisterPath.step p c = some c') :
    ∃ T', Rel p c' T' ∧ Reach1 M T T' := sim_step B coverage related transition

example {M : TMN} {p : Program} (coverage : Covered M p)
    {c : Configuration} (stopped : RegisterPath.step p c = none) : AtHalt p c :=
  sim_stop coverage stopped

example {M : TMN} (B : BoxLemmas M) {p : Program} (coverage : Covered M p)
    (haltRows : ∀ b, M 230 b = none) {c : Configuration} {T : Conf}
    (related : Rel p c T) (stopped : AtHalt p c) : KZip.Halts M T :=
  sim_halt B coverage haltRows related stopped

example {M : TMN} (B : BoxLemmas M) {p : Program} (coverage : Covered M p)
    (haltRows : ∀ b, M 230 b = none) {c : Configuration} {T : Conf}
    (related : Rel p c T) : RegisterPath.Halts p c ↔ KZip.Halts M T :=
  halts_iff B coverage haltRows related

#print axioms PortContract.precompose
#print axioms Covered.toSemantic
#print axioms SemanticCovered.of_leaves
#print axioms Semantic.sim_step
#print axioms Semantic.sim_halt
#print axioms Semantic.halts_iff
#print axioms KSim.halts_iff
end SetTheory.BusyBeaver.ZFC.KSimCompatibility
