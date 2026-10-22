import BusyBeaver.ZFC.KSim

open SetTheory.BusyBeaver.ZFC
open KZip KRuntimeCore RegisterPath KSim

section OriginalAPI
variable {M : TMN} (B : BoxLemmas M) {p : Program} (covered : Covered M p)

example {Q : List Bool} (h : runHalt M Q = true) (hNH : ∀ b, M 230 b = none)
    (n : Nat) {vs : List Nat} (hv : 10 ≤ vs.length) :
    KZip.Halts M (conc n vs (start Q)) :=
  runHalt_sound B hNH h n hv

example {c c' : Configuration} {T : Conf} (hc : Rel p c T)
    (hs : RegisterPath.step p c = some c') :
    ∃ T', Rel p c' T' ∧ Reach1 M T T' := sim_step B covered hc hs

example {c : Configuration} (hs : RegisterPath.step p c = none) :
    AtHalt p c := sim_stop covered hs

example (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf}
    (hc : Rel p c T) (hh : AtHalt p c) : KZip.Halts M T :=
  sim_halt B covered hNH hc hh

example (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf}
    (hc : Rel p c T) : RegisterPath.Halts p c ↔ KZip.Halts M T :=
  halts_iff B covered hNH hc
end OriginalAPI

-- Semantic clients do not supply BoxLemmas, an executor or its fuel.
example {M : TMN} {p : Program} (covered : SemanticCovered M p)
    (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf}
    (hc : Rel p c T) : RegisterPath.Halts p c ↔ KZip.Halts M T :=
  halts_iff_semantic covered hNH hc

#print axioms runHalt_reaches
#print axioms edgeContract_of_check
#print axioms semanticCovered_of_covered
#print axioms semanticCovered_of_allLeaves
#print axioms sim_step_semantic
#print axioms sim_stop_semantic
#print axioms sim_halt_semantic
#print axioms halts_iff_semantic
#print axioms halts_iff
