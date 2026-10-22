import BusyBeaver.ZFC.KSim

/-! Typed compatibility clients, plus the checker-independent endpoint. -/
namespace LegacySitesAudit
open SetTheory.BusyBeaver.ZFC
open KZip KRuntimeCore RegisterPath KSim

example {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
    {c c' : Configuration} {T : Conf} (hc : Rel p c T) (hs : RegisterPath.step p c = some c') :
    ∃ T', Rel p c' T' ∧ Reach1 M T T' := sim_step B hcov hc hs

-- The old stop lemma does not acquire a BoxLemmas premise.
example {M : TMN} {p : Program} (hcov : Covered M p)
    {c : Configuration} (hs : RegisterPath.step p c = none) : AtHalt p c := sim_stop hcov hs

example {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
    (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf} (hc : Rel p c T)
    (hh : AtHalt p c) : KZip.Halts M T := sim_halt B hcov hNH hc hh

example {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
    (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf} (hc : Rel p c T) :
    RegisterPath.Halts p c ↔ KZip.Halts M T := halts_iff B hcov hNH hc

#print axioms sim_step
#print axioms sim_stop
#print axioms sim_halt
#print axioms halts_iff
end LegacySitesAudit
