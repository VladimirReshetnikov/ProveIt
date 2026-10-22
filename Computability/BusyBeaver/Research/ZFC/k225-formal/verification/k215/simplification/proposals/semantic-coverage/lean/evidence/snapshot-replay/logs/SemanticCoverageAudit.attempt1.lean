import BusyBeaver.ZFC.KSim

namespace SetTheory.BusyBeaver.ZFC.SemanticCoverageAudit
open KZip KRuntimeCore RegisterPath KSim

-- These elaborated types are the original public interfaces.
example {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
    {c c' : Configuration} {T : Conf} (hc : Rel p c T) (hs : step p c = some c') :
    ∃ T', Rel p c' T' ∧ Reach1 M T T' := sim_step B hcov hc hs

example {M : TMN} {p : Program} (hcov : Covered M p)
    {c : Configuration} (hs : step p c = none) : AtHalt p c := sim_stop hcov hs

example {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
    (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf}
    (hc : Rel p c T) (hh : AtHalt p c) : Halts M T := sim_halt B hcov hNH hc hh

example {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
    (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf} (hc : Rel p c T) :
    RegisterPath.Halts p c ↔ KZip.Halts M T := halts_iff B hcov hNH hc

-- The new simulator needs semantic coverage; it no longer needs BoxLemmas.
example {M : TMN} {p : Program} (hcov : SemanticCovered M p)
    (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf} (hc : Rel p c T) :
    RegisterPath.Halts p c ↔ KZip.Halts M T := Semantic.halts_iff hcov hNH hc

-- A family of direct proofs can be mixed with unchanged checker leaves.
example {M : TMN} (B : BoxLemmas M) (p : Program) (t : RMBisim.Tree)
    (ht : RMBisim.ptree p = t) (shared : List Bool → Edge → Bool)
    (sound : ∀ Q e, shared Q e = true → EdgeContract M Q e)
    (hs : SiteCoverage.allSites (fun Q e => shared Q e || checkEdge M Q e) [] t = true) :
    SemanticCovered M p := semanticCovered_of_mixedSites B p t ht shared sound hs

#print axioms checkEdge_contract
#print axioms Covered.semantic
#print axioms semanticCovered_of_allSites
#print axioms semanticCovered_of_mixedSites
#print axioms Semantic.sim_step
#print axioms Semantic.sim_stop
#print axioms Semantic.sim_halt
#print axioms Semantic.halts_iff
#print axioms sim_step
#print axioms sim_stop
#print axioms sim_halt
#print axioms halts_iff

end SetTheory.BusyBeaver.ZFC.SemanticCoverageAudit
