import BusyBeaver.ZFC.KSim

/-! Typed compatibility clients, plus the checker-independent endpoint. -/
namespace SemanticSitesAudit
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

-- Neither the symbolic executor nor BoxLemmas is a premise of this theorem.
example {M : TMN} {p : Program} (hcov : SemanticCovered M p)
    (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf} (hc : Rel p c T) :
    RegisterPath.Halts p c ↔ KZip.Halts M T := semantic_halts_iff hcov hNH hc

-- Mixed migration: selected primitives use new contracts; every other leaf
-- keeps the old Boolean check. Selection does not silently discharge a contract.
example {M : TMN} (B : BoxLemmas M) (p : Program) (t : RMBisim.Tree)
    (ht : RMBisim.ptree p = t) (selected : List Bool → Edge → Bool)
    (shared : ∀ Q e, selected Q e = true → SiteSpec M Q e)
    (hs : SiteCoverage.allSites
      (fun Q e => if selected Q e then true else checkEdge M Q e) [] t = true) :
    SemanticCovered M p := by
  apply semantic_covered_of_allSites M p t ht _ hs
  intro Q e h
  by_cases hc : selected Q e = true
  · exact shared Q e hc
  · exact checkEdge_sound B (by simpa [hc] using h)

-- A zero-length decoder prefix is permitted; the tail must provide positivity.
example {M : TMN} {port : SConf} {Q : List Bool} {e : Edge}
    (tail : SiteContract M port Q e) : SiteContract M port Q e :=
  SiteContract.prepend (fun _ _ => Reach.refl M _) tail

#print axioms SiteContract.prepend
#print axioms checkEdge_sound
#print axioms Covered.to_semantic
#print axioms semantic_covered_of_allSites
#print axioms semantic_sim_step
#print axioms semantic_sim_stop
#print axioms semantic_sim_halt
#print axioms semantic_halts_iff
#print axioms halts_iff
end SemanticSitesAudit
