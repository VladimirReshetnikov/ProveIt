module
/- Exact211: fresh physical interpretation of the unchanged original coded source. -/
public import M6PA.Model.EndpointPaddedNatTape
public import M6.Startup
public import M6.Conjugacy
@[expose] public section
namespace M6.Arithmetic.PA.PhysicalAdequacy
open M6.Zip
/-- Auxiliary arithmetic tags do not enlarge the physical control set. The
exact 209-control partial table and the dense-stack interpreter have identical
blank-halting behavior; the six unused tags are excluded by the proved invariant. -/
theorem blank_halts_iff :
    M6.Zip.Halts M6.Table.machine (M6.Conjugacy.mapConf M6.Startup.blank) ↔ NatTape.Halts NatTape.blank := by
  have hl : PaddedBridge.Live (M6.Conjugacy.mapConf M6.Startup.blank).q :=
    Or.inr M6.Arithmetic.StateBound.start_working
  have hp := PaddedBridge.halts_iff (M6.Conjugacy.mapConf M6.Startup.blank) hl
  have hn := PaddedNatTape.halts_iff (M6.Conjugacy.mapConf M6.Startup.blank)
  change M6.Zip.Halts PaddedBridge.machine (M6.Conjugacy.mapConf M6.Startup.blank) ↔ NatTape.Halts NatTape.blank at hn
  exact hp.symm.trans hn
#print axioms blank_halts_iff
end M6.Arithmetic.PA.PhysicalAdequacy
