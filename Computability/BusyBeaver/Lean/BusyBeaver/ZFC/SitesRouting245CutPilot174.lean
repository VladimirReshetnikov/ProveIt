import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245

/-!
Exact routed subtree measurement 174: 47 leaves / 61 guards.
Both decrement guards are included by SiteRouting245.checkSite. This closed
check is about the actual imported subtree with its complete reverse prefix.
Fuel 4000 and margin 64 are unchanged. No complete coverage or endpoint is
asserted. The cut is only a measurement candidate until root checks it.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesRouting245CutPilot174
open RegisterPath RMBisim SiteCoverage

theorem checked :
    allSites SiteRouting245.checkSite [true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, true]) = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.SitesRouting245CutPilot174
