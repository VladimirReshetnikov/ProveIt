import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240

/-!
Fresh direct240 subtree measurement: 19 leaves / 25 guards.
Both decrement branches are included by the exact SiteRotation240 checker.
The complete root prefix is retained in reverse accumulator order. Fuel4000,
margin64 and default proof limits are unchanged. This local certificate alone
does not establish whole-tree coverage, runtime calibration or a state bound.
The checked routed-subtree proof pattern retains the original Mira-Cult,
Jeff Ketchersid, Andrew James Wade and ProveIt attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesRotation240PilotDeep
open RegisterPath RMBisim SiteCoverage

theorem checked :
    allSites SiteRotation240.checkSite [false, true, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false]) = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.SitesRotation240PilotDeep
