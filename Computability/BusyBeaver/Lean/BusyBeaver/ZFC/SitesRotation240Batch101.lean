import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240

/-!
Closed coverage of the exact direct240 instruction tree. Every new cut is a
kernel decision about the imported actual subtree with its complete reverse
prefix; every composition requires both actual children. The four measured
pilot modules are reused directly. No external coverage premise, native proof
evaluation, or enlarged proof limits. Grouping changes only file boundaries.
Adapted from the maintained permutation252/prefix246 coverage generators,
preserving Mira-Cult, Jeff Ketchersid and Wade's program/simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesRotation240
open RegisterPath RMBisim SiteCoverage

/-- Cut 102: 11 leaves / 15 guards. -/
theorem block_102 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true, true, false, false]) = true := by decide +kernel


end SetTheory.BusyBeaver.ZFC.SitesRotation240
