import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245

/-!
Closed coverage of the exact routed245 instruction tree. Every new cut is a
kernel decision about the imported actual subtree with its complete reverse
prefix; every composition requires both actual children. The three measured
pilot modules are reused directly. No external coverage premise, native proof
evaluation, or enlarged proof limits. Grouping changes only file boundaries.
Adapted from the maintained permutation252/prefix246 coverage generators,
preserving Mira-Cult, Jeff Ketchersid and Wade's program/simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesRouting245
open RegisterPath RMBisim SiteCoverage

/-- Cut 5: 1 leaves / 2 guards. -/
theorem block_5 :
    allSites SiteRouting245.checkSite [false, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, false]) = true := by decide +kernel

/-- Cut 6: 19 leaves / 25 guards. -/
theorem block_6 :
    allSites SiteRouting245.checkSite [false, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false]) = true := by decide +kernel

/-- Cut 7: 33 leaves / 43 guards. -/
theorem block_7 :
    allSites SiteRouting245.checkSite [true, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true]) = true := by decide +kernel

/-- Cut 8: 29 leaves / 37 guards. -/
theorem block_8 :
    allSites SiteRouting245.checkSite [true, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true]) = true := by decide +kernel


end SetTheory.BusyBeaver.ZFC.SitesRouting245
