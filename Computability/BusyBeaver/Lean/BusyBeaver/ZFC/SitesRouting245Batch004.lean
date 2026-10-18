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

/-- Cut 14: 26 leaves / 34 guards. -/
theorem block_14 :
    allSites SiteRouting245.checkSite [false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false]) = true := by decide +kernel

/-- Cut 15: 26 leaves / 34 guards. -/
theorem block_15 :
    allSites SiteRouting245.checkSite [true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true]) = true := by decide +kernel

/-- Cut 16: 27 leaves / 35 guards. -/
theorem block_16 :
    allSites SiteRouting245.checkSite [true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true]) = true := by decide +kernel


end SetTheory.BusyBeaver.ZFC.SitesRouting245
