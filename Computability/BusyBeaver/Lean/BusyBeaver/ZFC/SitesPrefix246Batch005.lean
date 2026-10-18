import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePrefix246

/-!
Generated closed actual-tree coverage for the exact246 table and checker.
Every cut is a kernel decision about the imported actual decoder subtree.
Every structural join requires both actual children. No external coverage
premise, native evaluation or enlarged proof limits. Grouping changes only
file boundaries, never the cut propositions or the full coverage statement.
Adapted from the maintained permutation252 and prefix250 generators, preserving
Mira-Cult, Jeff Ketchersid and Wade's program and simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesPrefix246
open RegisterPath RMBisim SiteCoverage

/-- Cut 14: 26 leaves, 34 guards. -/
theorem block_14 :
    allSites SitePrefix246.checkSite [false, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false]) = true := by decide +kernel

/-- Cut 15: 26 leaves, 34 guards. -/
theorem block_15 :
    allSites SitePrefix246.checkSite [true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true]) = true := by decide +kernel

/-- Cut 16: 27 leaves, 35 guards. -/
theorem block_16 :
    allSites SitePrefix246.checkSite [true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true]) = true := by decide +kernel

/-- Cut 17: 19 leaves, 25 guards. -/
theorem block_17 :
    allSites SitePrefix246.checkSite [false, false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false]) = true := by decide +kernel


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
