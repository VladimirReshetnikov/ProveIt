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

/-- Cut 24: 28 leaves, 36 guards. -/
theorem block_24 :
    allSites SitePrefix246.checkSite [true, true, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, true]) = true := by decide +kernel

/-- Cut 25: 2 leaves, 2 guards. -/
theorem block_25 :
    allSites SitePrefix246.checkSite [false, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, false]) = true := by decide +kernel

/-- Cut 26: 45 leaves, 59 guards. -/
theorem block_26 :
    allSites SitePrefix246.checkSite [false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false, false]) = true := by decide +kernel

/-- Cut 27: 7 leaves, 9 guards. -/
theorem block_27 :
    allSites SitePrefix246.checkSite [true, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false, true]) = true := by decide +kernel


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
