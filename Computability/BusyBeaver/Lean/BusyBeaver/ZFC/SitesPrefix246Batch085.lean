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

/-- Cut 229: 26 leaves, 34 guards. -/
theorem block_229 :
    allSites SitePrefix246.checkSite [false, false, false, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, false, false, false]) = true := by decide +kernel

/-- Cut 230: 27 leaves, 35 guards. -/
theorem block_230 :
    allSites SitePrefix246.checkSite [true, false, false, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, false, false, true]) = true := by decide +kernel

/-- Cut 231: 3 leaves, 4 guards. -/
theorem block_231 :
    allSites SitePrefix246.checkSite [true, false, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, false, true]) = true := by decide +kernel

/-- Cut 232: 37 leaves, 50 guards. -/
theorem block_232 :
    allSites SitePrefix246.checkSite [true, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, true]) = true := by decide +kernel


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
