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

/-- Cut 211: 26 leaves, 34 guards. -/
theorem block_211 :
    allSites SitePrefix246.checkSite [true, false, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, false, true]) = true := by decide +kernel

/-- Cut 212: 29 leaves, 37 guards. -/
theorem block_212 :
    allSites SitePrefix246.checkSite [true, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, true]) = true := by decide +kernel

/-- Cut 213: 1 leaves, 1 guards. -/
theorem block_213 :
    allSites SitePrefix246.checkSite [true, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, true]) = true := by decide +kernel

/-- Cut 214: 29 leaves, 37 guards. -/
theorem block_214 :
    allSites SitePrefix246.checkSite [false, false, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false]) = true := by decide +kernel


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
